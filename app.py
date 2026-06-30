import os
import re
import hmac
import hashlib
import sqlite3
import secrets
import razorpay
from collections import defaultdict
from time import time
from flask import Flask, render_template, request, jsonify, redirect, url_for, session
from dotenv import load_dotenv

load_dotenv()

app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", "fallback-secret-key")

RAZORPAY_KEY_ID     = os.getenv("RAZORPAY_KEY_ID", "").strip().strip('"').strip("'")
RAZORPAY_KEY_SECRET = os.getenv("RAZORPAY_KEY_SECRET", "").strip().strip('"').strip("'")
EVENT_FEE_PAISE     = 19900  # Rs.199

razorpay_client = razorpay.Client(auth=(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET))

if RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET:
    print(f"[Razorpay] Key loaded: {RAZORPAY_KEY_ID[:12]}...")
else:
    print("[Razorpay] WARNING: keys missing — running in DEMO MODE")

DB_PATH = "registrations.db"

# How long an unpaid order is allowed to sit before it's purged
PENDING_EXPIRY_MINUTES = 30

# ── Allowed values (server-side whitelist) ────────────────────────────────────

ALLOWED_BRANCHES = {
    "Computer Engineering",
    "Computer Science & Engineering",
    "Electronics & CS Engineering",
    "Mechanical Engineering",
}

ALLOWED_YEARS = {
    "First Year",
    "Second Year",
    "Third Year",
    "Fourth Year",
}

# Only this college domain may register
ALLOWED_EMAIL_DOMAIN = "crce.edu.in"

# ── Rate limiting (per IP) ────────────────────────────────────────────────────

_rate_store = defaultdict(list)
RATE_LIMIT  = 5
RATE_WINDOW = 300  # 5 minutes

def is_rate_limited(ip):
    now = time()
    _rate_store[ip] = [t for t in _rate_store[ip] if now - t < RATE_WINDOW]
    if len(_rate_store[ip]) >= RATE_LIMIT:
        return True
    _rate_store[ip].append(now)
    return False

def get_ip():
    return request.headers.get("X-Forwarded-For", request.remote_addr).split(",")[0].strip()

# ── Database ──────────────────────────────────────────────────────────────────
#
# Design: user data is NEVER written to the permanent `registrations` table
# on form submission. It is held in a `pending_orders` table, keyed by the
# Razorpay order_id, until payment is independently verified. Only the
# verified `/verify-payment` success path moves the data into `registrations`.
# A direct/bypassed POST to /create-order (or a faked "payment done" message
# to the backend) can therefore never produce a row in `registrations` —
# at worst it creates a row in `pending_orders`, which expires automatically
# and is never shown anywhere as a registration.

def get_db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    with get_db() as conn:
        # Permanent table — only ever populated post-payment-confirmation
        conn.execute("""
            CREATE TABLE IF NOT EXISTS registrations (
                id                INTEGER PRIMARY KEY AUTOINCREMENT,
                registration_id   TEXT    UNIQUE NOT NULL,
                name              TEXT    NOT NULL,
                email             TEXT    UNIQUE NOT NULL,
                phone             TEXT    UNIQUE NOT NULL,
                roll_number       TEXT    UNIQUE NOT NULL,
                branch            TEXT    NOT NULL,
                year              TEXT    NOT NULL,
                razorpay_order_id TEXT    UNIQUE NOT NULL,
                payment_id        TEXT    UNIQUE NOT NULL,
                created_at        TEXT    DEFAULT (datetime('now')),
                ip_address        TEXT
            )
        """)

        # Transient holding table — deleted on success, expired on timeout
        conn.execute("""
            CREATE TABLE IF NOT EXISTS pending_orders (
                razorpay_order_id TEXT PRIMARY KEY,
                name              TEXT NOT NULL,
                email             TEXT NOT NULL,
                phone             TEXT NOT NULL,
                roll_number       TEXT NOT NULL,
                branch            TEXT NOT NULL,
                year              TEXT NOT NULL,
                ip_address        TEXT,
                created_at        TEXT DEFAULT (datetime('now'))
            )
        """)

        conn.execute("""
            CREATE TABLE IF NOT EXISTS id_counter (
                name  TEXT PRIMARY KEY,
                value INTEGER NOT NULL DEFAULT 0
            )
        """)

        conn.commit()
        print("[DB] Ready —", DB_PATH)

def purge_expired_pending(conn):
    """Remove abandoned/unpaid orders older than PENDING_EXPIRY_MINUTES."""
    conn.execute(
        "DELETE FROM pending_orders WHERE created_at < datetime('now', ?)",
        (f"-{PENDING_EXPIRY_MINUTES} minutes",)
    )

def generate_registration_id(conn):
    """
    Atomic, collision-proof ID generator.
    MUST be called with the SAME connection/transaction that performs the
    subsequent INSERT into `registrations`, committed together. SQLite takes
    a write lock on this UPDATE, so two concurrent requests can never read or
    claim the same sequence value (unlike a COUNT(*)-based approach).
    """
    conn.execute(
        "INSERT INTO id_counter (name, value) VALUES ('registration', 0) "
        "ON CONFLICT(name) DO NOTHING"
    )
    conn.execute(
        "UPDATE id_counter SET value = value + 1 WHERE name = 'registration'"
    )
    row = conn.execute(
        "SELECT value FROM id_counter WHERE name = 'registration'"
    ).fetchone()
    seq = row["value"]
    return f"FC2026-{seq:04d}"

# ── Server-side validators ────────────────────────────────────────────────────

def validate_name(v):
    v = (v or "").strip()
    if len(v) < 2 or len(v) > 100:
        return None, "Name must be 2–100 characters"
    if not re.match(r"^[A-Za-z\s.\-']+$", v):
        return None, "Name contains invalid characters"
    return v, None

def validate_email(v):
    """
    Must be a syntactically valid email AND end in @crce.edu.in.
    This is the authoritative check — the frontend check is UX only and
    can be bypassed, so nothing here trusts the client.
    """
    v = (v or "").strip().lower()
    if len(v) > 254:
        return None, "Email too long"
    if not re.match(r"^[^\s@]+@[^\s@]+\.[^\s@]{2,}$", v):
        return None, "Invalid email address"
    if not v.endswith("@" + ALLOWED_EMAIL_DOMAIN):
        return None, f"Only college email addresses (@{ALLOWED_EMAIL_DOMAIN}) are allowed"
    return v, None

def validate_phone(v):
    v = (v or "").strip()
    if not re.match(r"^\d{10}$", v):
        return None, "Phone must be exactly 10 digits"
    return v, None

def validate_roll_number(v):
    v = (v or "").strip()
    if not re.match(r"^\d{5}$", v):
        return None, "Roll number must be exactly 5 digits"
    return v, None

def validate_branch(v):
    v = (v or "").strip()
    if v not in ALLOWED_BRANCHES:
        return None, "Invalid branch — must select from the form"
    return v, None

def validate_year(v):
    v = (v or "").strip()
    if v not in ALLOWED_YEARS:
        return None, "Invalid year — must select from the form"
    return v, None

# ── CSRF helpers ──────────────────────────────────────────────────────────────

def generate_csrf_token():
    if "csrf_token" not in session:
        session["csrf_token"] = secrets.token_hex(32)
    return session["csrf_token"]

def verify_csrf_token(token_from_request):
    expected = session.get("csrf_token", "")
    if not expected or not token_from_request:
        return False
    return hmac.compare_digest(expected, token_from_request)

# ── Helpers ───────────────────────────────────────────────────────────────────

def is_demo_mode():
    return not RAZORPAY_KEY_ID or not RAZORPAY_KEY_SECRET

def enforce_json_content_type():
    if not request.is_json:
        return jsonify({"error": "Content-Type must be application/json"}), 415
    return None

def enforce_max_payload(max_bytes=2048):
    length = request.content_length
    if length and length > max_bytes:
        return jsonify({"error": "Request payload too large"}), 413
    return None

# ── Routes ────────────────────────────────────────────────────────────────────

@app.route("/")
def index():
    csrf_token = generate_csrf_token()
    return render_template(
        "index.html",
        razorpay_key_id=RAZORPAY_KEY_ID,
        demo_mode=is_demo_mode(),
        csrf_token=csrf_token,
    )


@app.route("/create-order", methods=["POST"])
def create_order():
    """
    Payment initiation step only.
    No row is ever written to `registrations` here — only to the transient
    `pending_orders` table, keyed by the Razorpay order_id. Even a fully
    bypassed/scripted POST to this endpoint (frontend disabled) can never
    create a permanent registration; it can only create a row that expires
    automatically and is never treated as a real registration anywhere.
    """
    try:
        ip = get_ip()

        err = enforce_max_payload()
        if err: return err

        err = enforce_json_content_type()
        if err: return err

        data = request.get_json(silent=True)
        if not data:
            return jsonify({"error": "Empty or malformed JSON body"}), 400

        # ── CSRF token must match what the server issued ──────────────────
        csrf = data.get("csrf_token", "")
        if not verify_csrf_token(csrf):
            return jsonify({"error": "Invalid or missing CSRF token — request must originate from our form"}), 403

        # ── Rate limit per IP ──────────────────────────────────────────────
        if is_rate_limited(ip):
            return jsonify({"error": "Too many attempts. Please wait 5 minutes."}), 429

        # ── Validate every field server-side (never trust the client) ─────
        errors = {}

        name,        err = validate_name(data.get("name"))
        if err: errors["name"] = err

        email,       err = validate_email(data.get("email"))
        if err: errors["email"] = err

        phone,       err = validate_phone(data.get("phone"))
        if err: errors["phone"] = err

        roll_number, err = validate_roll_number(data.get("roll_number"))
        if err: errors["roll_number"] = err

        branch,      err = validate_branch(data.get("branch"))
        if err: errors["branch"] = err

        year,        err = validate_year(data.get("year"))
        if err: errors["year"] = err

        if errors:
            return jsonify({"error": "Validation failed", "fields": errors}), 422

        with get_db() as conn:
            # Sweep out anything abandoned past the expiry window first
            purge_expired_pending(conn)
            conn.commit()

            # ── Duplicate check against CONFIRMED registrations only ──────
            dup_email = conn.execute(
                "SELECT 1 FROM registrations WHERE email=?", (email,)
            ).fetchone()
            dup_phone = conn.execute(
                "SELECT 1 FROM registrations WHERE phone=?", (phone,)
            ).fetchone()
            dup_roll = conn.execute(
                "SELECT 1 FROM registrations WHERE roll_number=?", (roll_number,)
            ).fetchone()

        if dup_email:
            return jsonify({"error": "This email is already registered with a confirmed payment."}), 409
        if dup_phone:
            return jsonify({"error": "This phone number is already registered with a confirmed payment."}), 409
        if dup_roll:
            return jsonify({"error": "This roll number is already registered with a confirmed payment."}), 409

        # ── Create Razorpay order FIRST (we need the order_id as the key) ─
        order = razorpay_client.order.create({
            "amount":   EVENT_FEE_PAISE,
            "currency": "INR",
            "notes":    {"name": name, "email": email, "branch": branch, "year": year, "roll_number": roll_number}
        })

        # ── Stash submitted data in the transient pending_orders table ────
        # This is the ONLY write that happens at this stage — nothing is
        # written to `registrations` until payment is confirmed.
        with get_db() as conn:
            conn.execute(
                """INSERT INTO pending_orders
                   (razorpay_order_id, name, email, phone, roll_number, branch, year, ip_address)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                (order["id"], name, email, phone, roll_number, branch, year, ip)
            )
            conn.commit()

        # ── Rotate CSRF token after successful order creation ─────────────
        session["csrf_token"] = secrets.token_hex(32)

        return jsonify({
            "order_id": order["id"],
            "amount":   EVENT_FEE_PAISE,
            "currency": "INR",
            "name":     name,
            "email":    email,
            "phone":    phone,
        })

    except razorpay.errors.BadRequestError as e:
        print(f"[create-order RAZORPAY ERROR] {e}")
        return jsonify({"error": f"Payment gateway rejected the request: {str(e)}"}), 502
    except sqlite3.IntegrityError as e:
        print(f"[create-order DB INTEGRITY ERROR] {e}")
        return jsonify({"error": "An order for these details is already in progress. Please wait a moment and retry."}), 409
    except Exception as e:
        import traceback
        traceback.print_exc()
        print(f"[create-order ERROR] {type(e).__name__}: {e}")
        return jsonify({"error": "Something went wrong. Please try again.", "debug": str(e) if app.debug else None}), 500


@app.route("/verify-payment", methods=["POST"])
def verify_payment():
    """
    Payment confirmation step — the ONLY trigger for writing to `registrations`.

    Sequence:
      1. Independently verify the payment is real (signature + Razorpay API lookup).
      2. Only once verified, pull the held data from `pending_orders` using the
         verified order_id as the lookup key.
      3. Atomically insert into `registrations` and delete from `pending_orders`
         in a single transaction (so a row exists in exactly one place,
         never both, never neither).

    A client cannot skip straight here and "claim" success: the order_id must
    match one we created, the signature must be a real HMAC computed with our
    server-side secret, and the payment is re-fetched directly from Razorpay's
    own API to confirm status/amount/order — none of that is takeable from
    user-supplied input alone.
    """
    try:
        err = enforce_max_payload()
        if err: return err

        err = enforce_json_content_type()
        if err: return err

        data = request.get_json(silent=True)
        if not data:
            return jsonify({"error": "Empty or malformed JSON body"}), 400

        razorpay_order_id   = str(data.get("razorpay_order_id", "")).strip()
        razorpay_payment_id = str(data.get("razorpay_payment_id", "")).strip()
        razorpay_signature  = str(data.get("razorpay_signature", "")).strip()

        if not all([razorpay_order_id, razorpay_payment_id, razorpay_signature]):
            return jsonify({"error": "Missing required payment fields"}), 400

        # ── Pending order must exist and not have expired ─────────────────
        with get_db() as conn:
            purge_expired_pending(conn)
            conn.commit()
            pending = conn.execute(
                "SELECT * FROM pending_orders WHERE razorpay_order_id=?",
                (razorpay_order_id,)
            ).fetchone()

        if not pending:
            return jsonify({"error": "No matching pending order found (it may have expired). Please start again."}), 404

        # Already-confirmed check (idempotency: re-submits of the same callback)
        with get_db() as conn:
            already = conn.execute(
                "SELECT registration_id FROM registrations WHERE razorpay_order_id=?",
                (razorpay_order_id,)
            ).fetchone()
        if already:
            return jsonify({"redirect": url_for("success", registration_id=already["registration_id"])})

        # ── HMAC signature — cryptographic proof from Razorpay ────────────
        body         = f"{razorpay_order_id}|{razorpay_payment_id}"
        expected_sig = hmac.new(
            RAZORPAY_KEY_SECRET.encode("utf-8"),
            body.encode("utf-8"),
            hashlib.sha256
        ).hexdigest()

        if not hmac.compare_digest(expected_sig, razorpay_signature):
            return jsonify({"error": "Payment signature invalid"}), 400

        # ── Verify directly with Razorpay API — cannot be faked ───────────
        try:
            payment = razorpay_client.payment.fetch(razorpay_payment_id)
        except Exception:
            return jsonify({"error": "Could not verify payment with Razorpay"}), 502

        if payment.get("status") not in ("captured", "authorized"):
            return jsonify({"error": f"Payment not confirmed (status: {payment.get('status')})"}), 400

        if payment.get("amount") != EVENT_FEE_PAISE:
            return jsonify({"error": "Payment amount mismatch — possible tampering"}), 400

        if payment.get("order_id") != razorpay_order_id:
            return jsonify({"error": "Payment does not belong to this order"}), 400

        # ── All checks passed — THIS is the trigger for database entry ────
        with get_db() as conn:
            try:
                reg_id = generate_registration_id(conn)
                conn.execute(
                    """INSERT INTO registrations
                       (registration_id, name, email, phone, roll_number, branch, year,
                        razorpay_order_id, payment_id, ip_address)
                       VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                    (reg_id, pending["name"], pending["email"], pending["phone"],
                     pending["roll_number"], pending["branch"], pending["year"],
                     razorpay_order_id, razorpay_payment_id, pending["ip_address"])
                )
                conn.execute(
                    "DELETE FROM pending_orders WHERE razorpay_order_id=?",
                    (razorpay_order_id,)
                )
                conn.commit()
            except sqlite3.IntegrityError:
                conn.rollback()
                return jsonify({"error": "These details were already used in a confirmed registration."}), 409

        return jsonify({"redirect": url_for("success", registration_id=reg_id)})

    except Exception as e:
        print(f"[verify-payment ERROR] {e}")
        return jsonify({"error": "Verification failed. Please contact support."}), 500


@app.route("/success/<registration_id>")
def success(registration_id):
    if not re.match(r"^FC2026-\d{4}$", registration_id):
        return redirect(url_for("index"))

    with get_db() as conn:
        row = conn.execute(
            "SELECT * FROM registrations WHERE registration_id=?",
            (registration_id,)
        ).fetchone()

    if not row:
        return redirect(url_for("index"))

    return render_template("success.html", reg=row)


# ── Boot ──────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    init_db()
    app.run(debug=True)