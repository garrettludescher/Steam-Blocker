"""
steam_gate.py

Blocks Steam from running until you've reviewed a target number of Anki
cards today. Runs as a system tray icon that stays active at all times -
closing the details window just hides it, it does NOT quit the program.

Two ways to get today's review count:
  1. Local read (always available): copies your Anki Desktop collection
     file and counts today's reviews. Works with Anki closed, but only
     reflects reviews done on THIS PC.
  2. AnkiWeb sync (optional): logs into your AnkiWeb account and syncs a
     SEPARATE, dedicated collection copy that this app owns - it never
     touches your real Anki Desktop profile. This picks up reviews done
     on other devices (e.g. your phone) too. Your AnkiWeb password is
     stored in the Windows Credential Manager via the `keyring` package,
     never in a plain text file.

Each check uses whichever number is higher (local vs synced), since
that's always the more complete picture. AnkiWeb sync only happens
every couple of minutes in the background (not on every 5-second check)
to avoid hammering AnkiWeb's servers - Steam-blocking itself still
responds within 5 seconds using whatever the latest known count is.

Once you've hit today's target AND actually open Steam, the app closes
itself entirely (tray icon and all) so it's not sitting in the
background using CPU while you game. Toggle this off in Settings if
you'd rather it keep running quietly.

Requires:
    pip install psutil pystray pillow
Optional, only needed for AnkiWeb sync:
    pip install anki keyring

IMPORTANT: run this with pythonw.exe, not python.exe, or rename it to
steam_gate.pyw and double-click it - see the bottom of this file.
"""

import ctypes
import json
import os
import shutil
import sqlite3
import sys
import tempfile
import threading
import time
import tkinter as tk
from tkinter import ttk
from datetime import datetime, timedelta

import psutil
import pystray
from PIL import Image, ImageDraw, ImageTk

# ---------------- CONFIG ----------------
DEFAULT_TARGET_CARDS = 20
DEFAULT_AUTO_QUIT = True
CHECK_INTERVAL_MS = 5000         # local process/UI check - fast, no network
SYNC_INTERVAL_SECONDS = 120      # minimum gap between AnkiWeb syncs
STEAM_PROCESS_NAMES = {"steam.exe"}

# Leave as None to auto-detect your local Anki Desktop profile under
# %APPDATA%\Anki2\<profile>\collection.anki2. Set explicitly if you have
# multiple profiles and auto-detect picks the wrong one.
COLLECTION_PATH = None

CONFIG_DIR = os.path.join(os.environ.get("APPDATA", tempfile.gettempdir()), "SteamGate")
CONFIG_PATH = os.path.join(CONFIG_DIR, "config.json")
SYNC_COLLECTION_PATH = os.path.join(CONFIG_DIR, "sync_collection.anki2")

KEYRING_SERVICE_PASSWORD = "SteamGate"
KEYRING_SERVICE_AUTH = "SteamGateSyncAuth"

PROC_GONE_ERRORS = (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess)

# ---- Dark / neon HUD palette ----
BG = "#05060a"
PANEL = "#0d0f18"
TITLEBAR = "#0a0c14"
BORDER_DIM = "#1c2132"
TEXT_PRIMARY = "#eaf6ff"
TEXT_SECONDARY = "#6d7891"
ACCENT_CYAN = "#00e5ff"
ACCENT_GREEN = "#39ff9d"
ACCENT_RED = "#ff3b5c"
ACCENT_AMBER = "#ffb84d"
FONT_FAMILY = "Consolas"
# -----------------------------------------


def lerp_color(c1, c2, t):
    c1 = c1.lstrip("#")
    c2 = c2.lstrip("#")
    r1, g1, b1 = int(c1[0:2], 16), int(c1[2:4], 16), int(c1[4:6], 16)
    r2, g2, b2 = int(c2[0:2], 16), int(c2[2:4], 16), int(c2[4:6], 16)
    t = max(0.0, min(1.0, t))
    r = round(r1 + (r2 - r1) * t)
    g = round(g1 + (g2 - g1) * t)
    b = round(b1 + (b2 - b1) * t)
    return f"#{r:02x}{g:02x}{b:02x}"


def spaced(text):
    return " ".join(list(text))


# ---------------- Config persistence ----------------

def load_config():
    try:
        with open(CONFIG_PATH, "r") as f:
            return json.load(f)
    except Exception:
        return {}


def save_config(partial):
    os.makedirs(CONFIG_DIR, exist_ok=True)
    cfg = load_config()
    cfg.update(partial)
    with open(CONFIG_PATH, "w") as f:
        json.dump(cfg, f)


def load_target():
    cfg = load_config()
    try:
        t = int(cfg.get("target_cards", DEFAULT_TARGET_CARDS))
        return t if t > 0 else DEFAULT_TARGET_CARDS
    except (TypeError, ValueError):
        return DEFAULT_TARGET_CARDS


def save_target(t):
    save_config({"target_cards": t})


# Once a target is committed it locks for this many days - the user picks a
# daily goal and then has to live with it for a month, no changing it when
# a hard day makes them want to lower the bar.
TARGET_LOCK_DAYS = 30


def load_target_locked_until():
    """Epoch seconds until which the target is locked, or 0 if never set."""
    cfg = load_config()
    try:
        return float(cfg.get("target_locked_until", 0) or 0)
    except (TypeError, ValueError):
        return 0.0


def save_target_locked_until(ts):
    save_config({"target_locked_until": ts})


def target_is_locked():
    return time.time() < load_target_locked_until()


def load_auto_quit():
    cfg = load_config()
    return bool(cfg.get("auto_quit_on_unlock", DEFAULT_AUTO_QUIT))


def save_auto_quit(value):
    save_config({"auto_quit_on_unlock": bool(value)})


def load_sync_enabled():
    return bool(load_config().get("ankiweb_sync_enabled", False))


def save_sync_enabled(value):
    save_config({"ankiweb_sync_enabled": bool(value)})


def load_ankiweb_username():
    return load_config().get("ankiweb_username", "") or ""


def save_ankiweb_username(username):
    save_config({"ankiweb_username": username})


# ---------------- Credential storage (Windows Credential Manager via keyring) ----------------

def _get_keyring():
    try:
        import keyring
        return keyring
    except ImportError as e:
        raise RuntimeError("AnkiWeb sync needs the 'keyring' package - run: pip install keyring") from e


def save_ankiweb_password(username, password):
    kr = _get_keyring()
    kr.set_password(KEYRING_SERVICE_PASSWORD, username, password)


def get_ankiweb_password(username):
    if not username:
        return None
    kr = _get_keyring()
    try:
        return kr.get_password(KEYRING_SERVICE_PASSWORD, username)
    except Exception:
        return None


def safe_get_ankiweb_password(username):
    """Like get_ankiweb_password, but never raises - returns None (and the
    error string) if the optional 'keyring' package isn't installed, so
    callers on the UI/check loop can't be crashed by a missing dependency."""
    try:
        return get_ankiweb_password(username), None
    except RuntimeError as e:
        return None, str(e)


def save_sync_auth(username, hkey, endpoint):
    kr = _get_keyring()
    kr.set_password(KEYRING_SERVICE_AUTH, username, json.dumps({"hkey": hkey, "endpoint": endpoint}))


def load_sync_auth(username):
    if not username:
        return None, None
    kr = _get_keyring()
    try:
        raw = kr.get_password(KEYRING_SERVICE_AUTH, username)
    except Exception:
        raw = None
    if not raw:
        return None, None
    try:
        data = json.loads(raw)
        return data.get("hkey"), data.get("endpoint")
    except Exception:
        return None, None


def forget_ankiweb_credentials(username):
    if not username:
        return
    kr = _get_keyring()
    for service in (KEYRING_SERVICE_PASSWORD, KEYRING_SERVICE_AUTH):
        try:
            kr.delete_password(service, username)
        except Exception:
            pass


# ---------------- Anki (local file) helpers ----------------

def find_collection_path():
    if COLLECTION_PATH:
        return COLLECTION_PATH

    appdata = os.environ.get("APPDATA")
    if not appdata:
        raise RuntimeError("Couldn't find %APPDATA%; set COLLECTION_PATH manually.")

    base = os.path.join(appdata, "Anki2")
    if not os.path.isdir(base):
        raise FileNotFoundError(f"No Anki2 folder found at {base}")

    candidates = []
    for entry in os.listdir(base):
        full = os.path.join(base, entry)
        col = os.path.join(full, "collection.anki2")
        if os.path.isdir(full) and os.path.isfile(col):
            candidates.append(col)

    if not candidates:
        raise FileNotFoundError(f"No collection.anki2 found under {base}")

    candidates.sort(key=os.path.getmtime, reverse=True)
    return candidates[0]


def _day_cutoff_ms(rollover_hour):
    now = datetime.now()
    cutoff = now.replace(hour=rollover_hour, minute=0, second=0, microsecond=0)
    if now < cutoff:
        cutoff -= timedelta(days=1)
    return int(cutoff.timestamp() * 1000)


def get_reviewed_today():
    """Local read: copies the live Anki Desktop collection so we never
    touch or lock the real file, then counts today's reviews."""
    col_path = find_collection_path()

    tmp_dir = tempfile.mkdtemp(prefix="steam_gate_")
    try:
        tmp_col = os.path.join(tmp_dir, "collection.anki2")
        shutil.copy2(col_path, tmp_col)
        for suffix in ("-wal", "-shm"):
            side = col_path + suffix
            if os.path.exists(side):
                shutil.copy2(side, tmp_col + suffix)

        conn = sqlite3.connect(tmp_col)
        try:
            cur = conn.cursor()
            conf_row = cur.execute("SELECT conf FROM col").fetchone()
            rollover = 4
            if conf_row and conf_row[0]:
                try:
                    conf = json.loads(conf_row[0])
                    rollover = conf.get("rollover", 4)
                except (json.JSONDecodeError, TypeError):
                    pass

            cutoff_ms = _day_cutoff_ms(rollover)
            count = cur.execute(
                "SELECT COUNT(*) FROM revlog WHERE id >= ?", (cutoff_ms,)
            ).fetchone()[0]
            return count
        finally:
            conn.close()
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def sync_ankiweb_and_get_reviewed_today(username, password):
    """AnkiWeb sync: uses a dedicated collection file this app owns
    (never the real Anki Desktop profile), so a wrong full-sync
    direction can only affect our own disposable cache, never your
    real data. Runs on a background thread - this call blocks, do not
    call it from the UI thread directly."""
    try:
        import anki.collection as anki_collection
        from anki.sync_pb2 import SyncAuth as SyncAuthMsg
        from anki.errors import SyncError, SyncErrorKind
    except ImportError as e:
        raise RuntimeError("AnkiWeb sync needs the 'anki' package - run: pip install anki") from e

    os.makedirs(CONFIG_DIR, exist_ok=True)
    col = anki_collection.Collection(SYNC_COLLECTION_PATH)
    try:
        cached_hkey, cached_endpoint = load_sync_auth(username)
        auth = SyncAuthMsg(hkey=cached_hkey, endpoint=cached_endpoint or "") if cached_hkey else None

        def fresh_login():
            new_auth = col.sync_login(username=username, password=password, endpoint=None)
            save_sync_auth(username, new_auth.hkey, new_auth.endpoint)
            return new_auth

        if auth is None:
            auth = fresh_login()

        try:
            result = col.sync_collection(auth, False)
        except SyncError as e:
            if e.kind == SyncErrorKind.AUTH:
                auth = fresh_login()
                result = col.sync_collection(auth, False)
            else:
                raise

        if getattr(result, "new_endpoint", ""):
            save_sync_auth(username, auth.hkey, result.new_endpoint)

        if result.required in (result.NO_CHANGES, result.NORMAL_SYNC):
            pass  # collection is now up to date
        elif result.required == result.FULL_DOWNLOAD:
            # Expected the first time: our dedicated cache starts empty,
            # so downloading the real collection is the only sane
            # direction - safe to do automatically since this file is
            # disposable and never uploaded anywhere.
            col.close_for_full_sync()
            col.full_upload_or_download(auth=auth, server_usn=result.server_media_usn, upload=False)
            try:
                col.close()
            except Exception:
                pass
            col = anki_collection.Collection(SYNC_COLLECTION_PATH)
        else:
            # FULL_UPLOAD or ambiguous FULL_SYNC - this would mean our
            # disposable cache somehow looks non-empty to AnkiWeb, which
            # shouldn't happen since we only ever download into it. Refuse
            # to guess a direction rather than risk uploading garbage.
            raise RuntimeError(
                "AnkiWeb sync needs a manual upload/download choice this app won't make "
                f"automatically. Delete this file to force a fresh download: {SYNC_COLLECTION_PATH}"
            )

        rollover = col.get_config("rollover", 4)
        cutoff_ms = _day_cutoff_ms(rollover)
        count = col.db.scalar("select count(*) from revlog where id >= ?", cutoff_ms)
        return count
    finally:
        try:
            col.close()
        except Exception:
            pass


def steam_processes():
    for proc in psutil.process_iter(["pid", "name"]):
        try:
            name = (proc.info["name"] or "").lower()
        except PROC_GONE_ERRORS:
            continue
        if name in STEAM_PROCESS_NAMES:
            yield proc


def kill_steam():
    killed_any = False
    failed_any = False
    for proc in steam_processes():
        try:
            proc.kill()
            killed_any = True
        except psutil.AccessDenied:
            failed_any = True
        except (psutil.NoSuchProcess, psutil.ZombieProcess):
            pass
    return killed_any, failed_any


def notify_blocked(icon, message, title="Steam blocked"):
    try:
        if icon and getattr(icon, "HAS_NOTIFICATION", False):
            icon.notify(message, title)
            return
    except Exception:
        pass
    # Fallback to a native Windows message box. Guard it so a failure here
    # (non-Windows, or MessageBoxW unavailable) can never crash the check
    # loop - the notification is a nicety, not load-bearing.
    try:
        ctypes.windll.user32.MessageBoxW(0, message, title, 0x40 | 0x1000)
    except Exception:
        pass


# ---------------- Tray icon image ----------------

def make_icon_image(color_hex):
    c = color_hex.lstrip("#")
    r, g, b = int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)
    size = 64
    img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    draw.ellipse((4, 4, size - 4, size - 4), fill=(r, g, b, 255), outline=(10, 10, 14, 255), width=3)
    return img


ICON_LOCKED = make_icon_image(ACCENT_RED)
ICON_UNLOCKED = make_icon_image(ACCENT_GREEN)
ICON_ERROR = make_icon_image(ACCENT_AMBER)


# ---------------- Custom HUD widgets ----------------

def _round_rect_points(x1, y1, x2, y2, r):
    return [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r,
            x2, y2 - r, x2, y2, x2 - r, y2, x1 + r, y2,
            x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]


class NeonButton(tk.Canvas):
    def __init__(self, parent, text, command, width=150, height=34,
                 color=ACCENT_CYAN, bg=PANEL, font=None):
        super().__init__(parent, width=width, height=height, bg=bg, highlightthickness=0)
        self.command = command
        self.color = color
        self.bg = bg
        self.width = width
        self.height = height
        self.text = text.upper()
        self.font = font or (FONT_FAMILY, 10, "bold")
        self._hover = False
        self._enabled = True
        self._render()
        self.bind("<Button-1>", self._click)
        self.bind("<Enter>", self._on_enter)
        self.bind("<Leave>", self._on_leave)

    def _render(self):
        self.delete("all")
        if not self._enabled:
            outline = BORDER_DIM
            text_color = "#3a4157"
            pts = _round_rect_points(1, 1, self.width - 1, self.height - 1, 4)
            self.create_polygon(pts, smooth=True, fill=self.bg, outline=outline, width=1.5)
            self.create_text(self.width / 2, self.height / 2, text=self.text,
                              fill=text_color, font=self.font)
            return
        fill = self.color if self._hover else self.bg
        text_color = self.bg if self._hover else self.color
        pts = _round_rect_points(1, 1, self.width - 1, self.height - 1, 4)
        self.create_polygon(pts, smooth=True, fill=fill, outline=self.color, width=1.5)
        self.create_text(self.width / 2, self.height / 2, text=self.text,
                          fill=text_color, font=self.font)

    def set_enabled(self, value):
        self._enabled = bool(value)
        self._hover = False
        self._render()

    def _on_enter(self, e):
        if not self._enabled:
            return
        self._hover = True
        self._render()

    def _on_leave(self, e):
        if not self._enabled:
            return
        self._hover = False
        self._render()

    def _click(self, e):
        if self._enabled and self.command:
            self.command()


class NeonToggle(tk.Canvas):
    def __init__(self, parent, initial, command, width=46, height=24, bg=PANEL, color=ACCENT_CYAN):
        super().__init__(parent, width=width, height=height, bg=bg, highlightthickness=0)
        self.state = bool(initial)
        self.command = command
        self.width = width
        self.height = height
        self.color = color
        self.bg = bg
        self._render()
        self.bind("<Button-1>", self._toggle)

    def _render(self):
        self.delete("all")
        track = self.color if self.state else BORDER_DIM
        pts = _round_rect_points(0, 0, self.width, self.height, self.height / 2)
        self.create_polygon(pts, smooth=True, fill=track, outline="")
        knob_d = self.height - 4
        x = self.width - knob_d - 2 if self.state else 2
        knob_color = self.bg if self.state else TEXT_SECONDARY
        self.create_oval(x, 2, x + knob_d, 2 + knob_d, fill=knob_color, outline="")

    def set_state(self, value):
        self.state = bool(value)
        self._render()

    def _toggle(self, e):
        self.state = not self.state
        self._render()
        if self.command:
            self.command(self.state)


class RingGauge(tk.Canvas):
    def __init__(self, parent, size=160, thickness=10, bg=PANEL):
        super().__init__(parent, width=size, height=size, bg=bg, highlightthickness=0)
        self.size = size
        self.thickness = thickness
        self.bg = bg

    def set(self, fraction, value_text, sub_text, color):
        self.delete("all")
        fraction = max(0.0, min(1.0, fraction))
        pad = self.thickness + 6
        x0, y0, x1, y1 = pad, pad, self.size - pad, self.size - pad

        track_color = lerp_color(self.bg, color, 0.18)
        self.create_oval(x0, y0, x1, y1, outline=track_color, width=self.thickness)

        extent = -359.9 if fraction >= 0.999 else -360 * fraction
        if abs(extent) > 0.01:
            glow_color = lerp_color(self.bg, color, 0.55)
            self.create_arc(x0 - 3, y0 - 3, x1 + 3, y1 + 3, start=90, extent=extent,
                             style="arc", outline=glow_color, width=self.thickness + 7)
            self.create_arc(x0, y0, x1, y1, start=90, extent=extent,
                             style="arc", outline=color, width=self.thickness)

        cx, cy = self.size / 2, self.size / 2
        self.create_text(cx, cy - 10, text=value_text, fill=TEXT_PRIMARY,
                          font=(FONT_FAMILY, 22, "bold"))
        self.create_text(cx, cy + 17, text=sub_text, fill=TEXT_SECONDARY,
                          font=(FONT_FAMILY, 8))


def make_glow_divider(parent, width=300, color=ACCENT_CYAN, bg=PANEL, segments=50):
    c = tk.Canvas(parent, width=width, height=2, bg=bg, highlightthickness=0)
    seg_w = width / segments
    mid = segments / 2
    for i in range(segments):
        t = 1 - abs((i - mid) / mid)
        col = lerp_color(bg, color, max(t, 0) * 0.9)
        c.create_rectangle(i * seg_w, 0, (i + 1) * seg_w, 2, fill=col, outline=col)
    return c


# ---------------- Main app ----------------

class SteamGateApp:
    WIDTH = 420
    MAX_HEIGHT_MARGIN = 60  # keep this much screen height free (taskbar etc.)

    def __init__(self, root, icon):
        self.root = root
        self.icon = icon
        self.last_blocked_state = False
        self.target = load_target()
        self.auto_quit_on_unlock = load_auto_quit()
        self._after_id = None
        self._icon_photo = None
        self._quitting = False
        # Tracks Steam's running state between checks so auto-quit fires only
        # when Steam *launches* (a rising edge), not on every check where it
        # happens to be running. None = first check hasn't run yet, so a
        # launch into already-running Steam is never treated as a transition
        # (that's what lets you open the app while already gaming).
        self._prev_steam_running = None

        # AnkiWeb sync state
        self.sync_enabled = load_sync_enabled()
        self.ankiweb_username = load_ankiweb_username()
        self.synced_count = None
        self.last_sync_time = 0.0
        self.last_sync_error = None
        self._sync_thread_running = False

        root.title("Steam Gate")
        root.overrideredirect(True)
        root.configure(bg=BG)
        # Taskbar right-click "Close window" and Alt+F4 both send this - make
        # them hide the window too, same as the title bar's own X. The tray
        # icon's "Quit" is the only thing that actually calls quit_app().
        root.protocol("WM_DELETE_WINDOW", root.withdraw)
        root.withdraw()  # build off-screen so nothing flashes/resizes visibly

        self._build_titlebar()
        self._build_card()

        # Size the window to what its content actually needs, rather than a
        # guessed constant - guessed heights silently clip whatever's near
        # the bottom (e.g. the AnkiWeb password hint) when content grows.
        self.root.update_idletasks()
        natural_height = self.root.winfo_reqheight()
        screen_height = self.root.winfo_screenheight()
        self.height = min(natural_height, screen_height - self.MAX_HEIGHT_MARGIN)
        self._center_window()

        self._enable_taskbar_presence()

        self.check_now()

    # ---- layout ----

    def _enable_taskbar_presence(self):
        """overrideredirect() windows don't get a taskbar button by default
        on Windows - it's what removes the native title bar for our custom
        one. Force a taskbar entry back via the WS_EX_APPWINDOW style, so
        the app shows up in both the taskbar and the tray icon. No-op (and
        harmless) on non-Windows or if the API calls fail for any reason."""
        try:
            GWL_EXSTYLE = -20
            WS_EX_APPWINDOW = 0x00040000
            WS_EX_TOOLWINDOW = 0x00000080
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id())
            style = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
            style = (style & ~WS_EX_TOOLWINDOW) | WS_EX_APPWINDOW
            ctypes.windll.user32.SetWindowLongW(hwnd, GWL_EXSTYLE, style)
            # Windows only (re-)registers the taskbar button on a visibility
            # change, so cycle it once - ends withdrawn, matching the app's
            # normal "starts in the tray" behavior. (Tk refuses to iconify
            # an override-redirect window outright, so the taskbar button
            # only persists while the window is actually shown, not while
            # fully hidden - see the note at the bottom of this file.)
            self.root.deiconify()
            self.root.withdraw()
        except Exception:
            pass

    def _center_window(self):
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = (sw - self.WIDTH) // 2
        y = max(0, (sh - self.height) // 2)
        self.root.geometry(f"{self.WIDTH}x{self.height}+{x}+{y}")

    def _build_titlebar(self):
        bar = tk.Frame(self.root, bg=TITLEBAR, height=34)
        bar.pack(fill="x", side="top")
        bar.pack_propagate(False)

        left = tk.Frame(bar, bg=TITLEBAR)
        left.pack(side="left", padx=14)

        self.status_dot = tk.Canvas(left, width=10, height=10, bg=TITLEBAR, highlightthickness=0)
        self.status_dot_item = self.status_dot.create_oval(1, 1, 9, 9, fill=ACCENT_CYAN, outline="")
        self.status_dot.pack(side="left", padx=(0, 8))

        title = tk.Label(left, text=spaced("STEAM GATE"), bg=TITLEBAR, fg=TEXT_SECONDARY,
                          font=(FONT_FAMILY, 9, "bold"))
        title.pack(side="left")

        hide_btn = tk.Canvas(bar, width=22, height=22, bg=TITLEBAR, highlightthickness=0)
        hide_btn.create_line(7, 7, 15, 15, fill=TEXT_SECONDARY, width=1.5)
        hide_btn.create_line(15, 7, 7, 15, fill=TEXT_SECONDARY, width=1.5)
        hide_btn.pack(side="right", padx=12)
        hide_btn.bind("<Button-1>", lambda e: self.root.withdraw())

        for widget in (bar, left, title):
            widget.bind("<ButtonPress-1>", self._start_drag)
            widget.bind("<B1-Motion>", self._do_drag)

    def _start_drag(self, event):
        self._drag_x = event.x
        self._drag_y = event.y

    def _do_drag(self, event):
        x = self.root.winfo_pointerx() - self._drag_x
        y = self.root.winfo_pointery() - self._drag_y
        self.root.geometry(f"+{x}+{y}")

    def _build_card(self):
        outer = tk.Frame(self.root, bg=BG)
        outer.pack(fill="both", expand=True, padx=14, pady=(0, 14))

        self.halo = tk.Frame(outer, bg=lerp_color(BG, ACCENT_CYAN, 0.35))
        self.halo.pack(fill="both", expand=True)

        card = tk.Frame(self.halo, bg=PANEL)
        card.pack(fill="both", expand=True, padx=1, pady=1)
        self.card = card

        caption = tk.Label(card, text=spaced("DAILY REVIEW GATE"),
                            font=(FONT_FAMILY, 8), fg=TEXT_SECONDARY, bg=PANEL)
        caption.pack(pady=(10, 2))

        self.ring = RingGauge(card, size=132, thickness=9)
        self.ring.pack(pady=(2, 4))

        self.status_label = tk.Label(card, text="CHECKING...", font=(FONT_FAMILY, 14, "bold"),
                                      fg=TEXT_PRIMARY, bg=PANEL)
        self.status_label.pack(pady=(0, 3))

        self.detail_label = tk.Label(card, text="", font=(FONT_FAMILY, 9), fg=TEXT_SECONDARY,
                                      bg=PANEL, wraplength=340, justify="center")
        self.detail_label.pack(pady=(0, 2))

        self.sync_status_label = tk.Label(card, text="", font=(FONT_FAMILY, 8), fg="#4b5468",
                                           bg=PANEL, wraplength=340, justify="center")
        self.sync_status_label.pack(pady=(0, 6))

        self.check_button = NeonButton(card, "Check Now", self.manual_check,
                                        width=140, height=30, color=ACCENT_CYAN)
        self.check_button.pack(pady=(0, 8))

        make_glow_divider(card, width=340, color=ACCENT_CYAN, bg=PANEL).pack()

        settings_label = tk.Label(card, text=spaced("SETTINGS"), font=(FONT_FAMILY, 8, "bold"),
                                   fg=TEXT_SECONDARY, bg=PANEL)
        settings_label.pack(pady=(8, 6))

        # --- Daily target (locks for a month once committed) ---
        target_row = tk.Frame(card, bg=PANEL)
        target_row.pack(padx=36, pady=(0, 2), fill="x")

        tk.Label(target_row, text="Daily card target", font=(FONT_FAMILY, 10),
                 fg=TEXT_PRIMARY, bg=PANEL).pack(side="left")

        entry_area = tk.Frame(target_row, bg=PANEL)
        entry_area.pack(side="right")

        digits_only = (self.root.register(self._validate_digits), "%P")
        self.target_var = tk.StringVar(value=str(self.target))
        self.target_entry = tk.Entry(entry_area, width=5, textvariable=self.target_var,
                                      justify="center", font=(FONT_FAMILY, 10, "bold"),
                                      relief="flat", bg=BG, fg=TEXT_PRIMARY,
                                      insertbackground=ACCENT_CYAN,
                                      highlightthickness=1, highlightbackground=BORDER_DIM,
                                      highlightcolor=ACCENT_CYAN,
                                      validate="key", validatecommand=digits_only)
        self.target_entry.pack(side="left", ipady=3, padx=(0, 10))
        self.target_entry.bind("<Return>", lambda e: self.apply_target())

        self.set_button = NeonButton(entry_area, "Set", self.apply_target, width=52, height=26,
                                      color=ACCENT_CYAN, font=(FONT_FAMILY, 9, "bold"))
        self.set_button.pack(side="left")

        self.target_lock_label = tk.Label(card, text="", font=(FONT_FAMILY, 8),
                                           fg="#4b5468", bg=PANEL, wraplength=340,
                                           justify="center")
        self.target_lock_label.pack(padx=36, pady=(0, 6))
        self._refresh_target_lock_ui()

        # --- Auto-quit toggle ---
        auto_quit_row = tk.Frame(card, bg=PANEL)
        auto_quit_row.pack(padx=36, pady=(0, 2), fill="x")

        tk.Label(auto_quit_row, text="Close app once unlocked", font=(FONT_FAMILY, 10),
                 fg=TEXT_PRIMARY, bg=PANEL).pack(side="left")

        self.auto_quit_toggle = NeonToggle(auto_quit_row, self.auto_quit_on_unlock,
                                            self._on_auto_quit_toggle)
        self.auto_quit_toggle.pack(side="right")

        tk.Label(card, text="Closes fully once Steam opens after target is met.",
                 font=(FONT_FAMILY, 8), fg="#4b5468", bg=PANEL, justify="center").pack(
            padx=36, pady=(0, 2))

        make_glow_divider(card, width=340, color=ACCENT_CYAN, bg=PANEL).pack(pady=(4, 0))

        ankiweb_label = tk.Label(card, text=spaced("ANKIWEB SYNC"), font=(FONT_FAMILY, 8, "bold"),
                                  fg=TEXT_SECONDARY, bg=PANEL)
        ankiweb_label.pack(pady=(8, 6))

        sync_toggle_row = tk.Frame(card, bg=PANEL)
        sync_toggle_row.pack(padx=36, pady=(0, 6), fill="x")

        tk.Label(sync_toggle_row, text="Sync with AnkiWeb", font=(FONT_FAMILY, 10),
                 fg=TEXT_PRIMARY, bg=PANEL).pack(side="left")

        self.sync_toggle = NeonToggle(sync_toggle_row, self.sync_enabled, self._on_sync_toggle)
        self.sync_toggle.pack(side="right")

        cred_frame = tk.Frame(card, bg=PANEL)
        cred_frame.pack(padx=36, pady=(0, 3), fill="x")

        tk.Label(cred_frame, text="Email", font=(FONT_FAMILY, 9), fg=TEXT_SECONDARY,
                 bg=PANEL, anchor="w").grid(row=0, column=0, sticky="w", pady=2)
        self.username_var = tk.StringVar(value=self.ankiweb_username)
        self.username_entry = tk.Entry(cred_frame, textvariable=self.username_var,
                                        font=(FONT_FAMILY, 10), relief="flat", bg=BG,
                                        fg=TEXT_PRIMARY, insertbackground=ACCENT_CYAN,
                                        highlightthickness=1, highlightbackground=BORDER_DIM,
                                        highlightcolor=ACCENT_CYAN)
        self.username_entry.grid(row=0, column=1, sticky="ew", pady=2, ipady=3, padx=(8, 0))

        tk.Label(cred_frame, text="Password", font=(FONT_FAMILY, 9), fg=TEXT_SECONDARY,
                 bg=PANEL, anchor="w").grid(row=1, column=0, sticky="w", pady=2)
        self.password_var = tk.StringVar(value="")
        self.password_entry = tk.Entry(cred_frame, textvariable=self.password_var, show="\u2022",
                                        font=(FONT_FAMILY, 10), relief="flat", bg=BG,
                                        fg=TEXT_PRIMARY, insertbackground=ACCENT_CYAN,
                                        highlightthickness=1, highlightbackground=BORDER_DIM,
                                        highlightcolor=ACCENT_CYAN)
        self.password_entry.grid(row=1, column=1, sticky="ew", pady=2, ipady=3, padx=(8, 0))
        cred_frame.grid_columnconfigure(1, weight=1)

        has_saved_pw, _cred_err = safe_get_ankiweb_password(self.ankiweb_username) if self.ankiweb_username else (None, None)
        has_saved_pw = bool(has_saved_pw)
        self.password_hint_label = tk.Label(
            card, text=("Password saved" if has_saved_pw else "No password saved yet"),
            font=(FONT_FAMILY, 8), fg=(ACCENT_GREEN if has_saved_pw else "#4b5468"), bg=PANEL)
        self.password_hint_label.pack(pady=(0, 6))

        cred_btn_row = tk.Frame(card, bg=PANEL)
        cred_btn_row.pack(pady=(0, 2))

        NeonButton(cred_btn_row, "Save & Sync", self._save_ankiweb_credentials,
                   width=130, height=27, color=ACCENT_CYAN, font=(FONT_FAMILY, 9, "bold")
                   ).pack(side="left", padx=(0, 8))
        NeonButton(cred_btn_row, "Forget", self._forget_ankiweb_credentials,
                   width=80, height=27, color=ACCENT_RED, font=(FONT_FAMILY, 9, "bold")
                   ).pack(side="left")

        self.last_checked_label = tk.Label(card, text="", font=(FONT_FAMILY, 8),
                                            fg="#4b5468", bg=PANEL)
        self.last_checked_label.pack(side="bottom", pady=8)

        self._update_sync_status_label()

    @staticmethod
    def _validate_digits(proposed):
        return proposed == "" or proposed.isdigit()

    # ---- behavior: window / tray ----

    def show_window(self):
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()

    def _window_visible(self):
        """True if the details window is currently shown (not hidden in the
        tray). Used so auto-quit never yanks the app out from under you
        while you're actually looking at it."""
        try:
            return self.root.state() == "normal"
        except Exception:
            return False

    def _confirm_dialog(self, title, message, on_yes):
        """A small themed modal Yes/No confirmation, matching the HUD look
        (tk's default messagebox would be jarring gray). Calls on_yes()
        only if the user confirms."""
        dlg = tk.Toplevel(self.root)
        dlg.overrideredirect(True)
        dlg.configure(bg=lerp_color(BG, ACCENT_AMBER, 0.35))

        DW, DH = 340, 210
        # Center over the main window if it's visible, else over the screen.
        try:
            if self.root.state() == "normal":
                px = self.root.winfo_rootx() + (self.WIDTH - DW) // 2
                py = self.root.winfo_rooty() + (self.height - DH) // 2
            else:
                raise RuntimeError
        except Exception:
            px = (self.root.winfo_screenwidth() - DW) // 2
            py = (self.root.winfo_screenheight() - DH) // 2
        dlg.geometry(f"{DW}x{DH}+{max(0, px)}+{max(0, py)}")

        inner = tk.Frame(dlg, bg=PANEL)
        inner.pack(fill="both", expand=True, padx=1, pady=1)

        tk.Label(inner, text=spaced(title.upper()), font=(FONT_FAMILY, 11, "bold"),
                 fg=ACCENT_AMBER, bg=PANEL, wraplength=300).pack(pady=(22, 12))
        tk.Label(inner, text=message, font=(FONT_FAMILY, 9), fg=TEXT_PRIMARY, bg=PANEL,
                 wraplength=290, justify="center").pack(pady=(0, 18), padx=20)

        btn_row = tk.Frame(inner, bg=PANEL)
        btn_row.pack()

        dlg.grab_set()  # modal - block interaction with the main window

        def close():
            try:
                dlg.grab_release()
            except Exception:
                pass
            dlg.destroy()

        def confirm():
            close()
            on_yes()

        NeonButton(btn_row, "Cancel", close, width=110, height=30,
                   color=TEXT_SECONDARY, font=(FONT_FAMILY, 9, "bold")).pack(side="left", padx=(0, 10))
        NeonButton(btn_row, "Lock it in", confirm, width=120, height=30,
                   color=ACCENT_AMBER, font=(FONT_FAMILY, 9, "bold")).pack(side="left")

        dlg.bind("<Escape>", lambda e: close())
        dlg.lift()
        dlg.focus_force()

    def _on_auto_quit_toggle(self, new_state):
        self.auto_quit_on_unlock = new_state
        save_auto_quit(new_state)

    def quit_app(self):
        # The tray menu's "Quit" fires on pystray's thread, not Tk's. Doing
        # the teardown directly from there races with the Tk main loop and
        # can leave the process alive. So marshal the whole shutdown onto
        # the Tk thread via after(), and do it only once.
        if self._quitting:
            return
        self._quitting = True
        try:
            self.root.after(0, self._do_quit)
        except Exception:
            # Tk loop already gone - fall back to a hard exit.
            self._hard_exit()

    def _do_quit(self):
        # Runs on the Tk thread.
        if self._after_id is not None:
            try:
                self.root.after_cancel(self._after_id)
            except Exception:
                pass
        # Stop the tray icon on a separate thread: icon.stop() can block,
        # and we must not block the Tk thread while doing it.
        try:
            threading.Thread(target=self._stop_icon, daemon=True).start()
        except Exception:
            pass
        try:
            self.root.quit()      # break out of mainloop()
            self.root.destroy()   # tear down all widgets
        except Exception:
            pass
        # Backstop: whatever the state of the tray thread or leftover
        # non-daemon threads, guarantee the process actually exits shortly
        # after. Without this the pythonw/exe build can keep running with no
        # window and no tray icon - exactly the "it remains" symptom.
        self._hard_exit()

    def _stop_icon(self):
        try:
            self.icon.stop()
        except Exception:
            pass

    def _hard_exit(self):
        # Give the icon a brief moment to disappear from the tray, then
        # force-terminate. os._exit skips atexit/GC but guarantees the
        # process is gone - appropriate for a definitive "Quit".
        def _boom():
            try:
                self.icon.stop()
            except Exception:
                pass
            os._exit(0)
        t = threading.Timer(0.4, _boom)
        t.daemon = True
        t.start()

    def _refresh_target_lock_ui(self):
        """Enable/disable the target entry + Set button and show the lock
        status line, based on whether the monthly lock is currently active."""
        locked = target_is_locked()
        if locked:
            unlock_dt = datetime.fromtimestamp(load_target_locked_until())
            self.target_entry.config(state="disabled", disabledbackground=BG,
                                      disabledforeground="#3a4157")
            self.set_button.set_enabled(False)
            self.target_lock_label.config(
                text=f"Locked until {unlock_dt.strftime('%b %d, %Y')}. "
                     "The target can only be changed once a month.",
                fg=ACCENT_AMBER)
        else:
            self.target_entry.config(state="normal")
            self.set_button.set_enabled(True)
            self.target_lock_label.config(
                text="Setting a target locks it for a month - choose carefully.",
                fg="#4b5468")

    def apply_target(self):
        if target_is_locked():
            # Shouldn't be reachable (button/entry are disabled), but guard
            # anyway in case something calls this directly.
            self._refresh_target_lock_ui()
            return

        raw = self.target_var.get().strip()
        try:
            val = int(raw)
            if val <= 0:
                raise ValueError
        except ValueError:
            self.detail_label.config(text="Enter a positive whole number for the target.",
                                      fg=ACCENT_RED)
            self.target_var.set(str(self.target))
            return

        unlock_dt = datetime.now() + timedelta(days=TARGET_LOCK_DAYS)
        self._confirm_dialog(
            title="Lock in this target?",
            message=(f"Set your daily target to {val} card(s)?\n\n"
                     f"You won't be able to change it again until "
                     f"{unlock_dt.strftime('%b %d, %Y')} "
                     f"({TARGET_LOCK_DAYS} days from now)."),
            on_yes=lambda: self._commit_target(val),
        )

    def _commit_target(self, val):
        self.target = val
        save_target(val)
        save_target_locked_until(time.time() + TARGET_LOCK_DAYS * 86400)
        self._refresh_target_lock_ui()
        self.check_now()

    def manual_check(self):
        self._maybe_start_background_sync(force=True)
        self.check_now()

    # ---- behavior: AnkiWeb sync ----

    def _on_sync_toggle(self, new_state):
        self.sync_enabled = new_state
        save_sync_enabled(new_state)
        self._update_sync_status_label()

    def _save_ankiweb_credentials(self):
        username = self.username_var.get().strip()
        if not username:
            self.sync_status_label.config(text="Enter an AnkiWeb email first.", fg=ACCENT_RED)
            return

        self.ankiweb_username = username
        save_ankiweb_username(username)

        pw = self.password_var.get()
        if pw:
            try:
                save_ankiweb_password(username, pw)
            except RuntimeError as e:
                self.sync_status_label.config(text=str(e), fg=ACCENT_RED)
                return
            self.password_var.set("")
            self.password_hint_label.config(text="Password saved", fg=ACCENT_GREEN)

        self.sync_enabled = True
        save_sync_enabled(True)
        self.sync_toggle.set_state(True)

        self.sync_status_label.config(text="Saved - syncing now...", fg=TEXT_SECONDARY)
        self._maybe_start_background_sync(force=True)

    def _forget_ankiweb_credentials(self):
        if self.ankiweb_username:
            try:
                forget_ankiweb_credentials(self.ankiweb_username)
            except RuntimeError:
                pass
        self.ankiweb_username = ""
        save_ankiweb_username("")
        self.sync_enabled = False
        save_sync_enabled(False)
        self.sync_toggle.set_state(False)
        self.synced_count = None
        self.last_sync_error = None
        self.username_var.set("")
        self.password_var.set("")
        self.password_hint_label.config(text="No password saved yet", fg="#4b5468")
        self._update_sync_status_label()

    def _maybe_start_background_sync(self, force=False):
        if not self.sync_enabled or not self.ankiweb_username or self._sync_thread_running:
            return
        now = time.time()
        if not force and (now - self.last_sync_time) < SYNC_INTERVAL_SECONDS:
            return
        password, cred_err = safe_get_ankiweb_password(self.ankiweb_username)
        if cred_err:
            self.last_sync_error = cred_err
            self.last_sync_time = time.time()  # respect the retry interval instead of spamming every check
            self._update_sync_status_label()
            return
        if not password:
            self.last_sync_error = "No AnkiWeb password saved."
            self.last_sync_time = time.time()
            self._update_sync_status_label()
            return

        self._sync_thread_running = True
        self._update_sync_status_label()
        threading.Thread(target=self._sync_worker, args=(self.ankiweb_username, password),
                          daemon=True).start()

    def _sync_worker(self, username, password):
        try:
            count = sync_ankiweb_and_get_reviewed_today(username, password)
            self.root.after(0, self._on_sync_done, count, None)
        except Exception as e:
            self.root.after(0, self._on_sync_done, None, str(e))

    def _on_sync_done(self, count, error):
        self._sync_thread_running = False
        self.last_sync_time = time.time()
        if count is not None:
            self.synced_count = count
            self.last_sync_error = None
        else:
            self.last_sync_error = error
        self._update_sync_status_label()
        if not self._quitting:
            self.check_now()

    def _update_sync_status_label(self):
        if not self.sync_enabled:
            self.sync_status_label.config(text="")
            return
        if self._sync_thread_running:
            self.sync_status_label.config(text="AnkiWeb: syncing...", fg=TEXT_SECONDARY)
            return
        if self.last_sync_error:
            short = self.last_sync_error if len(self.last_sync_error) < 80 \
                else self.last_sync_error[:77] + "..."
            self.sync_status_label.config(text=f"AnkiWeb sync failed: {short}", fg=ACCENT_AMBER)
            return
        if self.last_sync_time == 0:
            self.sync_status_label.config(text="AnkiWeb: not synced yet", fg="#4b5468")
            return
        elapsed = int(time.time() - self.last_sync_time)
        when = "just now" if elapsed < 60 else f"{elapsed // 60}m ago"
        self.sync_status_label.config(text=f"AnkiWeb synced {when}", fg=ACCENT_GREEN)

    # ---- behavior: main check loop ----

    def _apply_state_color(self, color):
        self.halo.config(bg=lerp_color(BG, color, 0.35))
        try:
            self.status_dot.itemconfig(self.status_dot_item, fill=color)
        except Exception:
            pass

    def check_now(self):
        if self._quitting:
            return

        self._maybe_start_background_sync()

        try:
            local_reviewed = get_reviewed_today()
            local_error = None
        except Exception as e:
            local_reviewed = None
            local_error = str(e)

        steam_running = any(True for _ in steam_processes())
        # Rising edge: Steam was not running on the previous check and is now.
        # _prev_steam_running is None only on the very first check, so a fresh
        # launch into already-running Steam is NOT a launch event - that's the
        # case where you deliberately opened the app while gaming and want it
        # to stay open.
        steam_just_launched = (self._prev_steam_running is False) and steam_running

        if local_reviewed is None and self.synced_count is None:
            self.status_label.config(text=spaced("READ ERROR"), fg=ACCENT_AMBER)
            self.detail_label.config(text=local_error or "Unknown error", fg=TEXT_SECONDARY)
            self.ring.set(0, "--", "NO DATA", ACCENT_AMBER)
            self._apply_state_color(ACCENT_AMBER)
            self._set_icon(ICON_ERROR, "Steam Gate - error reading Anki data")
            if steam_running:
                killed, failed = kill_steam()
                if failed:
                    self.detail_label.config(
                        text=(local_error or "Unknown error") +
                             "\nAlso couldn't close Steam - try running this app as Administrator.",
                        fg=ACCENT_RED)
                if not self.last_blocked_state:
                    notify_blocked(self.icon, "Couldn't read your Anki review count, "
                                               "so Steam is blocked by default.")
                self.last_blocked_state = True
        else:
            candidates = [v for v in (local_reviewed, self.synced_count) if v is not None]
            reviewed = max(candidates)
            fraction = reviewed / self.target if self.target else 0

            if reviewed >= self.target:
                self.status_label.config(text=spaced("UNLOCKED"), fg=ACCENT_GREEN)
                self.ring.set(fraction, f"{reviewed}/{self.target}", "CARDS TODAY", ACCENT_GREEN)
                self._apply_state_color(ACCENT_GREEN)
                self._set_icon(ICON_UNLOCKED, f"Steam Gate - unlocked ({reviewed}/{self.target})")
                self.last_blocked_state = False

                # Auto-quit to save resources while gaming - but only when
                # Steam has just LAUNCHED (not merely running), and only when
                # the window isn't open. If you've opened the app - or you
                # relaunched it while already gaming - it stays put so you can
                # actually use it. It'll still auto-close the next time Steam
                # is launched from a fresh start.
                if (self.auto_quit_on_unlock and steam_just_launched
                        and not self._window_visible()):
                    self.detail_label.config(
                        text="Target met - closing Steam Gate to free up resources while you game.",
                        fg=TEXT_SECONDARY)
                    self.last_checked_label.config(
                        text=f"Last checked {datetime.now().strftime('%H:%M:%S')}")
                    notify_blocked(
                        self.icon,
                        "Target met for today - Steam Gate is closing to save resources while you game. "
                        "It'll come back next time it's launched.",
                        title="Steam Gate")
                    self._prev_steam_running = steam_running
                    self.root.after(1200, self.quit_app)
                    return

                self.detail_label.config(text="Target met for today. Enjoy.", fg=TEXT_SECONDARY)
            else:
                remaining = self.target - reviewed
                self.status_label.config(text=spaced("LOCKED"), fg=ACCENT_RED)
                self.detail_label.config(text=f"{remaining} more card(s) to unlock Steam.",
                                          fg=TEXT_SECONDARY)
                self.ring.set(fraction, f"{reviewed}/{self.target}", "CARDS TODAY", ACCENT_RED)
                self._apply_state_color(ACCENT_RED)
                self._set_icon(ICON_LOCKED, f"Steam Gate - locked ({reviewed}/{self.target})")
                if steam_running:
                    killed, failed = kill_steam()
                    if failed:
                        self.detail_label.config(
                            text=f"{remaining} more card(s) to unlock Steam.\n"
                                 "Also couldn't close Steam - try running this app as Administrator.",
                            fg=ACCENT_RED)
                    if not self.last_blocked_state:
                        notify_blocked(self.icon,
                                        f"You've reviewed {reviewed}/{self.target} Anki cards today. "
                                        f"Finish {remaining} more to unlock Steam.")
                    self.last_blocked_state = True
                else:
                    self.last_blocked_state = False

        self._prev_steam_running = steam_running
        self._update_sync_status_label()
        self._refresh_target_lock_ui()  # keep lock state fresh if the month elapses while open
        self.last_checked_label.config(text=f"Last checked {datetime.now().strftime('%H:%M:%S')}")
        self.schedule_next()

    def schedule_next(self):
        if self._quitting:
            return
        if self._after_id is not None:
            try:
                self.root.after_cancel(self._after_id)
            except Exception:
                pass
        self._after_id = self.root.after(CHECK_INTERVAL_MS, self.check_now)

    def _set_icon(self, image, title):
        try:
            self.icon.icon = image
            self.icon.title = title
        except Exception:
            pass
        try:
            self._icon_photo = ImageTk.PhotoImage(image)
            self.root.iconphoto(False, self._icon_photo)
        except Exception:
            pass


app_ref = {"app": None}


def on_open(icon, item):
    if app_ref["app"]:
        app_ref["app"].root.after(0, app_ref["app"].show_window)


def on_check_now(icon, item):
    if app_ref["app"]:
        app_ref["app"].root.after(0, app_ref["app"].manual_check)


def on_quit(icon, item):
    if app_ref["app"]:
        app_ref["app"].quit_app()


def status_text(item):
    app = app_ref["app"]
    if not app:
        return "Steam Gate"
    return app.status_label.cget("text")


def setup(icon):
    icon.visible = True
    root = tk.Tk()
    app = SteamGateApp(root, icon)
    app_ref["app"] = app
    root.mainloop()


def main():
    menu = pystray.Menu(
        pystray.MenuItem("Open Steam Gate", on_open, default=True),
        pystray.MenuItem(status_text, None, enabled=False),
        pystray.Menu.SEPARATOR,
        pystray.MenuItem("Check now", on_check_now),
        pystray.MenuItem("Quit", on_quit),
    )
    icon = pystray.Icon("steam_gate", ICON_ERROR, "Steam Gate - starting...", menu)
    icon.run(setup=setup)


if __name__ == "__main__":
    main()

# --------------------------------------------------------------------
# HOW TO RUN THIS WITHOUT A CONSOLE WINDOW
#
# python steam_gate.py runs attached to that Command Prompt window;
# closing the Command Prompt kills the app with it. Use pythonw.exe
# instead (no console at all):
#
#     pythonw steam_gate.py
#
# Or rename this file to steam_gate.pyw and double-click it.
#
# RUN AT STARTUP (Windows)
#   Win+R -> shell:startup -> create a shortcut to:
#     pythonw.exe "C:\path\to\steam_gate.py"
#   (or point it straight at steam_gate.pyw), or use Task Scheduler
#   with an "At log on" trigger running the same command.
#
# ABOUT THE DAILY TARGET LOCK
#  - Setting a daily target now pops a confirmation, and once you
#    confirm, the target locks for 30 days - the entry field and Set
#    button are disabled and a line shows the unlock date. This is
#    deliberate: it stops you from lowering the bar on a hard day.
#  - The lock is stored as an unlock timestamp in
#    %APPDATA%\SteamGate\config.json ("target_locked_until"). When the
#    30 days elapse, the field re-enables automatically (even if the
#    app was left running the whole time).
#  - To change TARGET_LOCK_DAYS, edit the constant near the top. Note
#    that config.json is plain JSON a determined user could edit by
#    hand to unlock early - this is a commitment aid, not tamper-proof
#    enforcement.
#
# ABOUT "CLOSE APP ONCE UNLOCKED" (auto-quit)
#  - When on (default), the app quits itself to save resources the
#    moment Steam is LAUNCHED after you've met today's target - keyed
#    to Steam actually starting up, not to it merely already running.
#  - So you can still open the app whenever you like once the goal is
#    met: relaunching it while you're already gaming keeps it open, and
#    it never closes out from under a window you've got open. It just
#    auto-closes again the next time Steam is launched from scratch.
#
# ABOUT THE TASKBAR ICON
#  - The app now shows a taskbar button whenever its window is open, in
#    addition to the tray icon (previously it never appeared in the
#    taskbar at all). Clicking the title bar's X, using the taskbar's
#    right-click "Close window", or Alt+F4 all just hide the window -
#    none of them quit the app. The only way to actually exit is
#    "Quit" from the tray icon's right-click menu (or the "Close app
#    once unlocked" auto-quit feature, if that's turned on).
#  - The taskbar button disappears when the window is hidden, same as
#    most "minimize to tray" utilities - Tk itself refuses to truly
#    minimize (iconify) a custom-chrome window like this one's, so a
#    taskbar entry that persists even while fully hidden isn't safely
#    achievable here. The tray icon is what's always present.
#
# ABOUT ANKIWEB SYNC
#  - Optional. Needs: pip install anki keyring
#  - Your AnkiWeb password is stored via the `keyring` package, which
#    uses the Windows Credential Manager - not a plain text file. The
#    daily target and the "sync enabled" flag live in
#    %APPDATA%\SteamGate\config.json; the password itself never does.
#  - Syncing uses a SEPARATE collection file this app owns
#    (%APPDATA%\SteamGate\sync_collection.anki2) - it downloads a copy
#    of your AnkiWeb data into that file only. It never opens, syncs,
#    or modifies your real Anki Desktop profile.
#  - Background syncs happen at most every two minutes automatically;
#    "Check Now" always forces an immediate one. Steam-blocking itself
#    still reacts within ~5 seconds either way, using whichever count
#    (local file vs last AnkiWeb sync) is currently higher.
#  - If sync ever reports it needs a manual upload/download choice
#    (which shouldn't normally happen, since this app only ever
#    downloads into its own cache), delete sync_collection.anki2 to
#    force a clean re-download next sync.
# --------------------------------------------------------------------
