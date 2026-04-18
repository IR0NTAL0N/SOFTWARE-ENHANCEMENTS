#!/usr/bin/env python3
r"""
Plex Playlist Organizer GUI v8
==============================

Major changes:
- Duplicate-title block move bug fixed by using Plex item IDs, not title text
- One global Plex token in General config
- Backup root in General config
- Server settings now only store name + base URL
- If config.json is missing or invalid, app opens Config first and can create it on save
- Search moved to the top row and acts as navigation, not filtering
- Copy current playlist from one server to another by title matching
- Optimized reordering by keeping an in-memory working order during move/apply operations
"""

from __future__ import annotations

import csv
import json
import shutil
import subprocess
import sys
import threading
import traceback
import uuid
from copy import deepcopy
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from collections import defaultdict
from time import sleep, monotonic
import socket
from typing import Any, Dict, List, Optional, Tuple
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk


CONFIG_PATH = Path("config.json")
DEFAULT_CONFIG = {
    "plex_token": "",
    "backup_root": r"W:\MediaServer\PlaylistOrganizer",
    "timeout_seconds": 60,
    "restore_pause_ms": 150,
    "suppress_confirmations": False,
    "db_backup_schedule": "weekly",
    "db_backup_retention": 5,
    "db_backup_time": "03:00",
    "servers": [
        {
            "name": "MediaServer",
            "base_url": "http://192.168.1.21:32400",
            "plex_db_path": ""
        }
    ]
}

FIRST_RUN_CONFIG = {
    "plex_token": "",
    "backup_root": "",
    "timeout_seconds": 60,
    "restore_pause_ms": 150,
    "suppress_confirmations": False,
    "db_backup_schedule": "weekly",
    "db_backup_retention": 5,
    "db_backup_time": "03:00",
    "servers": [
        {
            "name": "",
            "base_url": "",
            "plex_db_path": ""
        }
    ]
}

APP_VERSION = "v9i-recovery-journal"

# Temporary server-path override map. Keep empty unless explicitly needed.
HARDCODED_SERVER_DB_PATHS: Dict[str, str] = {}

# Temporary emergency override while the per-server config bug is being tracked down.
# Any server name listed here will always use the specified Plex DB path.

PLEX_BLACK = "#1f2326"
PLEX_DARK_GREY = "#2d3237"
PLEX_ORANGE = "#e5a00d"
PLEX_TEXT = "#cacbd1"


def default_backup_root() -> str:
    documents = Path.home() / "Documents"
    return str(documents / "PowrPlaylist" / "Backups")


def apply_plex_theme(root: tk.Tk) -> None:
    """Apply a minimal Plex-inspired theme without changing widget behavior."""
    try:
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass

        style.configure("TFrame", background=PLEX_BLACK)
        style.configure("TLabel", background=PLEX_BLACK, foreground=PLEX_TEXT)
        style.configure("TLabelframe", background=PLEX_BLACK, foreground=PLEX_ORANGE)
        style.configure("TLabelframe.Label", background=PLEX_BLACK, foreground=PLEX_ORANGE)
        style.configure("TButton", background=PLEX_DARK_GREY, foreground=PLEX_TEXT)
        style.map("TButton",
                  background=[("active", PLEX_ORANGE)],
                  foreground=[("active", PLEX_BLACK)])
        style.configure("Treeview", background=PLEX_DARK_GREY, fieldbackground=PLEX_DARK_GREY, foreground=PLEX_TEXT)
        style.map("Treeview", background=[("selected", PLEX_ORANGE)])
        root.configure(background=PLEX_BLACK)
    except Exception as exc:
        print(f"Theme failed, continuing without it: {exc}", file=sys.stderr)
FILTER_PRESETS_PATH = Path("filter_presets.json")
OPERATION_LOG_PATH = Path("powr_playlist_activity.log")
OPERATION_JOURNAL_PATH = Path("powr_playlist_operation_journal.json")
DB_BACKUP_SCHEDULE_OPTIONS = ["off", "daily", "weekly", "biweekly"]
DB_BACKUP_SCHEDULE_LABELS = {
    "off": "Off",
    "daily": "Daily",
    "weekly": "Weekly",
    "biweekly": "Every 2 Weeks",
}
DB_BACKUP_SCHEDULE_DAYS = {
    "off": None,
    "daily": 1,
    "weekly": 7,
    "biweekly": 14,
}
DB_BACKUP_CHECK_INTERVAL_MS = 60_000
WINDOWS_SCHEDULED_TASK_NAME = "PowrPlaylist-PlexDBBackup"


def parse_backup_time_string(value: Any) -> Tuple[int, int]:
    raw = str(value or DEFAULT_CONFIG["db_backup_time"]).strip()
    try:
        hour_text, minute_text = raw.split(":", 1)
        hour = int(hour_text)
        minute = int(minute_text)
    except Exception:
        hour, minute = 3, 0
    hour = min(23, max(0, hour))
    minute = min(59, max(0, minute))
    return hour, minute


def normalize_backup_time_string(value: Any) -> str:
    hour, minute = parse_backup_time_string(value)
    return f"{hour:02d}:{minute:02d}"


def get_script_path() -> Path:
    return Path(__file__).resolve()


def build_windows_task_scheduler_command(config: Dict[str, Any]) -> List[str]:
    schedule = str(config.get("db_backup_schedule", "off") or "off").strip().lower()
    if schedule == "off":
        raise PlexError("DB backup schedule is Off. Choose a schedule before creating a Windows task.")

    start_time = normalize_backup_time_string(config.get("db_backup_time", DEFAULT_CONFIG["db_backup_time"]))
    python_exe = Path(sys.executable)
    script_path = get_script_path()

    cmd = [
        "schtasks", "/create", "/f",
        "/tn", WINDOWS_SCHEDULED_TASK_NAME,
        "/tr", f'"{python_exe}" "{script_path}" --scheduled-db-backup',
        "/st", start_time,
    ]

    if schedule == "daily":
        cmd += ["/sc", "daily", "/mo", "1"]
    elif schedule == "weekly":
        cmd += ["/sc", "weekly", "/mo", "1"]
    elif schedule == "biweekly":
        cmd += ["/sc", "weekly", "/mo", "2"]
    else:
        raise PlexError(f"Unsupported DB backup schedule: {schedule}")

    return cmd


def create_or_update_windows_scheduled_backup_task(config: Dict[str, Any]) -> str:
    cfg = normalize_config(config)
    scheduled_servers = [s for s in cfg.get("servers", []) if str(s.get("plex_db_path", "")).strip()]
    if not scheduled_servers:
        raise PlexError("At least one server needs a Plex DB Path before creating a scheduled backup task.")

    cmd = build_windows_task_scheduler_command(cfg)
    completed = subprocess.run(cmd, capture_output=True, text=True, shell=False)
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout or "Unknown error").strip()
        raise PlexError(f"Could not create/update Windows scheduled task: {detail}")
    return (completed.stdout or "Windows scheduled task created.").strip()


def delete_windows_scheduled_backup_task(missing_ok: bool = True) -> str:
    completed = subprocess.run(["schtasks", "/delete", "/f", "/tn", WINDOWS_SCHEDULED_TASK_NAME], capture_output=True, text=True, shell=False)
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout or "Unknown error").strip()
        lowered = detail.lower()
        if missing_ok and ("cannot find the file" in lowered or "cannot find the task" in lowered or "not currently exist" in lowered):
            return "Windows scheduled task was not present."
        raise PlexError(f"Could not delete Windows scheduled task: {detail}")
    return (completed.stdout or "Windows scheduled task deleted.").strip()


def run_scheduled_db_backup_job(config: Optional[Dict[str, Any]] = None) -> int:
    cfg, _missing = load_config_soft() if config is None else (normalize_config(config), False)
    ran_any = False
    errors: List[str] = []
    for server_cfg in cfg.get("servers", []):
        server = PlexServer(server_cfg, cfg)
        if not server.plex_db_path():
            continue
        try:
            server.backup_plex_database(retention=cfg.get("db_backup_retention", 5), scheduled_run=True)
            ran_any = True
        except Exception as exc:
            errors.append(f"{server.name}: {exc}")
    save_config(cfg)
    if errors:
        raise PlexError("; ".join(errors))
    return 0 if ran_any else 0


class PlaceholderEntry(tk.Entry):
    def __init__(self, master=None, placeholder="", placeholder_color="gray50", textvariable=None, show=None, **kwargs):
        self.real_show = show
        self.placeholder = placeholder
        self.placeholder_color = placeholder_color
        self.default_fg = kwargs.pop("fg", None) or kwargs.get("foreground", "black")
        self.var = textvariable if textvariable is not None else tk.StringVar()
        super().__init__(master, textvariable=self.var, show=show or "", **kwargs)
        self._is_placeholder = False
        self.bind("<FocusIn>", self._clear_placeholder)
        self.bind("<FocusOut>", self._show_placeholder_if_needed)
        self._show_placeholder_if_needed()

    def _show_placeholder_if_needed(self, _event=None):
        if not self.var.get():
            self._is_placeholder = True
            self.config(fg=self.placeholder_color)
            self.var.set(self.placeholder)
            if self.real_show:
                self.config(show="")
        else:
            if self.var.get() != self.placeholder:
                self._is_placeholder = False
                self.config(fg=self.default_fg)
                if self.real_show:
                    self.config(show=self.real_show)

    def _clear_placeholder(self, _event=None):
        if self._is_placeholder:
            self._is_placeholder = False
            self.var.set("")
            self.config(fg=self.default_fg)
            if self.real_show:
                self.config(show=self.real_show)

    def get_actual(self):
        return "" if self._is_placeholder else self.var.get()


class PlexError(RuntimeError):
    pass


@dataclass
class PlaylistItem:
    position: int
    title: str
    year: Optional[int]
    rating_key: str
    playlist_item_id: str
    item_type: str = "video"
    genres: List[str] = field(default_factory=list)
    artist: str = ""
    album: str = ""
    studio: str = ""
    content_rating: str = ""
    duration_ms: int = 0
    date_added: int = 0
    last_played: int = 0

    @property
    def display(self) -> str:
        year_text = f" ({self.year})" if self.year else ""
        return f"#{self.position:03d} {self.title}{year_text}"

    @property
    def primary_genre(self) -> str:
        return self.genres[0] if self.genres else ""


def now_stamp() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def safe_name(text: str) -> str:
    return "".join(ch if ch.isalnum() or ch in ("-", "_") else "_" for ch in text).strip("_") or "item"


def normalize_base_url(url: str) -> str:
    value = str(url or "").strip()
    if not value:
        return ""
    value = value.replace("\\", "/")
    if value.startswith("//"):
        value = value.lstrip("/")
        value = "http://" + value
    elif "://" not in value:
        value = "http://" + value
    return value.rstrip("/")


def is_valid_base_url(url: str) -> bool:
    value = normalize_base_url(url)
    return value.startswith("http://") or value.startswith("https://")

def base_url_host(value: str) -> str:
    url = normalize_base_url(value)
    if not url:
        return ""
    try:
        without_scheme = url.split("://", 1)[1]
    except Exception:
        without_scheme = url
    return without_scheme.split("/", 1)[0].split(":", 1)[0].strip().lower()


def unc_path_host(value: str) -> str:
    raw = str(value or "").strip().replace("/", "\\")
    if not raw.startswith("\\"):
        return ""
    parts = [part for part in raw.split("\\") if part]
    return parts[0].strip().lower() if parts else ""


def looks_like_matching_server_path(base_url: str, db_path: str) -> bool:
    host = base_url_host(base_url)
    path_host = unc_path_host(db_path)
    if not host or not path_host:
        return True
    if host == path_host:
        return True
    aliases = {
        "192.168.1.21": {"mediaserver"},
        "mediaserver": {"192.168.1.21"},
        "192.168.1.90": {"media_machine", "mediamachine"},
        "media_machine": {"192.168.1.90", "mediamachine"},
        "mediamachine": {"192.168.1.90", "media_machine"},
    }
    return path_host in aliases.get(host, set()) or host in aliases.get(path_host, set())



def norm_text(value: Any) -> str:
    text = str(value or "").strip().lower()
    return " ".join(ch for ch in text.replace("_", " "))


def normalized_compare(value: str) -> str:
    raw = str(value or "").lower()
    cleaned = []
    for ch in raw:
        cleaned.append(ch if ch.isalnum() else " ")
    return " ".join("".join(cleaned).split())


def playlist_media_type(items: List[PlaylistItem]) -> str:
    if not items:
        return "video"
    counts = defaultdict(int)
    for item in items:
        key = (item.item_type or "video").lower()
        if key in {"track", "audio"}:
            counts["audio"] += 1
        else:
            counts["video"] += 1
    return "audio" if counts["audio"] > counts["video"] else "video"




def parse_backup_timestamp(value: Any) -> Optional[datetime]:
    raw = str(value or "").strip()
    if not raw:
        return None
    try:
        return datetime.fromisoformat(raw)
    except ValueError:
        return None


def backup_schedule_days(schedule: str) -> Optional[int]:
    return DB_BACKUP_SCHEDULE_DAYS.get(str(schedule or "off").strip().lower())


def next_backup_due_at(last_backup_at: Any, schedule: str, backup_time: Any = None, now: Optional[datetime] = None) -> Optional[datetime]:
    days = backup_schedule_days(schedule)
    if not days:
        return None
    check_now = now or datetime.now()
    hour, minute = parse_backup_time_string(backup_time)
    scheduled_today = check_now.replace(hour=hour, minute=minute, second=0, microsecond=0)
    last_dt = parse_backup_timestamp(last_backup_at)
    if last_dt is None:
        return scheduled_today
    due_at = last_dt + timedelta(days=days)
    return due_at.replace(hour=hour, minute=minute, second=0, microsecond=0)


def is_backup_due(last_backup_at: Any, schedule: str, backup_time: Any = None, now: Optional[datetime] = None) -> bool:
    due_at = next_backup_due_at(last_backup_at, schedule, backup_time=backup_time, now=now)
    if due_at is None:
        return False
    return (now or datetime.now()) >= due_at

def normalize_config(config: Dict[str, Any]) -> Dict[str, Any]:
    cfg = deepcopy(config) if isinstance(config, dict) else deepcopy(DEFAULT_CONFIG)

    # Upgrade old shape if needed
    if "servers" not in cfg or not isinstance(cfg["servers"], list) or not cfg["servers"]:
        if cfg.get("server_name") and cfg.get("base_url"):
            cfg["servers"] = [{"name": cfg["server_name"], "base_url": cfg["base_url"]}]
        else:
            cfg["servers"] = deepcopy(DEFAULT_CONFIG["servers"])

    if "plex_token" not in cfg:
        cfg["plex_token"] = cfg.get("plex_token", "")

    if "backup_root" not in cfg or not str(cfg.get("backup_root", "")).strip():
        cfg["backup_root"] = default_backup_root()

    if "timeout_seconds" not in cfg:
        cfg["timeout_seconds"] = DEFAULT_CONFIG["timeout_seconds"]

    if "restore_pause_ms" not in cfg:
        cfg["restore_pause_ms"] = DEFAULT_CONFIG["restore_pause_ms"]

    if "suppress_confirmations" not in cfg:
        cfg["suppress_confirmations"] = DEFAULT_CONFIG["suppress_confirmations"]

    schedule = str(cfg.get("db_backup_schedule", DEFAULT_CONFIG["db_backup_schedule"]) or "off").strip().lower()
    cfg["db_backup_schedule"] = schedule if schedule in DB_BACKUP_SCHEDULE_OPTIONS else DEFAULT_CONFIG["db_backup_schedule"]

    try:
        retention = int(cfg.get("db_backup_retention", DEFAULT_CONFIG["db_backup_retention"]))
    except Exception:
        retention = DEFAULT_CONFIG["db_backup_retention"]
    cfg["db_backup_retention"] = max(1, retention)
    cfg["db_backup_time"] = normalize_backup_time_string(cfg.get("db_backup_time", DEFAULT_CONFIG["db_backup_time"]))

    cleaned = []
    for server in cfg["servers"]:
        if not isinstance(server, dict):
            continue
        server_name = str(server.get("name", "")).strip()
        forced_db_path = HARDCODED_SERVER_DB_PATHS.get(server_name.lower())
        cleaned.append({
            "name": server_name,
            "base_url": normalize_base_url(server.get("base_url", "")),
            "plex_db_path": forced_db_path if forced_db_path is not None else str(server.get("plex_db_path", "")).strip(),
            "last_db_backup_at": str(server.get("last_db_backup_at", "")).strip(),
            "last_scheduled_db_backup_at": str(server.get("last_scheduled_db_backup_at", "")).strip(),
        })
    if not cleaned:
        cleaned = deepcopy(DEFAULT_CONFIG["servers"])

    cfg["servers"] = cleaned
    return cfg


def load_config_soft() -> Tuple[Dict[str, Any], bool]:
    if not CONFIG_PATH.exists():
        return normalize_config(FIRST_RUN_CONFIG), True
    try:
        cfg = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
        return normalize_config(cfg), False
    except Exception:
        return normalize_config(FIRST_RUN_CONFIG), True


def save_config(config: Dict[str, Any]) -> None:
    CONFIG_PATH.write_text(json.dumps(normalize_config(config), indent=2), encoding="utf-8")


class PlexServer:
    def __init__(self, server_config: Dict[str, Any], app_config: Dict[str, Any]) -> None:
        self.server_config = server_config
        self.app_config = app_config
        self.name = str(server_config["name"])
        self.base_url = str(server_config["base_url"]).rstrip("/")
        self.token = str(app_config.get("plex_token", ""))
        self.timeout = int(app_config.get("timeout_seconds", 60))
        self.restore_pause_ms = int(app_config.get("restore_pause_ms", 150))
        self.progress_callback = None

    def _emit_progress(self, message: str) -> None:
        callback = getattr(self, "progress_callback", None)
        if callback:
            try:
                callback(message)
            except Exception:
                pass

    def _request(self, method: str, path: str, expect_json: bool = True, **params: Any):
        if not self.token:
            raise PlexError("No Plex token configured. Open Config and set the global Plex token.")

        params["X-Plex-Token"] = self.token
        url = f"{self.base_url}{path}"
        query = urlencode(params, doseq=True)
        if query:
            url = f"{url}?{query}"

        req = Request(url, method=method.upper(), headers={
            "Accept": "application/json",
            "X-Plex-Accept": "application/json",
        })

        attempts = max(1, min(3, 2 if self.timeout < 90 else 3))
        last_error = None
        for attempt in range(1, attempts + 1):
            try:
                with urlopen(req, timeout=self.timeout) as response:
                    body = response.read().decode("utf-8", errors="replace")
                break
            except HTTPError as exc:
                try:
                    detail = exc.read().decode("utf-8", errors="replace")
                except Exception:
                    detail = str(exc)
                raise PlexError(f"HTTP error {exc.code}: {detail}") from exc
            except URLError as exc:
                last_error = exc
                reason = getattr(exc, "reason", exc)
                is_timeout = isinstance(reason, socket.timeout) or "timed out" in str(reason).lower()
                if attempt < attempts and is_timeout:
                    sleep(1.0 * attempt)
                    continue
                message = f"Connection error after {attempt} attempt(s): {exc}" if is_timeout else f"Connection error: {exc}"
                raise PlexError(message) from exc
        else:
            raise PlexError(f"Connection error: {last_error}")

        if not expect_json:
            return body

        if not body:
            return {}
        try:
            return json.loads(body)
        except json.JSONDecodeError as exc:
            raise PlexError(f"Invalid JSON response from Plex: {body[:300]}") from exc

    def ping(self) -> None:
        self._request("GET", "/")

    def root_info(self) -> Dict[str, Any]:
        data = self._request("GET", "/")
        return data.get("MediaContainer", data)

    def machine_identifier(self) -> str:
        root = self.root_info()
        machine_id = str(root.get("machineIdentifier", "")).strip()
        if not machine_id:
            raise PlexError("Could not determine Plex machineIdentifier.")
        return machine_id

    def _uri_root(self) -> str:
        return f"server://{self.machine_identifier()}/com.plexapp.plugins.library"

    def get_playlists(self) -> List[Dict[str, Any]]:
        data = self._request("GET", "/playlists")
        playlists = data.get("MediaContainer", {}).get("Metadata", [])
        playlists.sort(key=lambda p: str(p.get("title", "")).lower())
        return playlists

    def find_playlist(self, title: str) -> Optional[Dict[str, Any]]:
        for playlist in self.get_playlists():
            if str(playlist.get("title", "")).strip().lower() == title.strip().lower():
                return playlist
        return None

    def get_library_sections(self) -> List[Dict[str, Any]]:
        data = self._request("GET", "/library/sections")
        sections = data.get("MediaContainer", {}).get("Directory", [])
        return [section for section in sections if str(section.get("type", "")).lower() in {"movie", "show", "artist"}]

    def refresh_library_section(self, section_id: str, force: bool = False) -> None:
        params: Dict[str, Any] = {}
        if force:
            params["force"] = 1
        self._request("GET", f"/library/sections/{section_id}/refresh", expect_json=False, **params)

    def refresh_relevant_library_sections(self, playlist_type: str, force: bool = False) -> int:
        desired = {"Movie": "movie", "TV Show": "show", "Music": "artist"}.get(playlist_type or "", "movie")
        refreshed = 0
        for section in self.get_library_sections():
            if str(section.get("type", "")).lower() != desired:
                continue
            key = str(section.get("key", "")).strip()
            if not key:
                continue
            self.refresh_library_section(key, force=force)
            refreshed += 1
        return refreshed

    def get_playlist_items(self, playlist_rating_key: str) -> List[PlaylistItem]:
        data = self._request("GET", f"/playlists/{playlist_rating_key}/items")
        metadata = data.get("MediaContainer", {}).get("Metadata", [])
        items: List[PlaylistItem] = []
        for idx, item in enumerate(metadata, start=1):
            genres = [str(g.get("tag", "")).strip() for g in item.get("Genre", []) if str(g.get("tag", "")).strip()]
            items.append(
                PlaylistItem(
                    position=idx,
                    title=str(item.get("title", "<untitled>")),
                    year=item.get("year"),
                    rating_key=str(item.get("ratingKey", "")),
                    playlist_item_id=str(item.get("playlistItemID", "")),
                    item_type=str(item.get("type", "video") or "video"),
                    genres=genres,
                    artist=str(item.get("originalTitle") or item.get("grandparentTitle") or item.get("parentTitle") or ""),
                    album=str(item.get("parentTitle") or ""),
                    studio=str(item.get("studio") or ""),
                    content_rating=str(item.get("contentRating") or ""),
                    duration_ms=int(item.get("duration") or 0),
                    date_added=int(item.get("addedAt") or 0),
                    last_played=int(item.get("lastViewedAt") or 0),
                )
            )
        return items

    def backup_dir(self) -> Path:
        path = Path(self.app_config["backup_root"])
        path.mkdir(parents=True, exist_ok=True)
        return path

    def export_dir(self) -> Path:
        path = Path(self.app_config["backup_root"]) / "Exports"
        path.mkdir(parents=True, exist_ok=True)
        return path

    def db_backup_dir(self) -> Path:
        path = Path(self.app_config["backup_root"]) / "PlexDatabaseBackups"
        path.mkdir(parents=True, exist_ok=True)
        return path

    def plex_db_path(self) -> str:
        return str(self.server_config.get("plex_db_path", "")).strip()

    def last_db_backup_at(self) -> str:
        return str(self.server_config.get("last_db_backup_at", "")).strip()

    def set_last_db_backup_at(self, value: Optional[datetime] = None) -> str:
        stamp = (value or datetime.now()).isoformat(timespec="seconds")
        self.server_config["last_db_backup_at"] = stamp
        return stamp

    def last_scheduled_db_backup_at(self) -> str:
        return str(self.server_config.get("last_scheduled_db_backup_at", "")).strip()

    def set_last_scheduled_db_backup_at(self, value: Optional[datetime] = None) -> str:
        stamp = (value or datetime.now()).isoformat(timespec="seconds")
        self.server_config["last_scheduled_db_backup_at"] = stamp
        return stamp

    def db_backup_retention(self) -> int:
        try:
            return max(1, int(self.app_config.get("db_backup_retention", 5)))
        except Exception:
            return 5

    def db_backup_schedule(self) -> str:
        schedule = str(self.app_config.get("db_backup_schedule", "off") or "off").strip().lower()
        return schedule if schedule in DB_BACKUP_SCHEDULE_OPTIONS else "off"

    def db_backup_time(self) -> str:
        return normalize_backup_time_string(self.app_config.get("db_backup_time", DEFAULT_CONFIG["db_backup_time"]))

    def is_scheduled_db_backup_due(self, now: Optional[datetime] = None) -> bool:
        if not self.plex_db_path():
            return False
        return is_backup_due(self.last_scheduled_db_backup_at(), self.db_backup_schedule(), backup_time=self.db_backup_time(), now=now)

    def prune_db_backups(self, retention: Optional[int] = None) -> int:
        keep = max(1, retention if retention is not None else self.db_backup_retention())
        prefix = f"{safe_name(self.name)}_plexdb_"
        candidates = sorted(
            [p for p in self.db_backup_dir().glob(f"{prefix}*") if p.name.startswith(prefix)],
            key=lambda p: p.stat().st_mtime,
            reverse=True,
        )
        removed = 0
        for old_path in candidates[keep:]:
            if old_path.is_dir():
                shutil.rmtree(old_path, ignore_errors=True)
            else:
                old_path.unlink(missing_ok=True)
            removed += 1
        return removed

    def backup_plex_database(self, retention: Optional[int] = None, update_last_run: bool = True, scheduled_run: bool = False) -> Path:
        self._emit_progress(f"Backing up Plex DB for {self.name}...")
        db_path = self.plex_db_path()
        if not db_path:
            raise PlexError(f"No Plex DB path configured for server '{self.name}'.")
        source = Path(db_path)
        if not source.exists():
            raise PlexError(f"Plex DB path does not exist for server '{self.name}': {source}")

        destination = self.db_backup_dir() / f"{safe_name(self.name)}_plexdb_{now_stamp()}"
        if source.is_dir():
            shutil.copytree(source, destination)
        else:
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        self._emit_progress(f"Plex DB backup completed for {self.name}: {destination.name}")
        if update_last_run:
            stamp_dt = datetime.now()
            self.set_last_db_backup_at(stamp_dt)
            if scheduled_run:
                self.set_last_scheduled_db_backup_at(stamp_dt)
        self.prune_db_backups(retention=retention)
        return destination

    def export_backup(self, playlist_title: str, items: List[PlaylistItem]) -> Path:
        backup_path = self.backup_dir() / f"{safe_name(self.name)}_{safe_name(playlist_title)}_{now_stamp()}.json"
        latest_path = self.backup_dir() / f"{safe_name(self.name)}_{safe_name(playlist_title)}_latest.json"
        payload = {
            "server_name": self.name,
            "base_url": self.base_url,
            "playlist_title": playlist_title,
            "created_at": now_stamp(),
            "item_count": len(items),
            "items": [asdict(item) for item in items],
        }
        backup_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        shutil.copyfile(backup_path, latest_path)
        return backup_path

    def export_csv(self, playlist_title: str, items: List[PlaylistItem]) -> Path:
        csv_path = self.export_dir() / f"{safe_name(self.name)}_{safe_name(playlist_title)}_{now_stamp()}.csv"
        latest_path = self.export_dir() / f"{safe_name(self.name)}_{safe_name(playlist_title)}_latest.csv"
        with csv_path.open("w", newline="", encoding="utf-8-sig") as handle:
            writer = csv.writer(handle)
            writer.writerow(["position", "title", "year", "rating_key", "playlist_item_id"])
            for item in items:
                writer.writerow([item.position, item.title, item.year if item.year is not None else "", item.rating_key, item.playlist_item_id])
        shutil.copyfile(csv_path, latest_path)
        return csv_path

    def load_csv_order(self, csv_path: Path) -> List[Dict[str, str]]:
        if not csv_path.exists():
            raise PlexError(f"CSV file not found: {csv_path}")

        with csv_path.open("r", newline="", encoding="utf-8-sig") as handle:
            reader = csv.DictReader(handle)
            if reader.fieldnames is None:
                raise PlexError("CSV file has no header row.")
            required = {"position", "title", "rating_key"}
            missing = [name for name in required if name not in reader.fieldnames]
            if missing:
                raise PlexError(f"CSV missing required columns: {', '.join(missing)}")

            rows = []
            for row in reader:
                title = str(row.get("title", "")).strip()
                if not title:
                    continue
                rows.append({
                    "position": str(row.get("position", "")).strip(),
                    "title": title,
                    "year": str(row.get("year", "")).strip(),
                    "rating_key": str(row.get("rating_key", "")).strip(),
                    "playlist_item_id": str(row.get("playlist_item_id", "")).strip(),
                })

        if not rows:
            raise PlexError("CSV file contains no usable rows.")

        try:
            rows.sort(key=lambda row: int(row["position"]))
        except ValueError as exc:
            raise PlexError("CSV contains a non-numeric position value.") from exc

        return rows

    def latest_backup_path(self, playlist_title: str) -> Path:
        latest_path = self.backup_dir() / f"{safe_name(self.name)}_{safe_name(playlist_title)}_latest.json"
        if not latest_path.exists():
            raise PlexError(f"Latest backup not found: {latest_path}")
        return latest_path

    def load_backup(self, backup_path: Path) -> Dict[str, Any]:
        if not backup_path.exists():
            raise PlexError(f"Backup file not found: {backup_path}")
        try:
            return json.loads(backup_path.read_text(encoding="utf-8"))
        except Exception as exc:
            raise PlexError(f"Invalid backup JSON: {backup_path}") from exc

    def delete_playlist(self, playlist_rating_key: str) -> None:
        self._request("DELETE", f"/playlists/{playlist_rating_key}", expect_json=False)

    def create_playlist_from_rating_keys(self, title: str, rating_keys: List[str], media_type: str = "video") -> Dict[str, Any]:
        keys = [str(k).strip() for k in rating_keys if str(k).strip()]
        if not keys:
            raise PlexError("No matched titles were found on the destination server, so no playlist was created.")
        uri = f"{self._uri_root()}/library/metadata/{','.join(keys)}"
        media_type = "audio" if media_type == "audio" else "video"
        data = self._request("POST", "/playlists", type=media_type, title=title, smart=0, uri=uri)
        created = data.get("MediaContainer", {}).get("Metadata", [])
        if created:
            return created[0]
        playlist = self.find_playlist(title)
        if playlist:
            return playlist
        raise PlexError(f"Plex created playlist '{title}' but did not return playlist metadata.")


    def add_items_to_playlist(self, playlist_rating_key: str, rating_keys: List[str]) -> List[PlaylistItem]:
        keys = [str(k).strip() for k in rating_keys if str(k).strip()]
        if not keys:
            raise PlexError("No rating keys were supplied to add to the playlist.")
        uri = f"{self._uri_root()}/library/metadata/{','.join(keys)}"
        self._request("PUT", f"/playlists/{playlist_rating_key}/items", expect_json=False, uri=uri)
        return self.get_playlist_items(playlist_rating_key)

    def search_media(self, query: str) -> List[Dict[str, Any]]:
        data = self._request("GET", "/search", query=query)
        meta = data.get("MediaContainer", {}).get("Metadata", [])
        results = []
        for item in meta:
            item_type = str(item.get("type", "") or "").lower()
            if item_type not in {"movie", "video", "show", "episode", "track", "album", "artist"}:
                continue
            genres = [str(g.get("tag", "")).strip() for g in item.get("Genre", []) if str(g.get("tag", "")).strip()]
            guid_values = []
            for g in item.get("Guid", []):
                gid = str(g.get("id", "")).strip()
                if gid:
                    guid_values.append(gid)
            results.append({
                "title": str(item.get("title", "")),
                "year": item.get("year"),
                "rating_key": str(item.get("ratingKey", "")),
                "type": item_type,
                "guid": guid_values,
                "genres": genres,
                "artist": str(item.get("originalTitle") or item.get("grandparentTitle") or item.get("parentTitle") or ""),
                "album": str(item.get("parentTitle") or ""),
                "duration_ms": int(item.get("duration") or 0),
                "library_section_id": str(item.get("librarySectionID") or ""),
                "library_section_title": str(item.get("librarySectionTitle") or ""),
            })
        return results

    def get_metadata_for_rating_key(self, rating_key: str) -> Dict[str, Any]:
        data = self._request("GET", f"/library/metadata/{rating_key}")
        meta = data.get("MediaContainer", {}).get("Metadata", [])
        if not meta:
            raise PlexError(f"Plex did not return metadata for rating key {rating_key}.")
        return meta[0]

    def delete_library_item(self, rating_key: str) -> None:
        self._request("DELETE", f"/library/metadata/{rating_key}", expect_json=False)

    def remove_items_from_playlist(self, playlist_rating_key: str, playlist_item_ids: List[str]) -> None:
        for playlist_item_id in playlist_item_ids:
            self._request("DELETE", f"/playlists/{playlist_rating_key}/items/{playlist_item_id}", expect_json=False)

    def _candidate_strings(self, item: PlaylistItem) -> List[str]:
        values = [item.title, item.artist, item.album]
        return [normalized_compare(v) for v in values if str(v).strip()]

    def _allowed_media_types(self, item_type: str) -> set[str]:
        item_type = str(item_type or "").strip().lower()
        if item_type in {"movie", "video"}:
            return {"movie", "video"}
        if item_type in {"show", "episode"}:
            return {"show", "episode"}
        if item_type in {"track", "audio", "album", "artist"}:
            return {"track", "audio", "album", "artist"}
        return {item_type} if item_type else set()

    def _allowed_section_types(self, item_type: str) -> set[str]:
        item_type = str(item_type or "").strip().lower()
        if item_type in {"movie", "video"}:
            return {"movie"}
        if item_type in {"show", "episode"}:
            return {"show"}
        if item_type in {"track", "audio", "album", "artist"}:
            return {"artist"}
        return set()

    def _relevant_section_id_set(self, item_type: str) -> set[str]:
        if not hasattr(self, "_relevant_section_cache"):
            self._relevant_section_cache = {}
        key = str(item_type or "").strip().lower()
        if key in self._relevant_section_cache:
            return set(self._relevant_section_cache[key])
        allowed_types = self._allowed_section_types(key)
        section_ids: set[str] = set()
        try:
            for section in self.get_library_sections():
                section_type = str(section.get("type", "") or "").strip().lower()
                if allowed_types and section_type not in allowed_types:
                    continue
                sec_key = str(section.get("key", "") or "").strip()
                if sec_key:
                    section_ids.add(sec_key)
        except Exception:
            section_ids = set()
        self._relevant_section_cache[key] = set(section_ids)
        return section_ids

    def _source_guid_set(self, source_item: PlaylistItem) -> set[str]:
        guid_values: set[str] = set()
        try:
            meta = self.get_metadata_for_rating_key(source_item.rating_key)
            for g in meta.get("Guid", []):
                gid = str(g.get("id", "") or "").strip()
                if gid:
                    guid_values.add(gid)
        except Exception:
            pass
        return guid_values

    def _duration_close(self, source_item: PlaylistItem, result: Dict[str, Any]) -> bool:
        src = int(source_item.duration_ms or 0)
        dst = int(result.get("duration_ms") or 0)
        if not src or not dst:
            return True
        return abs(src - dst) <= 120000

    def _rank_candidate_results(self, source_item: PlaylistItem, results: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        from difflib import SequenceMatcher

        src_norm = normalized_compare(source_item.title)
        src_year = source_item.year
        src_type = str(source_item.item_type or "").strip().lower()
        src_guids = self._source_guid_set(source_item)
        ranked: List[Tuple[Tuple[int, int, int, int, int], Dict[str, Any]]] = []
        for result in results:
            res_norm = normalized_compare(result.get("title", ""))
            ratio = int(SequenceMatcher(None, src_norm, res_norm).ratio() * 1000)
            guid_score = 1 if src_guids and src_guids.intersection(set(result.get("guid", []) or [])) else 0
            exact_title = 1 if src_norm and res_norm == src_norm else 0
            year_score = 1 if src_year is not None and result.get("year") == src_year else 0
            type_score = 1 if str(result.get("type", "") or "").strip().lower() in self._allowed_media_types(src_type) else 0
            duration_score = 1 if self._duration_close(source_item, result) else 0
            ranked.append(((guid_score, exact_title, year_score, type_score + duration_score, ratio), result))
        ranked.sort(key=lambda pair: pair[0], reverse=True)
        return [r for _, r in ranked]

    def candidate_results_for_item(self, source_item: PlaylistItem) -> List[Dict[str, Any]]:
        title = source_item.title
        cache_key = (str(source_item.item_type or "").lower(), str(title or "").strip().lower(), source_item.year or 0)
        if not hasattr(self, "_candidate_cache"):
            self._candidate_cache = {}
        if cache_key in self._candidate_cache:
            return list(self._candidate_cache[cache_key])

        queries = [title]
        if source_item.artist and normalized_compare(source_item.artist) != normalized_compare(title):
            queries.append(source_item.artist)
        if source_item.album and normalized_compare(source_item.album) not in {normalized_compare(title), normalized_compare(source_item.artist)}:
            queries.append(source_item.album)

        all_results: List[Dict[str, Any]] = []
        seen_keys: set[str] = set()
        for query in queries:
            if not str(query).strip():
                continue
            for result in self.search_media(query):
                rk = str(result.get("rating_key", "") or "").strip()
                if not rk or rk in seen_keys:
                    continue
                seen_keys.add(rk)
                all_results.append(result)

        allowed_types = self._allowed_media_types(source_item.item_type)
        relevant_sections = self._relevant_section_id_set(source_item.item_type)
        filtered: List[Dict[str, Any]] = []
        for result in all_results:
            result_type = str(result.get("type", "") or "").strip().lower()
            if allowed_types and result_type not in allowed_types:
                continue
            section_id = str(result.get("library_section_id", "") or "").strip()
            if relevant_sections and section_id and section_id not in relevant_sections:
                continue
            filtered.append(result)

        ranked = self._rank_candidate_results(source_item, filtered)
        self._candidate_cache[cache_key] = list(ranked)
        return ranked

    def match_item_robust(self, source_item: PlaylistItem) -> Tuple[Optional[str], Optional[str], List[Dict[str, Any]], str]:
        candidates = self.candidate_results_for_item(source_item)
        if not candidates:
            return None, "missing", [], "no_candidates"

        src_norm = normalized_compare(source_item.title)
        src_year = source_item.year
        src_guids = self._source_guid_set(source_item)

        guid_matches = [r for r in candidates if src_guids and src_guids.intersection(set(r.get("guid", []) or []))]
        if len(guid_matches) == 1:
            return guid_matches[0]["rating_key"], None, guid_matches, "guid"
        if len(guid_matches) > 1:
            ranked = self._rank_candidate_results(source_item, guid_matches)
            top = ranked[0]
            if len(ranked) == 1 or (str(top.get("title", "")).strip() and normalized_compare(top.get("title", "")) == src_norm and (src_year is None or top.get("year") == src_year)):
                return top["rating_key"], None, ranked, "guid_ranked"
            return None, "ambiguous", ranked[:10], "guid_ambiguous"

        exact_title_year = [r for r in candidates if normalized_compare(r.get("title", "")) == src_norm and (src_year is None or r.get("year") == src_year)]
        if len(exact_title_year) == 1:
            return exact_title_year[0]["rating_key"], None, exact_title_year, "exact_title_year"
        if len(exact_title_year) > 1:
            ranked = self._rank_candidate_results(source_item, exact_title_year)
            top = ranked[0]
            if src_year is not None and len(ranked) >= 2 and (top.get("year") == src_year) and (ranked[1].get("year") != src_year):
                return top["rating_key"], None, ranked, "exact_title_year_ranked"
            return None, "ambiguous", ranked[:10], "exact_title_year_ambiguous"

        exact_title = [r for r in candidates if normalized_compare(r.get("title", "")) == src_norm]
        if len(exact_title) == 1 and (src_year is None or abs(int(exact_title[0].get("year") or 0) - int(src_year or 0)) <= 1):
            return exact_title[0]["rating_key"], None, exact_title, "exact_title"
        if len(exact_title) > 1:
            ranked = self._rank_candidate_results(source_item, exact_title)
            same_year = [r for r in ranked if src_year is not None and r.get("year") == src_year]
            if len(same_year) == 1:
                return same_year[0]["rating_key"], None, ranked, "exact_title_same_year"
            return None, "ambiguous", ranked[:10], "exact_title_ambiguous"

        # Be intentionally conservative for fuzzy matching.
        ranked = self._rank_candidate_results(source_item, candidates)
        if ranked:
            from difflib import SequenceMatcher
            top = ranked[0]
            top_norm = normalized_compare(top.get("title", ""))
            ratio = SequenceMatcher(None, src_norm, top_norm).ratio()
            year_ok = src_year is None or top.get("year") == src_year
            if ratio >= 0.94 and year_ok:
                return top["rating_key"], None, ranked, "strict_fuzzy"
            close = [r for r in ranked if SequenceMatcher(None, src_norm, normalized_compare(r.get("title", ""))).ratio() >= 0.90 and (src_year is None or r.get("year") == src_year)]
            if len(close) == 1:
                return close[0]["rating_key"], None, ranked, "strict_fuzzy_single"
            if close:
                return None, "ambiguous", close[:10], "strict_fuzzy_ambiguous"
        return None, "missing", ranked[:10], "strict_missing"

    def _canonical_identity(self, title: str, year: Optional[int]) -> str:
        norm = normalized_compare(title)
        year_text = str(year) if year is not None else ""
        return f"{norm}|{year_text}"

    def verify_created_playlist(self, playlist_rating_key: str, expected_source_items: List[PlaylistItem]) -> Dict[str, Any]:
        actual_items = self.get_playlist_items(playlist_rating_key)
        actual_identity_counts: Dict[str, int] = defaultdict(int)
        for item in actual_items:
            actual_identity_counts[self._canonical_identity(item.title, item.year)] += 1

        missing_source_items: List[str] = []
        expected_identity_counts: Dict[str, int] = defaultdict(int)
        for item in expected_source_items:
            ident = self._canonical_identity(item.title, item.year)
            expected_identity_counts[ident] += 1
            if actual_identity_counts.get(ident, 0) < expected_identity_counts[ident]:
                missing_source_items.append(item.display)

        duplicate_items: List[str] = []
        for ident, count in actual_identity_counts.items():
            if count > 1:
                duplicate_items.append(f"{ident} x{count}")

        return {
            "actual_items": actual_items,
            "actual_count": len(actual_items),
            "expected_count": len(expected_source_items),
            "missing_source_items": missing_source_items,
            "duplicate_items": duplicate_items,
        }

    def cure_playlist_from_source(
        self,
        playlist_rating_key: str,
        playlist_name: str,
        source_items: List[PlaylistItem],
        verification: Dict[str, Any],
        source_server_name: str = "",
    ) -> Dict[str, Any]:
        expected_identity_counts: Dict[str, int] = defaultdict(int)
        actual_identity_counts: Dict[str, int] = defaultdict(int)
        for item in source_items:
            expected_identity_counts[self._canonical_identity(item.title, item.year)] += 1
        for item in verification.get("actual_items", []):
            actual_identity_counts[self._canonical_identity(item.title, item.year)] += 1

        cured_keys: List[str] = []
        cure_details: List[str] = []
        source_label = str(source_server_name or "source").strip() or "source"
        dest_label = str(self.name or "destination").strip() or "destination"
        total_items = len(source_items)
        for idx, item in enumerate(source_items, start=1):
            ident = self._canonical_identity(item.title, item.year)
            if actual_identity_counts.get(ident, 0) >= expected_identity_counts.get(ident, 0):
                continue
            self._emit_progress(f"Curing item {idx}/{total_items}: {source_label} -> {dest_label} | {item.display}")
            match_key, status, candidates, match_reason = self.match_item_robust(item)
            if match_key:
                cured_keys.append(match_key)
                actual_identity_counts[ident] += 1
                cure_details.append(f"Cured: {item.display} | reason={match_reason} | match_key={match_key}")
                self._emit_progress(f"Cured item {idx}/{total_items}: {source_label} -> {dest_label} | {item.display} | match_key={match_key}")
            else:
                cure_details.append(f"Uncured: {item.display} | status={status or 'missing'} | reason={match_reason}")
                self._emit_progress(f"Uncured item {idx}/{total_items}: {source_label} -> {dest_label} | {item.display} | status={status or 'missing'} | reason={match_reason}")

        if cured_keys:
            self._emit_progress(f"Applying cure pass to '{playlist_name}' with {len(cured_keys)} item(s)")
            self.add_items_to_playlist(playlist_rating_key, cured_keys)

        post_verify = self.verify_created_playlist(playlist_rating_key, source_items)
        post_verify["cured_count"] = len(cured_keys)
        post_verify["cure_details"] = cure_details
        post_verify["still_missing_after_cure"] = list(post_verify.get("missing_source_items", []))
        return post_verify

    def copy_playlist_from_source(
        self,
        source_items: List[PlaylistItem],
        playlist_name: str,
        overwrite_existing: bool,
        source_server_name: str = "",
    ) -> Tuple[int, int, int, List[str], List[str], List[Dict[str, Any]], Dict[str, Any]]:
        existing = self.find_playlist(playlist_name)
        if existing and overwrite_existing:
            self.delete_playlist(str(existing["ratingKey"]))
        elif existing and not overwrite_existing:
            raise PlexError(f"Destination playlist '{playlist_name}' already exists.")

        # Reset per-run caches so we always resolve against the current destination DB state.
        self._candidate_cache = {}
        self._relevant_section_cache = {}

        matched_keys: List[str] = []
        missing: List[str] = []
        ambiguous: List[str] = []
        unresolved: List[Dict[str, Any]] = []

        source_label = str(source_server_name or "source").strip() or "source"
        dest_label = str(self.name or "destination").strip() or "destination"
        total_items = len(source_items)
        for idx, item in enumerate(source_items, start=1):
            self._emit_progress(
                f"Resolving item {idx}/{total_items}: {source_label} -> {dest_label} | {item.display}"
            )
            match_key, status, candidates, match_reason = self.match_item_robust(item)
            if match_key:
                self._emit_progress(
                    f"Resolved item {idx}/{total_items}: {source_label} -> {dest_label} | {item.display} | match_key={match_key}"
                )
                matched_keys.append(match_key)
                continue

            entry = {
                "status": status or "missing",
                "display": item.display,
                "title": item.title,
                "year": item.year,
                "item_type": item.item_type,
                "artist": item.artist,
                "album": item.album,
                "match_reason": match_reason,
                "candidates": candidates[:10] if candidates else [],
            }
            unresolved.append(entry)
            if status == "ambiguous":
                self._emit_progress(
                    f"Ambiguous item {idx}/{total_items}: {source_label} -> {dest_label} | {item.display} | candidates={len(candidates or [])} | reason={match_reason}"
                )
                ambiguous.append(item.display)
            else:
                self._emit_progress(
                    f"Missing item {idx}/{total_items}: {source_label} -> {dest_label} | {item.display} | reason={match_reason}"
                )
                missing.append(item.display)

        verification: Dict[str, Any] = {
            "actual_items": [],
            "actual_count": 0,
            "expected_count": len(source_items),
            "missing_source_items": list(missing),
            "duplicate_items": [],
            "cured_count": 0,
            "cure_details": [],
            "still_missing_after_cure": list(missing),
        }

        if matched_keys:
            self._emit_progress(
                f"Creating destination playlist '{playlist_name}' on {dest_label} from {source_label} with {len(matched_keys)} resolved item(s)"
            )
            created_playlist = self.create_playlist_from_rating_keys(playlist_name, matched_keys, playlist_media_type(source_items))
            playlist_key = str(created_playlist.get("ratingKey", "") or "")
            if playlist_key:
                self._emit_progress(f"Verifying created playlist '{playlist_name}' on {source_label} -> {dest_label}")
                verification = self.verify_created_playlist(playlist_key, source_items)
                missing_after_create = verification.get("missing_source_items", [])
                if missing_after_create:
                    self._emit_progress(f"Verification found {len(missing_after_create)} missing item(s) for '{playlist_name}'; starting cure pass")
                    verification = self.cure_playlist_from_source(playlist_key, playlist_name, source_items, verification, source_server_name=source_server_name)
                    final_missing = verification.get("still_missing_after_cure", [])
                    if final_missing:
                        self._emit_progress(f"Cure pass incomplete for '{playlist_name}': {len(final_missing)} item(s) still missing")
                    else:
                        self._emit_progress(f"Cure pass verified playlist '{playlist_name}' successfully")
                else:
                    self._emit_progress(f"Verification passed for '{playlist_name}' with {verification.get('actual_count', 0)} item(s)")

        return len(matched_keys), len(missing), len(ambiguous), missing, ambiguous, unresolved, verification

    def _find_item_by_playlist_item_id(self, items: List[PlaylistItem], playlist_item_id: str) -> PlaylistItem:
        for item in items:
            if item.playlist_item_id == playlist_item_id:
                return item
        raise PlexError(f"Could not find playlist item id: {playlist_item_id}")

    def _move_local_after(self, items: List[PlaylistItem], playlist_item_id: str, after_playlist_item_id: str) -> List[PlaylistItem]:
        work = list(items)
        idx = next((i for i, item in enumerate(work) if item.playlist_item_id == playlist_item_id), None)
        if idx is None:
            raise PlexError(f"Could not find playlist item id in local order: {playlist_item_id}")
        item = work.pop(idx)
        if after_playlist_item_id == "0":
            work.insert(0, item)
        else:
            after_idx = next((i for i, existing in enumerate(work) if existing.playlist_item_id == after_playlist_item_id), None)
            if after_idx is None:
                raise PlexError(f"Could not find pivot item in local order: {after_playlist_item_id}")
            work.insert(after_idx + 1, item)

        for i, itm in enumerate(work, start=1):
            itm.position = i
        return work

    def apply_move_to_position(self, playlist_title: str, items: List[PlaylistItem], playlist_item_id: str, target_position: int) -> Tuple[List[PlaylistItem], Path]:
        if target_position < 1 or target_position > len(items):
            raise PlexError(f"Target position out of range: {target_position}")
        current = self._find_item_by_playlist_item_id(items, playlist_item_id)
        self._emit_progress(f"Preparing direct move for {current.title} from slot {current.position} to {target_position}")
        backup_path = self.export_backup(playlist_title, items)
        if current.position == target_position:
            return list(items), backup_path

        work = list(items)
        if target_position == 1:
            pivot_after = "0"
        else:
            work_without = [i for i in work if i.playlist_item_id != playlist_item_id]
            pivot_after = work_without[target_position - 2].playlist_item_id

        self._emit_progress(f"Applying direct move to slot {target_position}")
        self._move_playlist_item_api(playlist_item_id, pivot_after)
        work = self._move_local_after(work, playlist_item_id, pivot_after)
        return work, backup_path

    def apply_move_block_relative(
        self,
        playlist_title: str,
        items: List[PlaylistItem],
        source_playlist_item_ids: List[str],
        anchor_playlist_item_id: str,
        where: str,
    ) -> Tuple[List[PlaylistItem], Path]:
        if where not in {"before", "after"}:
            raise PlexError("where must be 'before' or 'after'")
        if not source_playlist_item_ids:
            raise PlexError("No source items were supplied for block move.")
        if anchor_playlist_item_id in set(source_playlist_item_ids):
            raise PlexError("Anchor cannot be inside the selected items.")

        backup_path = self.export_backup(playlist_title, items)
        work = list(items)

        selected_set = set(source_playlist_item_ids)
        selected = [item for item in work if item.playlist_item_id in selected_set]
        remaining = [item for item in work if item.playlist_item_id not in selected_set]

        anchor_index = next((i for i, item in enumerate(remaining) if item.playlist_item_id == anchor_playlist_item_id), None)
        if anchor_index is None:
            raise PlexError("Anchor was not found in the remaining playlist.")

        if where == "before":
            desired_order = remaining[:anchor_index] + selected + remaining[anchor_index:]
        else:
            desired_order = remaining[:anchor_index + 1] + selected + remaining[anchor_index + 1:]

        current_order = list(work)
        total_steps = len(desired_order)
        for target_index, desired_item in enumerate(desired_order, start=1):
            self._emit_progress(f"Block move step {target_index}/{total_steps}: {desired_item.title}")
            current_index = next(i for i, item in enumerate(current_order) if item.playlist_item_id == desired_item.playlist_item_id)
            if current_index + 1 == target_index:
                continue

            if target_index == 1:
                pivot_after = "0"
            else:
                pivot_after = current_order[target_index - 2].playlist_item_id

            self._move_playlist_item_api(desired_item.playlist_item_id, pivot_after)
            current_order = self._move_local_after(current_order, desired_item.playlist_item_id, pivot_after)
            if self.restore_pause_ms > 0:
                sleep(self.restore_pause_ms / 1000.0)

        return current_order, backup_path

    def _move_playlist_item_api(self, playlist_item_id: str, after_playlist_item_id: str) -> None:
        # rating key of playlist is not needed for this endpoint if we address the playlist item directly under current playlist paths
        # but Plex expects /playlists/{playlistRatingKey}/items/{playlistItemID}/move in many docs.
        # We will resolve this by using the current loaded playlist path during callers through cached context.
        raise PlexError("Internal API misuse: _move_playlist_item_api must be monkey-patched with current playlist context.")

    def bind_playlist_context(self, playlist_rating_key: str):
        def mover(playlist_item_id: str, after_playlist_item_id: str):
            self._request("PUT", f"/playlists/{playlist_rating_key}/items/{playlist_item_id}/move", expect_json=False, after=after_playlist_item_id)
        self._move_playlist_item_api = mover

    def apply_order_rows(self, playlist_title: str, playlist_rating_key: str, current_items: List[PlaylistItem], desired_rows: List[Dict[str, str]]) -> Tuple[List[PlaylistItem], int, int, List[str], Path]:
        if not desired_rows:
            raise PlexError("No desired rows supplied for ordering.")
        if len(desired_rows) > len(current_items):
            raise PlexError("Imported CSV contains more rows than the current playlist.")

        backup_path = self.export_backup(f"{playlist_title}_pre_import", current_items)
        work = list(current_items)
        moved_count = 0
        skipped_count = 0
        warnings: List[str] = []

        self.bind_playlist_context(playlist_rating_key)

        total_rows = len(desired_rows)
        for target_index, desired in enumerate(desired_rows, start=1):
            desired_title = str(desired.get("title", "") or "").strip()
            self._emit_progress(f"Restore/import step {target_index}/{total_rows}: {desired_title or "<untitled>"}")
            match = None
            desired_rating_key = str(desired.get("rating_key", "") or "").strip()
            desired_year_raw = str(desired.get("year", "") or "").strip()
            desired_year = int(desired_year_raw) if desired_year_raw.isdigit() else None

            # first match by rating key
            for item in work:
                if item.rating_key and desired_rating_key and item.rating_key == desired_rating_key:
                    match = item
                    break

            # then title first, then title+year when duplicates exist
            if match is None:
                exact = [item for item in work if item.title.strip().lower() == desired_title.lower()]
                if len(exact) == 1:
                    match = exact[0]
                elif len(exact) > 1 and desired_year is not None:
                    exact_year = [item for item in exact if item.year == desired_year]
                    if len(exact_year) == 1:
                        match = exact_year[0]

            if match is None:
                skipped_count += 1
                warnings.append(f"Could not find imported row for slot {target_index}: {desired_title}")
                continue

            if match.position == target_index:
                continue

            if target_index == 1:
                pivot_after = "0"
            else:
                pivot_after = work[target_index - 2].playlist_item_id

            self._move_playlist_item_api(match.playlist_item_id, pivot_after)
            work = self._move_local_after(work, match.playlist_item_id, pivot_after)
            moved_count += 1

            if self.restore_pause_ms > 0:
                sleep(self.restore_pause_ms / 1000.0)

        return work, moved_count, skipped_count, warnings, backup_path

    def restore_from_backup(self, playlist_title: str, playlist_rating_key: str, current_items: List[PlaylistItem], backup_path: Path):
        backup = self.load_backup(backup_path)
        desired_items = backup.get("items", [])
        if not desired_items:
            raise PlexError(f"Backup contains no items: {backup_path}")
        return self.apply_order_rows(playlist_title, playlist_rating_key, current_items, desired_items)


class ConfigDialog(tk.Toplevel):
    def __init__(self, parent, config: Dict[str, Any], require_save: bool = False) -> None:
        super().__init__(parent)
        self.title("Configuration")
        self.geometry("980x760")
        self.minsize(940, 720)
        self.transient(parent)
        self.grab_set()
        self.require_save = require_save
        self.result_config = None
        self.working = normalize_config(config)
        self.is_first_run = require_save
        if self.is_first_run:
            # keep timeout and restore pause defaults, but start all other fields blank
            self.working["plex_token"] = ""
            self.working["backup_root"] = default_backup_root()
            self.working["db_backup_schedule"] = DEFAULT_CONFIG["db_backup_schedule"]
            self.working["db_backup_retention"] = DEFAULT_CONFIG["db_backup_retention"]
            self.working["db_backup_time"] = DEFAULT_CONFIG["db_backup_time"]
            self.working["servers"] = [{"name": "", "base_url": "", "plex_db_path": "", "last_db_backup_at": "", "last_scheduled_db_backup_at": ""}]

        self.plex_token_var = tk.StringVar(value="" if self.require_save and not str(self.working.get("plex_token", "")).strip() else str(self.working.get("plex_token", "")))
        self.backup_root_var = tk.StringVar(value=str(self.working.get("backup_root", "")).strip() or default_backup_root())
        self.timeout_var = tk.StringVar(value=str(self.working.get("timeout_seconds", 60)))
        self.restore_pause_var = tk.StringVar(value=str(self.working.get("restore_pause_ms", 150)))
        self.suppress_confirmations_var = tk.BooleanVar(value=bool(self.working.get("suppress_confirmations", False)))
        self.db_backup_schedule_var = tk.StringVar(value=str(self.working.get("db_backup_schedule", "weekly")))
        self.db_backup_retention_var = tk.StringVar(value=str(self.working.get("db_backup_retention", 5)))
        self.db_backup_time_var = tk.StringVar(value=str(self.working.get("db_backup_time", DEFAULT_CONFIG["db_backup_time"])))

        self.server_name_var = tk.StringVar()
        self.server_url_var = tk.StringVar()
        self.server_db_path_var = tk.StringVar()
        self.active_server_idx: Optional[int] = None
        self._suspend_server_events = False

        self.columnconfigure(1, weight=1)
        self.rowconfigure(0, weight=1)

        self._build_ui()
        self._bind_autosave()
        self._center_on_screen()
        self._refresh_server_list()

        self.protocol("WM_DELETE_WINDOW", self._on_window_close)

    def _bind_autosave(self):
        server_widgets = [self.server_name_entry, self.server_url_entry, self.server_db_path_entry]
        general_widgets = [self.token_entry, self.timeout_entry, self.restore_pause_entry, self.db_backup_time_entry, self.db_backup_retention_entry]
        for widget in server_widgets:
            widget.bind("<FocusOut>", self._autosave_server_editor, add="+")
        for widget in general_widgets:
            widget.bind("<FocusOut>", self._autosave_general_fields, add="+")
        self.db_backup_schedule_combo.bind("<<ComboboxSelected>>", self._autosave_general_fields, add="+")

    def _center_on_screen(self):
        self.update_idletasks()
        width = max(self.winfo_width(), 980)
        height = max(self.winfo_height(), 760)
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        x = max(0, (screen_w - width) // 2)
        y = max(0, (screen_h - height) // 2)
        self.geometry(f"{width}x{height}+{x}+{y}")

    def _build_ui(self):
        left = ttk.LabelFrame(self, text="Servers", padding=10)
        left.grid(row=0, column=0, sticky="nsw", padx=(10, 6), pady=10)
        left.rowconfigure(1, weight=1)

        self.server_listbox = tk.Listbox(left, height=14, exportselection=False)
        self.server_listbox.grid(row=1, column=0, sticky="nsw")
        self.server_listbox.bind("<<ListboxSelect>>", self._on_server_selected)

        ttk.Button(left, text="Add Server", command=self._add_server).grid(row=2, column=0, sticky="ew", pady=(8, 2))
        ttk.Button(left, text="Remove Server", command=self._remove_server).grid(row=3, column=0, sticky="ew", pady=2)

        right = ttk.Frame(self, padding=(6, 10, 10, 10))
        right.grid(row=0, column=1, sticky="nsew")
        right.columnconfigure(1, weight=1)

        ttk.Label(right, text="Server Name:").grid(row=0, column=0, sticky="w", pady=4)
        self.server_name_entry = PlaceholderEntry(right, textvariable=self.server_name_var, placeholder="Example: MediaServer")
        self.server_name_entry.grid(row=0, column=1, sticky="ew", pady=4)

        ttk.Label(right, text="Base URL:").grid(row=1, column=0, sticky="w", pady=4)
        self.server_url_entry = PlaceholderEntry(right, textvariable=self.server_url_var, placeholder="Example: http://192.168.1.21:32400")
        self.server_url_entry.grid(row=1, column=1, sticky="ew", pady=4)
        self.server_url_entry.bind("<FocusOut>", self._normalize_server_url_field, add="+")

        ttk.Label(right, text="Plex DB Path:").grid(row=2, column=0, sticky="w", pady=4)
        db_wrap = ttk.Frame(right)
        db_wrap.grid(row=2, column=1, sticky="ew", pady=4)
        db_wrap.columnconfigure(0, weight=1)
        self.server_db_path_entry = PlaceholderEntry(db_wrap, textvariable=self.server_db_path_var, placeholder=r"Choose the Databases folder (contains com.plexapp.plugins.library.db)")
        self.server_db_path_entry.grid(row=0, column=0, sticky="ew")
        ttk.Button(db_wrap, text="Browse", command=self._browse_db_path).grid(row=0, column=1, padx=(6, 0))

        general = ttk.LabelFrame(right, text="General", padding=10)
        general.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(8, 0))
        general.columnconfigure(1, weight=1)

        ttk.Label(general, text="Plex Token:").grid(row=0, column=0, sticky="w", pady=4)
        self.token_entry = PlaceholderEntry(general, textvariable=self.plex_token_var, placeholder="Paste your Plex token here", show="*")
        self.token_entry.grid(row=0, column=1, sticky="ew", pady=4)

        ttk.Label(general, text="Backup Location:").grid(row=1, column=0, sticky="w", pady=4)
        backup_loc_wrap = ttk.Frame(general)
        backup_loc_wrap.grid(row=1, column=1, sticky="ew", pady=4)
        backup_loc_wrap.columnconfigure(0, weight=1)
        self.backup_root_display = ttk.Entry(backup_loc_wrap, textvariable=self.backup_root_var, state="readonly")
        self.backup_root_display.grid(row=0, column=0, sticky="ew")
        ttk.Button(backup_loc_wrap, text="Change Backup Location...", command=self._change_backup_location).grid(row=0, column=1, padx=(6, 0))
        ttk.Button(backup_loc_wrap, text="Reset to Default", command=self._reset_backup_location_default).grid(row=0, column=2, padx=(6, 0))

        ttk.Label(general, text="Timeout Seconds:").grid(row=2, column=0, sticky="w", pady=4)
        self.timeout_entry = ttk.Entry(general, textvariable=self.timeout_var)
        self.timeout_entry.grid(row=2, column=1, sticky="ew", pady=4)

        ttk.Label(general, text="Restore Pause ms:").grid(row=3, column=0, sticky="w", pady=4)
        self.restore_pause_entry = ttk.Entry(general, textvariable=self.restore_pause_var)
        self.restore_pause_entry.grid(row=3, column=1, sticky="ew", pady=4)

        ttk.Checkbutton(
            general,
            text="Suppress confirmations on startup",
            variable=self.suppress_confirmations_var
        ).grid(row=4, column=0, columnspan=2, sticky="w", pady=(8, 0))

        backup_box = ttk.LabelFrame(right, text="Plex Database Backup", padding=10)
        backup_box.grid(row=5, column=0, columnspan=2, sticky="ew", pady=(8, 0))
        backup_box.columnconfigure(1, weight=1)

        ttk.Label(backup_box, text="Backup Schedule:").grid(row=0, column=0, sticky="w", pady=4)
        self.db_backup_schedule_combo = ttk.Combobox(
            backup_box,
            textvariable=self.db_backup_schedule_var,
            state="readonly",
            values=DB_BACKUP_SCHEDULE_OPTIONS,
        )
        self.db_backup_schedule_combo.grid(row=0, column=1, sticky="ew", pady=4)

        ttk.Label(backup_box, text="Backup Time (24h HH:MM):").grid(row=1, column=0, sticky="w", pady=4)
        self.db_backup_time_entry = ttk.Entry(backup_box, textvariable=self.db_backup_time_var)
        self.db_backup_time_entry.grid(row=1, column=1, sticky="ew", pady=4)

        ttk.Label(backup_box, text="Backups To Keep:").grid(row=2, column=0, sticky="w", pady=4)
        self.db_backup_retention_entry = ttk.Entry(backup_box, textvariable=self.db_backup_retention_var)
        self.db_backup_retention_entry.grid(row=2, column=1, sticky="ew", pady=4)

        backup_btn_row = ttk.Frame(backup_box)
        backup_btn_row.grid(row=3, column=0, columnspan=2, sticky="e", pady=(8, 0))
        ttk.Label(backup_btn_row, text="Scheduled backup task updates automatically when this window closes.").grid(row=0, column=0, sticky="w", padx=(0, 12))
        ttk.Button(backup_btn_row, text="Backup Plex DB Now", command=self._backup_selected_db_now).grid(row=0, column=1)

        help_box = ttk.LabelFrame(right, text="Field Help", padding=10)
        help_box.grid(row=6, column=0, columnspan=2, sticky="nsew", pady=(8, 0))
        help_box.columnconfigure(0, weight=1)
        help_box.rowconfigure(0, weight=1)

        self.help_text = tk.Text(help_box, wrap="word", height=5, relief="flat", borderwidth=0)
        self.help_text.grid(row=0, column=0, sticky="nsew")
        self.help_text.configure(state="disabled")

        help_scroll = ttk.Scrollbar(help_box, orient="vertical", command=self.help_text.yview)
        help_scroll.grid(row=0, column=1, sticky="ns")
        self.help_text.configure(yscrollcommand=help_scroll.set)

        bottom = ttk.Frame(right)
        bottom.grid(row=7, column=0, columnspan=2, sticky="ew", pady=(14, 0))
        bottom.columnconfigure(0, weight=1)

        ttk.Button(bottom, text="Reset to Defaults", command=self._reset_defaults).grid(row=0, column=0, sticky="w")
        if self.require_save:
            ttk.Button(bottom, text="Exit App", command=self._exit_app_requested).grid(row=0, column=1, sticky="e", padx=(6, 6))
            ttk.Button(bottom, text="Continue", command=self._save).grid(row=0, column=2, sticky="e")
        else:
            ttk.Button(bottom, text="Close", command=self._cancel).grid(row=0, column=1, sticky="e", padx=6)


        self._register_help_widget(self.server_name_entry, "Server Name\nName this Plex server entry so you can tell it apart from your other servers.\nExample: MediaServer")
        self._register_help_widget(self.server_url_entry, "Base URL\nEnter the Plex server address and port.\nExample: http://192.168.1.21:32400")
        self._register_help_widget(self.server_db_path_entry, "Plex DB Path\nChoose the Plex Databases FOLDER, not an individual file.\nPowr Playlist will back up the full Databases folder.\nTypical file inside that folder: com.plexapp.plugins.library.db\nLocal example: C:\\Users\\username\\AppData\\Local\\Plex Media Server\\Plug-in Support\\Databases\nNetwork example: \\\\server\\Users\\username\\AppData\\Local\\Plex Media Server\\Plug-in Support\\Databases")
        self._register_help_widget(self.token_entry, "Plex Token\nEnter your Plex authentication token used to connect to the server.\nTo find it, see Plex's guide here:\nhttps://support.plex.tv/articles/204059436-finding-an-authentication-token-x-plex-token/\nThis field is required.")
        self._register_help_widget(self.backup_root_display, "Backup Location\nPowr Playlist stores playlist backups, exports, and Plex database backups here.\nUse Change Backup Location to choose a local folder, mapped drive, or network path.")
        self._register_help_widget(self.timeout_entry, "Timeout Seconds\nHow long the app should wait for a Plex server response before treating the request as failed.")
        self._register_help_widget(self.restore_pause_entry, "Restore Pause ms\nPause in milliseconds between move operations during slower restore and reorder workflows.")
        self._register_help_widget(self.db_backup_schedule_combo, "Backup Schedule\nChoose how often the Plex database backup task should run.\nThe app does not need to remain open for scheduled backups.")
        self._register_help_widget(self.db_backup_time_entry, "Backup Time\nChoose the time of day for the scheduled Plex database backup task.\nUse 24-hour format like 02:30 or 21:15.")
        self._register_help_widget(self.db_backup_retention_entry, "Backups To Keep\nChoose how many older Plex database backups to retain before the app removes the oldest ones.")
        self._register_help_widget(self.server_listbox, "Servers\nSelect which saved server entry you want to view or edit.")
        self._set_help_text("Select a field to see help here.")


    def _autosave_server_editor(self, _event=None):
        self._save_editor_to_current_server()

    def _autosave_general_fields(self, _event=None):
        self.working["plex_token"] = self.token_entry.get_actual().strip()
        self.working["backup_root"] = self.backup_root_var.get().strip() or default_backup_root()
        self.working["timeout_seconds"] = self.timeout_var.get().strip() or str(self.working.get("timeout_seconds", 60))
        self.working["restore_pause_ms"] = self.restore_pause_var.get().strip() or str(self.working.get("restore_pause_ms", 150))
        self.working["db_backup_schedule"] = self.db_backup_schedule_var.get().strip() or DEFAULT_CONFIG["db_backup_schedule"]
        self.working["db_backup_retention"] = self.db_backup_retention_var.get().strip() or str(DEFAULT_CONFIG["db_backup_retention"])
        self.working["db_backup_time"] = self.db_backup_time_var.get().strip() or DEFAULT_CONFIG["db_backup_time"]
        self.working["suppress_confirmations"] = bool(self.suppress_confirmations_var.get())

    def _register_help_widget(self, widget, help_text: str):
        widget.bind("<FocusIn>", lambda _event, txt=help_text: self._set_help_text(txt), add="+")

    def _set_help_text(self, help_text: str):
        if not hasattr(self, "help_text"):
            return
        self.help_text.configure(state="normal")
        self.help_text.delete("1.0", tk.END)
        self.help_text.insert("1.0", help_text.strip())
        self.help_text.configure(state="disabled")

    def _cancel_required(self):
        self._save()

    def _cancel(self):
        self._save()

    def _on_window_close(self):
        if self.require_save:
            self._exit_app_requested()
        else:
            self._cancel()

    def _exit_app_requested(self):
        if not self.require_save:
            self.destroy()
            return
        should_exit = messagebox.askyesno(
            "Exit Powr Playlist?",
            "Initial setup is incomplete. If you exit now, Powr Playlist will close.\n\nDo you want to exit the app?",
            parent=self,
        )
        if should_exit:
            self.result_config = None
            self.destroy()

    def _selected_index(self):
        sel = self.server_listbox.curselection()
        return int(sel[0]) if sel else None

    def _refresh_server_list(self, preserve_idx: Optional[int] = None):
        self._suspend_server_events = True
        try:
            self.server_listbox.delete(0, tk.END)
            for server in self.working["servers"]:
                self.server_listbox.insert(tk.END, server.get("name") or "<unnamed>")
            if not self.working["servers"]:
                self.active_server_idx = None
                self._load_server_into_editor(None)
                return
            idx = preserve_idx if preserve_idx is not None else self.active_server_idx
            if idx is None or idx < 0 or idx >= len(self.working["servers"]):
                idx = 0
            self.server_listbox.selection_clear(0, tk.END)
            self.server_listbox.selection_set(idx)
            self.server_listbox.activate(idx)
            self.active_server_idx = idx
        finally:
            self._suspend_server_events = False
        self._load_server_into_editor(self.active_server_idx)

    def _save_editor_to_current_server(self) -> bool:
        idx = self.active_server_idx
        if idx is None or idx < 0 or idx >= len(self.working["servers"]):
            return True
        name = self.server_name_entry.get_actual().strip()
        url = normalize_base_url(self.server_url_entry.get_actual().strip())
        db_path = self.server_db_path_entry.get_actual().strip()
        self.working["servers"][idx]["name"] = name
        self.working["servers"][idx]["base_url"] = url
        self.working["servers"][idx]["plex_db_path"] = db_path
        return True

    def _load_server_into_editor(self, idx: Optional[int]):
        if idx is None or idx < 0 or idx >= len(self.working["servers"]):
            self.server_name_var.set("")
            self.server_url_var.set("")
            self.server_db_path_var.set("")
            self.server_name_entry._show_placeholder_if_needed()
            self.server_url_entry._show_placeholder_if_needed()
            self.server_db_path_entry._show_placeholder_if_needed()
            return
        server = self.working["servers"][idx]
        self.server_name_var.set(server.get("name", ""))
        self.server_url_var.set(server.get("base_url", ""))
        self.server_db_path_var.set(server.get("plex_db_path", ""))
        self.server_name_entry._show_placeholder_if_needed()
        self.server_url_entry._show_placeholder_if_needed()
        self.server_db_path_entry._show_placeholder_if_needed()

    def _on_server_selected(self, _event=None):
        if self._suspend_server_events:
            return
        sel = self.server_listbox.curselection()
        if not sel:
            return
        new_idx = int(sel[0])
        if new_idx == self.active_server_idx:
            return
        self._save_editor_to_current_server()
        self.active_server_idx = new_idx
        self._load_server_into_editor(new_idx)

    def _normalize_server_url_field(self, _event=None):
        value = self.server_url_entry.get_actual().strip()
        if not value:
            self.server_url_entry._show_placeholder_if_needed()
            return
        normalized = normalize_base_url(value)
        self.server_url_var.set(normalized)
        self.server_url_entry._show_placeholder_if_needed()

    def _browse_db_path(self):
        start_dir = self.server_db_path_var.get().strip() or str(Path.home())
        if start_dir and not Path(start_dir).exists():
            start_dir = str(Path(start_dir).parent)
        path = filedialog.askdirectory(title="Select Plex Databases folder", initialdir=start_dir, mustexist=True)
        if path:
            self.server_db_path_var.set(path)
            self.server_db_path_entry._show_placeholder_if_needed()

    def _change_backup_location(self):
        current = self.backup_root_var.get().strip() or default_backup_root()
        start_dir = current if Path(current).exists() else str(Path(current).parent)
        path = filedialog.askdirectory(title="Choose Backup Location", initialdir=start_dir, mustexist=False)
        if not path:
            return
        chosen = Path(path)
        if not chosen.exists():
            if not messagebox.askyesno("Create Folder", f"This folder does not exist yet. Create it?\n\n{chosen}", parent=self):
                return
            try:
                chosen.mkdir(parents=True, exist_ok=True)
            except Exception as exc:
                messagebox.showerror("Backup Location", f"Could not create folder:\n{chosen}\n\n{exc}", parent=self)
                return
        self.backup_root_var.set(str(chosen))
        self._autosave_general_fields()

    def _reset_backup_location_default(self):
        self.backup_root_var.set(default_backup_root())
        self._autosave_general_fields()

    def _backup_selected_db_now(self):
        idx = self.active_server_idx
        if idx is None:
            return
        self._save_editor_to_current_server()
        self._autosave_general_fields()
        server_cfg = self.working["servers"][idx]
        try:
            server = PlexServer(server_cfg, {
                "plex_token": self.token_entry.get_actual().strip(),
                "backup_root": self.backup_root_var.get().strip() or self.working.get("backup_root", "") or default_backup_root(),
                "timeout_seconds": int(self.timeout_var.get().strip() or 60),
                "restore_pause_ms": int(self.restore_pause_var.get().strip() or 150),
                "db_backup_schedule": self.db_backup_schedule_var.get().strip() or DEFAULT_CONFIG["db_backup_schedule"],
                "db_backup_retention": int(self.db_backup_retention_var.get().strip() or DEFAULT_CONFIG["db_backup_retention"]),
                "db_backup_time": normalize_backup_time_string(self.db_backup_time_var.get().strip() or DEFAULT_CONFIG["db_backup_time"]),
            })
            path = server.backup_plex_database(retention=int(self.db_backup_retention_var.get().strip() or DEFAULT_CONFIG["db_backup_retention"]))
            messagebox.showinfo("Plex DB Backup", f"Plex DB backup created:\n{path}", parent=self)
        except Exception as exc:
            messagebox.showerror("Plex DB Backup Failed", str(exc), parent=self)

    def _apply_server_changes(self):
        idx = self.active_server_idx
        if idx is None:
            return
        self._save_editor_to_current_server()
        self._refresh_server_list(preserve_idx=idx)

    def _add_server(self):
        if not self._save_editor_to_current_server():
            return
        new_name = f"Server{len(self.working['servers']) + 1}"
        self.working["servers"].append({"name": new_name, "base_url": "http://127.0.0.1:32400", "plex_db_path": "", "last_db_backup_at": "", "last_scheduled_db_backup_at": ""})
        idx = len(self.working["servers"]) - 1
        self.active_server_idx = idx
        self._refresh_server_list(preserve_idx=idx)

    def _remove_server(self):
        idx = self.active_server_idx
        if idx is None:
            return
        if len(self.working["servers"]) <= 1:
            messagebox.showwarning("Cannot Remove", "At least one server is required.", parent=self)
            return
        self.working["servers"].pop(idx)
        new_idx = min(idx, len(self.working["servers"]) - 1)
        self.active_server_idx = new_idx if self.working["servers"] else None
        self._refresh_server_list(preserve_idx=self.active_server_idx)

    def _reset_defaults(self):
        self.working = normalize_config(FIRST_RUN_CONFIG)
        self.plex_token_var.set("")
        self.backup_root_var.set(default_backup_root())
        self.timeout_var.set("60")
        self.restore_pause_var.set("150")
        self.db_backup_schedule_var.set(DEFAULT_CONFIG["db_backup_schedule"])
        self.db_backup_retention_var.set(str(DEFAULT_CONFIG["db_backup_retention"]))
        self.db_backup_time_var.set(DEFAULT_CONFIG["db_backup_time"])
        self.suppress_confirmations_var.set(False)
        self.token_entry._show_placeholder_if_needed()
        self.active_server_idx = 0 if self.working["servers"] else None
        self._refresh_server_list(preserve_idx=self.active_server_idx)

    def _create_or_update_backup_task(self):
        if self.active_server_idx is not None:
            self._apply_server_changes()
        try:
            preview_config = {
                "plex_token": self.token_entry.get_actual().strip(),
                "backup_root": self.backup_root_var.get().strip() or default_backup_root(),
                "timeout_seconds": int(self.timeout_var.get().strip() or 60),
                "restore_pause_ms": int(self.restore_pause_var.get().strip() or 150),
                "db_backup_schedule": str(self.db_backup_schedule_var.get().strip() or DEFAULT_CONFIG["db_backup_schedule"]).lower(),
                "db_backup_retention": max(1, int(self.db_backup_retention_var.get().strip() or DEFAULT_CONFIG["db_backup_retention"])),
                "db_backup_time": normalize_backup_time_string(self.db_backup_time_var.get().strip() or DEFAULT_CONFIG["db_backup_time"]),
                "suppress_confirmations": bool(self.suppress_confirmations_var.get()),
                "servers": deepcopy(self.working["servers"]),
            }
            result = create_or_update_windows_scheduled_backup_task(preview_config)
            messagebox.showinfo("Windows Task Scheduler", result, parent=self)
        except Exception as exc:
            messagebox.showerror("Windows Task Scheduler", str(exc), parent=self)

    def _delete_backup_task(self):
        try:
            result = delete_windows_scheduled_backup_task(missing_ok=True)
            messagebox.showinfo("Windows Task Scheduler", result, parent=self)
        except Exception as exc:
            messagebox.showerror("Windows Task Scheduler", str(exc), parent=self)

    def _validate_config(self) -> List[str]:
        errors: List[str] = []
        if not self.working["servers"]:
            errors.append("Add at least one server entry.")
        plex_token = self.token_entry.get_actual().strip()
        if not plex_token:
            errors.append("Global Plex Token is required. Example: paste your X-Plex-Token here.")
        backup_root = self.backup_root_var.get().strip() or default_backup_root()
        if not backup_root:
            errors.append(f"Backup Location is required. Example: {default_backup_root()}")
        try:
            int(self.timeout_var.get().strip())
            int(self.restore_pause_var.get().strip())
            int(self.db_backup_retention_var.get().strip())
        except ValueError:
            errors.append("Timeout Seconds, Restore Pause ms, and Backups To Keep must all be whole numbers.")
        db_backup_schedule = str(self.db_backup_schedule_var.get().strip() or DEFAULT_CONFIG["db_backup_schedule"]).lower()
        if db_backup_schedule not in DB_BACKUP_SCHEDULE_OPTIONS:
            errors.append("Choose a valid Backup Schedule.")
        names = [s.get("name", "").strip() for s in self.working["servers"]]
        if any(not name for name in names):
            errors.append("Every server needs a Server Name. Example: MediaServer")
        non_empty_names = [name for name in names if name]
        if len(set(name.lower() for name in non_empty_names)) != len(non_empty_names):
            errors.append("Server names must be unique.")
        for server in self.working["servers"]:
            server_name = server.get("name", "<unnamed>").strip() or "<unnamed>"
            base_url = normalize_base_url(server.get("base_url", ""))
            server["base_url"] = base_url
            if not base_url:
                errors.append(f"Server '{server_name}' needs a Base URL. Example: http://192.168.1.21:32400")
            elif not is_valid_base_url(base_url):
                errors.append(f"Server '{server_name}' has an invalid Base URL. Example: http://192.168.1.21:32400")
        return errors

    def _save(self):
        if self.active_server_idx is not None:
            self._save_editor_to_current_server()
        self._autosave_general_fields()

        errors = self._validate_config()
        if errors:
            messagebox.showwarning("Configuration Incomplete", "Please fix the following before leaving Configuration:\n\n- " + "\n- ".join(errors), parent=self)
            return

        plex_token = self.token_entry.get_actual().strip()
        backup_root = self.backup_root_var.get().strip() or default_backup_root()
        timeout_seconds = int(self.timeout_var.get().strip())
        restore_pause_ms = int(self.restore_pause_var.get().strip())
        db_backup_retention = max(1, int(self.db_backup_retention_var.get().strip()))
        db_backup_time = normalize_backup_time_string(self.db_backup_time_var.get().strip() or DEFAULT_CONFIG["db_backup_time"])
        db_backup_schedule = str(self.db_backup_schedule_var.get().strip() or DEFAULT_CONFIG["db_backup_schedule"]).lower()

        self.result_config = {
            "plex_token": plex_token,
            "backup_root": backup_root,
            "timeout_seconds": timeout_seconds,
            "restore_pause_ms": restore_pause_ms,
            "db_backup_schedule": db_backup_schedule,
            "db_backup_retention": db_backup_retention,
            "db_backup_time": db_backup_time,
            "suppress_confirmations": bool(self.suppress_confirmations_var.get()),
            "servers": deepcopy(self.working["servers"]),
        }
        try:
            if db_backup_schedule == "off":
                delete_windows_scheduled_backup_task(missing_ok=True)
            else:
                create_or_update_windows_scheduled_backup_task(self.result_config)
        except Exception as exc:
            if not messagebox.askyesno("Windows Task Scheduler", f"Could not update the Windows scheduled backup task.\n\n{exc}\n\nClose configuration anyway?", parent=self):
                return
        self.destroy()


class CopyPlaylistDialog(tk.Toplevel):
    def __init__(self, parent, current_server_name: str, current_playlist_name: str, server_names: List[str]) -> None:
        super().__init__(parent)
        self.title("Copy Playlist To Server")
        self.geometry("720x500")
        self.minsize(680, 460)
        self.transient(parent)
        self.grab_set()
        self.result = None

        self.source_server_var = tk.StringVar(value=current_server_name)
        self.source_playlist_var = tk.StringVar(value=current_playlist_name)
        self.dest_server_var = tk.StringVar(value=server_names[0] if server_names else "")
        if self.dest_server_var.get() == current_server_name and len(server_names) > 1:
            self.dest_server_var.set(server_names[1])
        self.playlist_name_var = tk.StringVar(value=current_playlist_name)
        self.refresh_mode_var = tk.StringVar(value="none")

        frm = ttk.Frame(self, padding=12)
        frm.pack(fill="both", expand=True)
        frm.columnconfigure(1, weight=1)
        frm.rowconfigure(6, weight=1)

        ttk.Label(frm, text="Source Server:").grid(row=0, column=0, sticky="w", pady=4)
        source_server_entry = ttk.Entry(frm, textvariable=self.source_server_var, state="readonly")
        source_server_entry.grid(row=0, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="Source Playlist:").grid(row=1, column=0, sticky="w", pady=4)
        source_playlist_entry = ttk.Entry(frm, textvariable=self.source_playlist_var, state="readonly")
        source_playlist_entry.grid(row=1, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="Destination Server:").grid(row=2, column=0, sticky="w", pady=4)
        dest_server_combo = ttk.Combobox(frm, textvariable=self.dest_server_var, values=server_names, state="readonly")
        dest_server_combo.grid(row=2, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="New Playlist Name:").grid(row=3, column=0, sticky="w", pady=4)
        playlist_name_entry = ttk.Entry(frm, textvariable=self.playlist_name_var)
        playlist_name_entry.grid(row=3, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="Pre-Transfer Refresh:").grid(row=4, column=0, sticky="w", pady=4)
        refresh_combo = ttk.Combobox(
            frm,
            textvariable=self.refresh_mode_var,
            state="readonly",
            values=[
                "none",
                "scan_both",
                "deep_refresh_both",
            ],
        )
        refresh_combo.grid(row=4, column=1, sticky="ew", pady=4)

        note = ttk.Label(
            frm,
            text=(
                "If the destination playlist already exists, the app will ask whether to overwrite it. "
                "Plex library refresh requests run asynchronously; a regular scan is lighter, while deep refresh forces metadata refresh."
            ),
            wraplength=660,
            justify="left",
        )
        note.grid(row=5, column=0, columnspan=2, sticky="w", pady=(10, 8))

        help_box = ttk.LabelFrame(frm, text="Field Help", padding=10)
        help_box.grid(row=6, column=0, columnspan=2, sticky="nsew", pady=(4, 0))
        help_box.columnconfigure(0, weight=1)
        help_box.rowconfigure(0, weight=1)

        self.help_text = tk.Text(help_box, wrap="word", height=6, relief="flat", borderwidth=0)
        self.help_text.grid(row=0, column=0, sticky="nsew")
        self.help_text.configure(state="disabled")

        help_scroll = ttk.Scrollbar(help_box, orient="vertical", command=self.help_text.yview)
        help_scroll.grid(row=0, column=1, sticky="ns")
        self.help_text.configure(yscrollcommand=help_scroll.set)

        btns = ttk.Frame(frm)
        btns.grid(row=7, column=0, columnspan=2, sticky="e", pady=(12, 0))
        ttk.Button(btns, text="Cancel", command=self.destroy).grid(row=0, column=0, padx=6)
        ttk.Button(btns, text="Copy", command=self._copy).grid(row=0, column=1)

        self._register_help_widget(
            source_server_entry,
            "Source Server\n\nShows the Plex server that currently holds the playlist you are copying from.",
        )
        self._register_help_widget(
            source_playlist_entry,
            "Source Playlist\n\nShows the playlist on the source server that will be copied.",
        )
        self._register_help_widget(
            dest_server_combo,
            "Destination Server\n\nChoose the Plex server that should receive the copied playlist items.",
        )
        self._register_help_widget(
            playlist_name_entry,
            "New Playlist Name\n\nEnter the name that should be used for the destination playlist on the receiving server. If a playlist with this name already exists, the app will ask whether to overwrite it.",
        )
        self._register_help_widget(
            refresh_combo,
            "Pre-Transfer Refresh\n\nChoose whether the app should request a Plex library refresh on both the source and destination servers before matching titles.\n\nnone: do not request a refresh\nscan_both: request a lighter library scan on both servers\ndeep_refresh_both: request a heavier metadata refresh on both servers\n\nPlex handles refresh requests asynchronously.",
        )
        self._set_help_text("Select a field to see help here.")

    def _register_help_widget(self, widget, help_text: str):
        widget.bind("<FocusIn>", lambda _event, txt=help_text: self._set_help_text(txt), add="+")

    def _set_help_text(self, help_text: str):
        self.help_text.configure(state="normal")
        self.help_text.delete("1.0", tk.END)
        self.help_text.insert("1.0", help_text.strip())
        self.help_text.configure(state="disabled")

    def _copy(self):
        dest_server = self.dest_server_var.get().strip()
        playlist_name = self.playlist_name_var.get().strip()
        if not dest_server:
            messagebox.showwarning("Missing Destination", "Choose a destination server.", parent=self)
            return
        if not playlist_name:
            messagebox.showwarning("Missing Name", "Enter a playlist name.", parent=self)
            return
        self.result = {
            "dest_server": dest_server,
            "playlist_name": playlist_name,
            "refresh_mode": self.refresh_mode_var.get().strip() or "none",
        }
        self.destroy()


class PlaylistTargetDialog(tk.Toplevel):
    def __init__(self, parent, current_server_name: str, current_playlist_name: str, server_names: List[str], playlist_loader) -> None:
        super().__init__(parent)
        self.title("Add Copy Buffer")
        self.geometry("640x300")
        self.minsize(600, 280)
        self.transient(parent)
        self.grab_set()
        self.result = None
        self.playlist_loader = playlist_loader

        self.mode_var = tk.StringVar(value="append")
        self.target_server_var = tk.StringVar(value=current_server_name if current_server_name in server_names else (server_names[0] if server_names else ""))
        self.new_name_var = tk.StringVar(value="")
        self.existing_name_var = tk.StringVar(value="")

        frm = ttk.Frame(self, padding=12)
        frm.pack(fill="both", expand=True)
        frm.columnconfigure(1, weight=1)

        ttk.Label(frm, text="What do you want to do with the copy buffer?").grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 10))

        ttk.Radiobutton(frm, text="Append to existing playlist", variable=self.mode_var, value="append", command=self._refresh_mode).grid(row=1, column=0, columnspan=2, sticky="w")
        self.existing_wrap = ttk.Frame(frm)
        self.existing_wrap.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(4, 10))
        self.existing_wrap.columnconfigure(1, weight=1)
        ttk.Label(self.existing_wrap, text="Server:").grid(row=0, column=0, sticky="w", padx=(18, 6))
        self.server_combo = ttk.Combobox(self.existing_wrap, textvariable=self.target_server_var, state="readonly", values=server_names)
        self.server_combo.grid(row=0, column=1, sticky="ew")
        self.server_combo.bind("<<ComboboxSelected>>", self._on_server_changed)

        ttk.Label(self.existing_wrap, text="Existing playlist:").grid(row=1, column=0, sticky="w", padx=(18, 6), pady=(8, 0))
        self.existing_combo = ttk.Combobox(self.existing_wrap, textvariable=self.existing_name_var, state="readonly", values=[])
        self.existing_combo.grid(row=1, column=1, sticky="ew", pady=(8, 0))

        ttk.Radiobutton(frm, text="Create new playlist", variable=self.mode_var, value="create", command=self._refresh_mode).grid(row=3, column=0, columnspan=2, sticky="w")
        self.new_wrap = ttk.Frame(frm)
        self.new_wrap.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(4, 0))
        self.new_wrap.columnconfigure(1, weight=1)
        ttk.Label(self.new_wrap, text="Target server:").grid(row=0, column=0, sticky="w", padx=(18, 6))
        self.new_server_combo = ttk.Combobox(self.new_wrap, textvariable=self.target_server_var, state="readonly", values=server_names)
        self.new_server_combo.grid(row=0, column=1, sticky="ew")
        self.new_server_combo.bind("<<ComboboxSelected>>", self._on_server_changed)
        ttk.Label(self.new_wrap, text="New playlist name:").grid(row=1, column=0, sticky="w", padx=(18, 6), pady=(8, 0))
        self.new_entry = ttk.Entry(self.new_wrap, textvariable=self.new_name_var)
        self.new_entry.grid(row=1, column=1, sticky="ew", pady=(8, 0))

        btns = ttk.Frame(frm)
        btns.grid(row=5, column=0, columnspan=2, sticky="e", pady=(18, 0))
        ttk.Button(btns, text="Cancel", command=self.destroy).grid(row=0, column=0, padx=6)
        ttk.Button(btns, text="Continue", command=self._accept).grid(row=0, column=1)

        self._load_playlists_for_server(self.target_server_var.get(), current_playlist_name)
        self._refresh_mode()

    def _load_playlists_for_server(self, server_name: str, preferred_playlist: str = ""):
        try:
            playlist_names = list(self.playlist_loader(server_name) or [])
        except Exception as exc:
            messagebox.showerror("Load Playlists", str(exc), parent=self)
            playlist_names = []
        self.existing_combo.configure(values=playlist_names)
        if preferred_playlist and preferred_playlist in playlist_names:
            self.existing_name_var.set(preferred_playlist)
        elif playlist_names:
            self.existing_name_var.set(playlist_names[0])
        else:
            self.existing_name_var.set("")

    def _on_server_changed(self, _event=None):
        self._load_playlists_for_server(self.target_server_var.get())

    def _refresh_mode(self):
        mode = self.mode_var.get().strip().lower()
        if mode == "append":
            self.server_combo.configure(state="readonly")
            self.existing_combo.configure(state="readonly")
            self.new_server_combo.configure(state="disabled")
            self.new_entry.configure(state="disabled")
        else:
            self.server_combo.configure(state="disabled")
            self.existing_combo.configure(state="disabled")
            self.new_server_combo.configure(state="readonly")
            self.new_entry.configure(state="normal")
            self.new_entry.focus_set()

    def _accept(self):
        mode = self.mode_var.get().strip().lower()
        target_server = self.target_server_var.get().strip()
        if not target_server:
            messagebox.showwarning("Choose Server", "Choose a destination server.", parent=self)
            return
        if mode == "append":
            name = self.existing_name_var.get().strip()
            if not name:
                messagebox.showwarning("Choose Playlist", "Choose an existing playlist.", parent=self)
                return
            self.result = {"mode": "append", "playlist_name": name, "target_server_name": target_server}
        else:
            name = self.new_name_var.get().strip()
            if not name:
                messagebox.showwarning("Missing Name", "Enter a name for the new playlist.", parent=self)
                return
            self.result = {"mode": "create", "playlist_name": name, "target_server_name": target_server}
        self.destroy()


class OrganizerApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Plex Playlist Organizer")
        self.root.geometry("1260x900")
        self.root.minsize(1140, 760)

        self.config, self.config_missing = load_config_soft()
        self.server_map = {server["name"]: server for server in self.config["servers"]}

        self.server_name_var = tk.StringVar(value=self.config["servers"][0]["name"] if self.config["servers"] else "")
        self.playlist_title_var = tk.StringVar(value="")
        self.status_var = tk.StringVar(value="Ready.")
        self.move_position_var = tk.StringVar()
        self.cut_title_var = tk.StringVar(value="Move buffer: empty")
        self.selected_summary_var = tk.StringVar(value="Selected: none")
        self.imported_csv_var = tk.StringVar(value="Imported CSV: none")
        self.smart_playlist_type_var = tk.StringVar(value="Movie")
        self.group_by_var = tk.StringVar(value="None")
        self.search_result_var = tk.StringVar(value="Filtered: 0")
        self.rule_field_vars = [tk.StringVar() for _ in range(4)]
        self.rule_op_vars = [tk.StringVar() for _ in range(4)]
        self.rule_value_vars = [tk.StringVar() for _ in range(4)]
        self.filter_preset_var = tk.StringVar(value="")
        self.visible_columns = ["position", "title", "genre", "year"]
        self.available_columns = [
            ("position", "#"), ("title", "Title"), ("genre", "Genre"), ("year", "Year"),
            ("studio", "Studio"), ("content_rating", "Content Rating"), ("artist", "Artist"),
            ("album", "Album"), ("duration", "Duration"), ("date_added", "Date Added"), ("last_played", "Last Played")
        ]
        self.filter_presets = self.load_filter_presets()
        self.suppress_confirmations_var = tk.BooleanVar(value=bool(self.config.get("suppress_confirmations", False)))

        self.server: Optional[PlexServer] = None
        self.playlist_rating_key: Optional[str] = None
        self.playlist_list: List[Dict[str, Any]] = []
        self.all_items: List[PlaylistItem] = []

        self.cut_item_ids: List[str] = []
        self.cut_item_rating_keys: List[str] = []
        self.copy_item_ids: List[str] = []
        self.copy_item_rating_keys: List[str] = []
        self.copy_items: List[PlaylistItem] = []
        self.copy_source_server_name: str = ""
        self.copy_title_var = tk.StringVar(value="Copy buffer: empty")
        self.skip_db_backup_prompt_for_copy_buffer_session = False

        self.imported_csv_path: Optional[Path] = None
        self.imported_csv_rows: List[Dict[str, str]] = []

        self.filtered_items: List[PlaylistItem] = []
        self.display_rows: List[Tuple[str, Any]] = []
        self.sort_column: str = "position"
        self.sort_reverse: bool = False
        self.drag_item_ids: List[str] = []
        self.drag_start_row: Optional[str] = None
        self.drag_start_y: int = 0
        self.drag_active: bool = False
        self.progress_dialog: Optional[tk.Toplevel] = None
        self.progress_label_var = tk.StringVar(value="Working...")
        self.progress_bar = None
        self.active_task_count = 0
        self.current_task_label = ""
        self.current_task_started_at = 0.0
        self.last_progress_at = 0.0
        self.last_progress_message = "Idle."
        self.stall_seconds = 60
        self.activity_log_path = OPERATION_LOG_PATH
        self.activity_text = None
        self.activity_verbose_var = tk.BooleanVar(value=True)
        self.operation_journal_path = OPERATION_JOURNAL_PATH
        self.current_write_journal: Optional[Dict[str, Any]] = None
        self.last_playlist_backup_path: Optional[Path] = None
        self.last_playlist_backup_label: str = ""

        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.on_root_close)
        self.on_filter_type_changed()
        self.refresh_filter_preset_combo()
        self.log_event("Activity log initialized.")
        self.root.after(300, self.check_for_interrupted_operation)

        if self.config_missing or not self.config.get("plex_token"):
            self.root.after(100, lambda: self.open_config_dialog(require_save=True))
        else:
            self.root.after(100, self.initialize_server)

    def _build_ui(self) -> None:
        self.root.columnconfigure(1, weight=1)
        self.root.rowconfigure(1, weight=1)

        top = ttk.Frame(self.root, padding=10)
        top.grid(row=0, column=0, columnspan=2, sticky="nsew")
        top.columnconfigure(8, weight=1)

        ttk.Label(top, text="Server:").grid(row=0, column=0, sticky="w", padx=(0, 6))
        self.server_combo = ttk.Combobox(top, textvariable=self.server_name_var, state="readonly", width=18, values=list(self.server_map.keys()))
        self.server_combo.grid(row=0, column=1, sticky="w", padx=(0, 12))
        self.server_combo.bind("<<ComboboxSelected>>", self.on_server_changed)

        ttk.Label(top, text="Playlist:").grid(row=0, column=2, sticky="w", padx=(0, 6))
        self.playlist_combo = ttk.Combobox(top, textvariable=self.playlist_title_var, state="readonly", width=30)
        self.playlist_combo.grid(row=0, column=3, sticky="w", padx=(0, 8))
        self.playlist_combo.bind("<<ComboboxSelected>>", lambda _e: self.refresh_playlist())

        ttk.Button(top, text="Refresh", command=self.refresh_playlist).grid(row=0, column=4, sticky="w", padx=(0, 8))
        ttk.Button(top, text="Ping", command=self.ping_server).grid(row=0, column=5, sticky="w", padx=(0, 8))
        ttk.Button(top, text="Config", command=lambda: self.open_config_dialog(require_save=False)).grid(row=0, column=6, sticky="w", padx=(0, 8))
        ttk.Button(top, text="About", command=self.show_about).grid(row=0, column=7, sticky="w", padx=(0, 12))

        self.server_label = ttk.Label(top, text="")
        self.server_label.grid(row=1, column=0, columnspan=7, sticky="w", pady=(8, 0))
        ttk.Label(top, textvariable=self.search_result_var).grid(row=1, column=7, columnspan=2, sticky="e", pady=(8, 0))

        left_container = ttk.Frame(self.root, padding=(10, 0, 4, 10))
        left_container.grid(row=1, column=0, sticky="nsew")
        left_container.columnconfigure(0, weight=1)
        left_container.rowconfigure(0, weight=1)

        self.left_canvas = tk.Canvas(left_container, highlightthickness=0, borderwidth=0, width=370)
        left_scroll = ttk.Scrollbar(left_container, orient="vertical", command=self.left_canvas.yview)
        self.left_canvas.configure(yscrollcommand=left_scroll.set)
        self.left_canvas.grid(row=0, column=0, sticky="nsew")
        left_scroll.grid(row=0, column=1, sticky="ns")

        left = ttk.Frame(self.left_canvas)
        self._left_canvas_window = self.left_canvas.create_window((0, 0), window=left, anchor="nw")
        left.bind("<Configure>", self._on_left_frame_configure)
        self.left_canvas.bind("<Configure>", self._on_left_canvas_configure)
        self.left_canvas.bind_all("<MouseWheel>", self._on_global_mousewheel, add="+")

        right = ttk.Frame(self.root, padding=(0, 0, 10, 10))
        right.grid(row=1, column=1, sticky="nsew")
        right.columnconfigure(0, weight=1)
        right.rowconfigure(2, weight=1)

        action_box = ttk.LabelFrame(left, text="Playlist Actions", padding=10)
        action_box.grid(row=0, column=0, sticky="new", pady=(0, 10))
        action_box.columnconfigure(0, weight=1)
        action_box.columnconfigure(1, weight=1)
        ttk.Button(action_box, text="Backup", command=self.backup_playlist).grid(row=0, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(action_box, text="Export CSV", command=self.export_csv).grid(row=0, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(action_box, text="Import CSV", command=self.import_csv).grid(row=1, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(action_box, text="Apply Imported CSV", command=self.apply_imported_csv).grid(row=1, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(action_box, text="Restore Latest", command=self.restore_latest).grid(row=2, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(action_box, text="Restore From File", command=self.restore_file).grid(row=2, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(action_box, text="Copy Playlist To Server", command=self.copy_playlist_to_server).grid(row=3, column=0, columnspan=2, sticky="ew", pady=2)
        ttk.Label(action_box, textvariable=self.imported_csv_var, wraplength=320, justify="left").grid(row=4, column=0, columnspan=2, sticky="w", pady=(8, 0))

        move_box = ttk.LabelFrame(left, text="Reorder Current Playlist", padding=10)
        move_box.grid(row=1, column=0, sticky="new", pady=(0, 10))
        move_box.columnconfigure(1, weight=1)
        ttk.Label(move_box, text="To slot:").grid(row=0, column=0, sticky="w", padx=(0, 6))
        ttk.Entry(move_box, textvariable=self.move_position_var, width=8).grid(row=0, column=1, sticky="ew", padx=(0, 6))
        ttk.Button(move_box, text="Move To Slot", command=self.move_to_position).grid(row=0, column=2, sticky="ew")
        move_row = ttk.Frame(move_box)
        move_row.grid(row=1, column=0, columnspan=3, sticky="ew", pady=(8, 0))
        move_row.columnconfigure(0, weight=1)
        move_row.columnconfigure(1, weight=1)
        ttk.Button(move_row, text="Move Up One", command=self.move_up_one).grid(row=0, column=0, sticky="ew", padx=(0, 4))
        ttk.Button(move_row, text="Move Down One", command=self.move_down_one).grid(row=0, column=1, sticky="ew", padx=(4, 0))

        select_box = ttk.LabelFrame(left, text="Selection Actions", padding=10)
        select_box.grid(row=2, column=0, sticky="new", pady=(0, 10))
        select_box.columnconfigure(0, weight=1)
        select_box.columnconfigure(1, weight=1)
        ttk.Label(select_box, textvariable=self.selected_summary_var, wraplength=320, justify="left").grid(row=0, column=0, columnspan=2, sticky="w")
        ttk.Label(select_box, textvariable=self.cut_title_var, wraplength=150, justify="center", anchor="center").grid(row=1, column=0, sticky="ew", pady=(6, 0), padx=(0, 4))
        ttk.Label(select_box, textvariable=self.copy_title_var, wraplength=150, justify="center", anchor="center").grid(row=1, column=1, sticky="ew", pady=(6, 0), padx=(4, 0))
        ttk.Button(select_box, text="Cut Selected", command=self.cut_selected_block).grid(row=2, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(select_box, text="Copy Selected", command=self.copy_selected_block).grid(row=2, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(select_box, text="Paste Before", command=lambda: self.paste_cut_block("before")).grid(row=3, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(select_box, text="Paste After", command=lambda: self.paste_cut_block("after")).grid(row=3, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(select_box, text="Add Selected To Playlist...", command=self.add_selected_to_playlist).grid(row=4, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(select_box, text="Add Copy Buffer...", command=self.add_copy_buffer_to_playlist).grid(row=4, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(select_box, text="New Playlist From Selected", command=self.new_playlist_from_selected).grid(row=5, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(select_box, text="New Playlist From Move Buffer", command=self.new_playlist_from_cut).grid(row=5, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(select_box, text="Export Selected To CSV", command=self.export_selected_to_csv).grid(row=6, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(select_box, text="Export Move Buffer", command=self.export_cut_to_csv).grid(row=6, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Button(select_box, text="Clear Move Buffer", command=self.clear_cut_buffer).grid(row=7, column=0, sticky="ew", pady=(4, 0), padx=(0, 4))
        ttk.Button(select_box, text="Clear Copy Buffer", command=self.clear_copy_buffer).grid(row=7, column=1, sticky="ew", pady=(4, 0), padx=(4, 0))

        options_box = ttk.LabelFrame(left, text="Options", padding=10)
        options_box.grid(row=3, column=0, sticky="new", pady=(0, 10))
        ttk.Checkbutton(options_box, text="Suppress confirmations", variable=self.suppress_confirmations_var, command=self.on_toggle_confirmations).grid(row=0, column=0, sticky="w")

        danger_box = ttk.LabelFrame(left, text="Danger Zone", padding=10)
        danger_box.grid(row=4, column=0, sticky="new")
        danger_box.columnconfigure(0, weight=1)
        danger_box.columnconfigure(1, weight=1)
        ttk.Button(danger_box, text="Remove From Playlist", command=self.remove_selected_from_playlist).grid(row=0, column=0, sticky="ew", pady=2, padx=(0, 4))
        ttk.Button(danger_box, text="Delete From Plex", command=self.delete_selected_from_plex).grid(row=0, column=1, sticky="ew", pady=2, padx=(4, 0))
        ttk.Label(
            danger_box,
            text="Powr Playlist never modifies your real media files. It only changes Plex playlist/library state and app backups.",
            wraplength=320,
            justify="left",
        ).grid(row=1, column=0, columnspan=2, sticky="w", pady=(8, 0))

        smart_box = ttk.LabelFrame(right, text="Smart Search / Filter", padding=10)
        smart_box.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        for c in range(4):
            smart_box.columnconfigure(c, weight=1 if c in {1,3} else 0)

        ttk.Label(smart_box, text="Playlist Type").grid(row=0, column=0, sticky="w")
        self.playlist_type_combo = ttk.Combobox(smart_box, textvariable=self.smart_playlist_type_var, state="readonly", values=["Movie", "TV Show", "Music"])
        self.playlist_type_combo.grid(row=0, column=1, sticky="ew", padx=(0, 8))
        self.playlist_type_combo.bind("<<ComboboxSelected>>", lambda _e: self.on_filter_type_changed())

        ttk.Label(smart_box, text="Group By").grid(row=0, column=2, sticky="w")
        self.group_by_combo = ttk.Combobox(smart_box, textvariable=self.group_by_var, state="readonly")
        self.group_by_combo.grid(row=0, column=3, sticky="ew")
        self.group_by_combo.bind("<<ComboboxSelected>>", lambda _e: self.apply_smart_filter())

        self.rule_field_combos = []
        self.rule_op_combos = []
        self.rule_value_entries = []
        for i in range(1, 4):
            ttk.Label(smart_box, text=f"Rule {i}").grid(row=i, column=0, sticky="w", pady=4)
            field_combo = ttk.Combobox(smart_box, textvariable=self.rule_field_vars[i], state="readonly")
            field_combo.grid(row=i, column=1, sticky="ew", padx=(0, 6), pady=4)
            field_combo.bind("<<ComboboxSelected>>", lambda _e, idx=i: self.on_rule_field_changed(idx))
            op_combo = ttk.Combobox(smart_box, textvariable=self.rule_op_vars[i], state="readonly", values=["contains", "equals", "starts with", "ends with", "any of", "none of", ">=", "<=", ">", "<", "between"])
            op_combo.grid(row=i, column=2, sticky="ew", padx=(0, 6), pady=4)
            value_entry = ttk.Entry(smart_box, textvariable=self.rule_value_vars[i])
            value_entry.grid(row=i, column=3, sticky="ew", pady=4)
            value_entry.bind("<KeyRelease>", lambda _e: self.apply_smart_filter())
            self.rule_field_combos.append(field_combo)
            self.rule_op_combos.append(op_combo)
            self.rule_value_entries.append(value_entry)

        btn_bar = ttk.Frame(smart_box)
        btn_bar.grid(row=4, column=0, columnspan=4, sticky="e", pady=(8, 0))
        ttk.Button(btn_bar, text="Apply Filter", command=self.apply_smart_filter).grid(row=0, column=0, padx=4)
        ttk.Button(btn_bar, text="Clear Filter", command=self.clear_smart_filter).grid(row=0, column=1, padx=4)
        ttk.Button(btn_bar, text="Save Filter", command=self.save_current_filter_preset).grid(row=0, column=2, padx=4)
        self.filter_preset_combo = ttk.Combobox(btn_bar, textvariable=self.filter_preset_var, state="readonly", width=18)
        self.filter_preset_combo.grid(row=0, column=3, padx=4)
        self.filter_preset_combo.bind("<<ComboboxSelected>>", lambda _e: self.load_selected_filter_preset())
        ttk.Button(btn_bar, text="Delete Filter", command=self.delete_selected_filter_preset).grid(row=0, column=4, padx=4)

        header_bar = ttk.Frame(right)
        header_bar.grid(row=1, column=0, sticky="ew", pady=(0, 6))
        header_bar.columnconfigure(0, weight=1)
        ttk.Label(header_bar, text="Playlist Items").grid(row=0, column=0, sticky="w")
        ttk.Button(header_bar, text="Columns", command=self.choose_visible_columns).grid(row=0, column=1, sticky="e")

        self.tree = ttk.Treeview(right, show="headings", selectmode="extended")
        self.configure_tree_columns()
        self.tree.grid(row=2, column=0, sticky="nsew")

        yscroll = ttk.Scrollbar(right, orient="vertical", command=self.tree.yview)
        yscroll.grid(row=2, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=yscroll.set)
        self.tree.bind("<<TreeviewSelect>>", lambda _e: self.update_selection_label())
        self.tree.bind("<Double-1>", lambda _e: self.cut_selected_block())
        self.tree.bind("<Control-a>", self.on_select_all)
        self.tree.bind("<Control-A>", self.on_select_all)
        self.root.bind("<Control-z>", self.on_undo_shortcut)
        self.root.bind("<Control-Z>", self.on_undo_shortcut)
        self.tree.bind("<Button-3>", self.on_tree_right_click)
        self.tree.bind("<ButtonPress-1>", self.on_tree_drag_start, add="+")
        self.tree.bind("<B1-Motion>", self.on_tree_drag_motion, add="+")
        self.tree.bind("<ButtonRelease-1>", self.on_tree_drag_release, add="+")

        self._build_tree_context_menu()

        activity = ttk.LabelFrame(self.root, text="Activity & Safety Log", padding=6)
        activity.grid(row=2, column=0, columnspan=2, sticky="nsew", padx=10, pady=(0, 6))
        activity.columnconfigure(0, weight=1)
        activity.rowconfigure(0, weight=1)

        self.activity_text = tk.Text(activity, height=8, wrap="word", state="disabled")
        self.activity_text.grid(row=0, column=0, sticky="nsew")
        activity_scroll = ttk.Scrollbar(activity, orient="vertical", command=self.activity_text.yview)
        activity_scroll.grid(row=0, column=1, sticky="ns")
        self.activity_text.configure(yscrollcommand=activity_scroll.set)

        activity_btns = ttk.Frame(activity)
        activity_btns.grid(row=1, column=0, columnspan=2, sticky="e", pady=(6, 0))
        ttk.Checkbutton(activity_btns, text="Verbose", variable=self.activity_verbose_var).pack(side="left", padx=(0, 8))
        ttk.Button(activity_btns, text="Save Log", command=self.save_activity_log_dialog).pack(side="left", padx=4)
        ttk.Button(activity_btns, text="Clear View", command=self.clear_activity_view).pack(side="left", padx=4)

        status = ttk.Label(self.root, textvariable=self.status_var, relief="sunken", anchor="w", padding=6)
        status.grid(row=3, column=0, columnspan=2, sticky="ew")



    def log_event(self, message: str, always_show: bool = True):
        stamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{stamp}] {message}"
        try:
            with self.activity_log_path.open("a", encoding="utf-8") as handle:
                handle.write(line + "\n")
        except Exception:
            pass
        if self.activity_text is not None and (always_show or self.activity_verbose_var.get()):
            self.activity_text.configure(state="normal")
            self.activity_text.insert("end", line + "\n")
            self.activity_text.see("end")
            self.activity_text.configure(state="disabled")

    def clear_activity_view(self):
        if self.activity_text is not None:
            self.activity_text.configure(state="normal")
            self.activity_text.delete("1.0", "end")
            self.activity_text.configure(state="disabled")
        self.log_event("Activity view cleared.")

    def save_activity_log_dialog(self):
        path = filedialog.asksaveasfilename(title="Save activity log", initialfile=self.activity_log_path.name, defaultextension=".log", filetypes=[("Log files", "*.log"), ("Text files", "*.txt"), ("All files", "*.*")])
        if not path:
            return
        content = self.activity_text.get("1.0", "end") if self.activity_text is not None else ""
        Path(path).write_text(content, encoding="utf-8")
        self.log_event(f"Saved activity log to {path}")

    def update_task_progress(self, message: str, always_show: bool = True):
        self.last_progress_at = monotonic()
        self.last_progress_message = message
        self.progress_label_var.set(message)
        self._update_write_journal_progress(message)
        self.log_event(message, always_show=always_show)
        if self.progress_dialog and self.progress_dialog.winfo_exists():
            self.progress_dialog.update_idletasks()

    def _server_progress(self, message: str):
        self.root.after(0, lambda msg=message: self.update_task_progress(msg, always_show=self.activity_verbose_var.get()))

    def _check_task_stall(self):
        if self.active_task_count <= 0:
            return
        elapsed = monotonic() - self.last_progress_at if self.last_progress_at else 0
        if elapsed >= self.stall_seconds:
            stall_msg = f"No progress detected for {int(elapsed)}s during '{self.current_task_label}'. Last update: {self.last_progress_message}"
            self.progress_label_var.set(stall_msg)
            self.log_event(stall_msg)
            self.last_progress_at = monotonic()
        self.root.after(1000, self._check_task_stall)

    def _write_operation_journal_file(self, payload: Dict[str, Any]):
        try:
            self.operation_journal_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        except Exception as exc:
            self.log_event(f"Failed to write operation journal: {exc}")

    def _begin_write_journal(self, label: str, context: Dict[str, Any]):
        payload = {
            "status": "running",
            "task_label": label,
            "operation_type": context.get("operation_type", "write"),
            "server_name": context.get("server_name", ""),
            "playlist_title": context.get("playlist_title", ""),
            "playlist_rating_key": context.get("playlist_rating_key", ""),
            "notes": context.get("notes", ""),
            "started_at": datetime.now().isoformat(timespec="seconds"),
            "last_progress_message": label,
            "last_progress_at": datetime.now().isoformat(timespec="seconds"),
            "safety_backup_path": "",
        }
        self.current_write_journal = payload
        self._write_operation_journal_file(payload)

    def _update_write_journal_progress(self, message: str):
        if not self.current_write_journal:
            return
        self.current_write_journal["last_progress_message"] = message
        self.current_write_journal["last_progress_at"] = datetime.now().isoformat(timespec="seconds")
        self._write_operation_journal_file(self.current_write_journal)

    def _set_write_journal_backup_path(self, path: Path):
        if not self.current_write_journal:
            return
        self.current_write_journal["safety_backup_path"] = str(path)
        self._write_operation_journal_file(self.current_write_journal)

    def _finish_write_journal(self, status: str, error: str = ""):
        if not self.current_write_journal:
            return
        self.current_write_journal["status"] = status
        self.current_write_journal["finished_at"] = datetime.now().isoformat(timespec="seconds")
        if error:
            self.current_write_journal["error"] = error
        self._write_operation_journal_file(self.current_write_journal)
        self.current_write_journal = None

    def check_for_interrupted_operation(self):
        try:
            if not self.operation_journal_path.exists():
                return
            payload = json.loads(self.operation_journal_path.read_text(encoding="utf-8"))
            if not isinstance(payload, dict):
                return
            if payload.get("status") != "running":
                return
            lines = [
                "An interrupted playlist operation was detected.",
                f"Task: {payload.get('task_label', '')}",
                f"Server: {payload.get('server_name', '')}",
                f"Playlist: {payload.get('playlist_title', '')}",
                f"Last step: {payload.get('last_progress_message', '')}",
            ]
            backup_path = str(payload.get("safety_backup_path", "")).strip()
            if backup_path:
                lines.append(f"Safety backup: {backup_path}")
            messagebox.showwarning("Interrupted Operation Detected", "\n".join(lines), parent=self.root)
            self.log_event("Detected interrupted operation journal on startup.")
        except Exception as exc:
            self.log_event(f"Failed to inspect interrupted operation journal: {exc}")

    def load_filter_presets(self) -> Dict[str, Any]:
        try:
            if FILTER_PRESETS_PATH.exists():
                data = json.loads(FILTER_PRESETS_PATH.read_text(encoding="utf-8"))
                return data if isinstance(data, dict) else {}
        except Exception:
            return {}
        return {}

    def save_filter_presets(self):
        FILTER_PRESETS_PATH.write_text(json.dumps(self.filter_presets, indent=2), encoding="utf-8")
        self.refresh_filter_preset_combo()

    def refresh_filter_preset_combo(self):
        if hasattr(self, "filter_preset_combo"):
            names = sorted(self.filter_presets.keys(), key=str.lower)
            self.filter_preset_combo["values"] = names
            if self.filter_preset_var.get() not in names:
                self.filter_preset_var.set("")

    def current_filter_payload(self) -> Dict[str, Any]:
        return {
            "playlist_type": self.smart_playlist_type_var.get(),
            "group_by": self.group_by_var.get(),
            "rules": [
                {"field": self.rule_field_vars[i].get(), "op": self.rule_op_vars[i].get(), "value": self.rule_value_vars[i].get()}
                for i in range(1, 4)
            ],
            "visible_columns": list(self.visible_columns),
        }

    def save_current_filter_preset(self):
        name = simpledialog.askstring("Save Filter", "Name this filter preset:", parent=self.root)
        if not name:
            return
        self.filter_presets[name.strip()] = self.current_filter_payload()
        self.save_filter_presets()
        self.filter_preset_var.set(name.strip())
        self.set_status(f"Saved filter preset '{name.strip()}'.")

    def load_selected_filter_preset(self):
        name = self.filter_preset_var.get().strip()
        payload = self.filter_presets.get(name)
        if not payload:
            return
        self.smart_playlist_type_var.set(payload.get("playlist_type", "Movie"))
        self.on_filter_type_changed()
        self.group_by_var.set(payload.get("group_by", "None"))
        rules = payload.get("rules", [])
        for i in range(1,4):
            rule = rules[i-1] if i-1 < len(rules) else {}
            self.rule_field_vars[i].set(rule.get("field", ""))
            self.rule_op_vars[i].set(rule.get("op", "contains"))
            self.rule_value_vars[i].set(rule.get("value", ""))
        cols = payload.get("visible_columns")
        if isinstance(cols, list) and cols:
            self.visible_columns = [c for c in cols if c in {k for k,_ in self.available_columns}]
            self.configure_tree_columns()
        self.apply_smart_filter()
        self.set_status(f"Loaded filter preset '{name}'.")

    def delete_selected_filter_preset(self):
        name = self.filter_preset_var.get().strip()
        if not name or name not in self.filter_presets:
            return
        if not messagebox.askyesno("Delete Filter", f"Delete filter preset '{name}'?"):
            return
        self.filter_presets.pop(name, None)
        self.save_filter_presets()
        self.filter_preset_var.set("")
        self.set_status(f"Deleted filter preset '{name}'.")

    def choose_visible_columns(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("Choose Columns")
        dlg.transient(self.root)
        dlg.grab_set()
        vars = {}
        frame = ttk.Frame(dlg, padding=12)
        frame.pack(fill="both", expand=True)
        for idx, (key, label) in enumerate(self.available_columns):
            if key == "position":
                default = True
            else:
                default = key in self.visible_columns
            var = tk.BooleanVar(value=default)
            vars[key] = var
            chk = ttk.Checkbutton(frame, text=label, variable=var)
            chk.grid(row=idx//2, column=idx%2, sticky="w", padx=8, pady=4)
        def apply():
            cols = [k for k,_ in self.available_columns if vars[k].get()]
            if "position" not in cols:
                cols.insert(0, "position")
            if "title" not in cols:
                cols.insert(1 if cols and cols[0]=="position" else 0, "title")
            self.visible_columns = cols
            self.configure_tree_columns()
            self.populate_tree(self.filtered_items if self.filtered_items else self.all_items, selected_rating_keys=[item.rating_key for item in self.selected_items()])
            dlg.destroy()
        btns = ttk.Frame(frame)
        btns.grid(row=99, column=0, columnspan=2, sticky="e", pady=(12,0))
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right", padx=4)
        ttk.Button(btns, text="Apply", command=apply).pack(side="right", padx=4)

    def configure_tree_columns(self):
        labels = {k:v for k,v in self.available_columns}
        self.tree["columns"] = tuple(self.visible_columns)
        for col in self.visible_columns:
            self.tree.heading(col, text=labels.get(col, col.title()), command=lambda c=col: self.on_sort_column(c))
            width = 110
            anchor = "w"
            if col == "position": width, anchor = 70, "center"
            elif col == "title": width = 520
            elif col in {"genre","studio","artist","album"}: width = 160
            elif col in {"year","date_added","last_played"}: width, anchor = 100, "center"
            elif col == "duration": width, anchor = 110, "center"
            elif col == "content_rating": width, anchor = 120, "center"
            self.tree.column(col, width=width, anchor=anchor)

    def format_tree_value(self, item: PlaylistItem, col: str):
        if col == "position": return item.position
        if col == "title": return item.title
        if col == "genre": return item.primary_genre or ""
        if col == "year": return item.year or ""
        if col == "studio": return item.studio
        if col == "content_rating": return item.content_rating
        if col == "artist": return item.artist
        if col == "album": return item.album
        if col == "duration":
            secs = int((item.duration_ms or 0) / 1000)
            h, rem = divmod(secs, 3600); m, s = divmod(rem, 60)
            return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"
        if col == "date_added":
            return datetime.fromtimestamp(item.date_added).strftime("%Y-%m-%d") if item.date_added else ""
        if col == "last_played":
            return datetime.fromtimestamp(item.last_played).strftime("%Y-%m-%d") if item.last_played else ""
        return ""

    def _on_left_frame_configure(self, _event=None):
        if hasattr(self, "left_canvas"):
            self.left_canvas.configure(scrollregion=self.left_canvas.bbox("all"))

    def _on_left_canvas_configure(self, event):
        if hasattr(self, "_left_canvas_window"):
            self.left_canvas.itemconfigure(self._left_canvas_window, width=event.width)

    def _on_global_mousewheel(self, event):
        if not hasattr(self, "left_canvas"):
            return
        try:
            widget = self.root.winfo_containing(event.x_root, event.y_root)
        except (KeyError, tk.TclError):
            widget = getattr(event, "widget", None)
        if widget is None:
            return
        current = widget
        inside_left = False
        while current is not None:
            if current == self.left_canvas:
                inside_left = True
                break
            current = getattr(current, "master", None)
        if inside_left:
            delta = getattr(event, "delta", 0)
            if delta:
                self.left_canvas.yview_scroll(int(-1 * (delta / 120)), "units")

    def on_tree_drag_start(self, event):
        row_id = self.tree.identify_row(event.y)
        self.drag_start_row = row_id or None
        self.drag_start_y = event.y
        self.drag_active = False
        self.drag_item_ids = []
        if not row_id:
            return
        item = self.tree_item_for_iid(row_id)
        if item is None:
            return
        ctrl_or_shift = bool(event.state & 0x0005)
        if ctrl_or_shift:
            # Preserve standard Windows-style multi-select behavior.
            self.drag_start_row = None
            return
        if row_id not in self.tree.selection():
            self.tree.selection_set(row_id)
            self.tree.focus(row_id)
            self.update_selection_label()
        self.drag_item_ids = [itm.playlist_item_id for itm in self.selected_items()]

    def on_tree_drag_motion(self, event):
        if self.drag_start_row and self.drag_item_ids and abs(event.y - self.drag_start_y) > 8:
            self.drag_active = True

    def on_tree_drag_release(self, event):
        if not self.drag_active or not self.drag_item_ids:
            self.drag_start_row = None
            self.drag_item_ids = []
            self.drag_active = False
            return
        row_id = self.tree.identify_row(event.y)
        target = self.tree_item_for_iid(row_id) if row_id else None
        if target is None or target.playlist_item_id in set(self.drag_item_ids):
            self.drag_start_row = None
            self.drag_item_ids = []
            self.drag_active = False
            return
        bbox = self.tree.bbox(row_id)
        where = "after"
        if bbox:
            midpoint = bbox[1] + (bbox[3] // 2)
            where = "before" if event.y < midpoint else "after"
        self.move_selected_relative(self.drag_item_ids, target, where)
        self.drag_start_row = None
        self.drag_item_ids = []
        self.drag_active = False

    def _build_tree_context_menu(self):
        self.tree_menu = tk.Menu(self.root, tearoff=0)
        self.tree_menu.add_command(label="Select All", command=self.select_all_visible_items)
        self.tree_menu.add_separator()
        self.tree_menu.add_command(label="Cut Selected", command=self.cut_selected_block)
        self.tree_menu.add_command(label="Copy Selected", command=self.copy_selected_block)
        self.tree_menu.add_command(label="Paste Before Selected", command=lambda: self.paste_cut_block("before"))
        self.tree_menu.add_command(label="Paste After Selected", command=lambda: self.paste_cut_block("after"))
        self.tree_menu.add_separator()
        self.tree_menu.add_command(label="Add Selected To Playlist...", command=self.add_selected_to_playlist)
        self.tree_menu.add_command(label="New Playlist From Selected", command=self.new_playlist_from_selected)
        self.tree_menu.add_command(label="Export Selected To CSV", command=self.export_selected_to_csv)
        self.tree_menu.add_separator()
        self.tree_menu.add_command(label="Undo Last Playlist Change", command=self.undo_last_playlist_change)
        self.tree_menu.add_separator()
        self.tree_menu.add_command(label="Copy Playlist To Server", command=self.copy_playlist_to_server)
        self.tree_menu.add_command(label="Remove Selected From Playlist", command=self.remove_selected_from_playlist)
        self.tree_menu.add_command(label="Delete Selected From Plex", command=self.delete_selected_from_plex)

    def select_all_visible_items(self):
        item_iids = [str(idx) for idx, (kind, _payload) in enumerate(self.display_rows) if kind == "item"]
        if not item_iids:
            return
        self.tree.selection_set(item_iids)
        self.tree.focus(item_iids[0])
        self.tree.see(item_iids[0])
        self.update_selection_label()

    def on_select_all(self, event=None):
        self.select_all_visible_items()
        return "break"

    def on_tree_right_click(self, event):
        row_id = self.tree.identify_row(event.y)
        if row_id:
            item = self.tree_item_for_iid(row_id)
            if item is not None and row_id not in self.tree.selection():
                self.tree.selection_set(row_id)
                self.tree.focus(row_id)
                self.update_selection_label()
        has_selection = bool(self.selected_items())
        has_cut = bool(self.cut_item_ids)
        self.tree_menu.entryconfigure("Cut Selected", state=("normal" if has_selection else "disabled"))
        self.tree_menu.entryconfigure("Copy Selected", state=("normal" if has_selection else "disabled"))
        self.tree_menu.entryconfigure("Paste Before Selected", state=("normal" if has_selection and has_cut else "disabled"))
        self.tree_menu.entryconfigure("Paste After Selected", state=("normal" if has_selection and has_cut else "disabled"))
        self.tree_menu.entryconfigure("Add Selected To Playlist...", state=("normal" if has_selection else "disabled"))
        self.tree_menu.entryconfigure("New Playlist From Selected", state=("normal" if has_selection else "disabled"))
        self.tree_menu.entryconfigure("Export Selected To CSV", state=("normal" if has_selection else "disabled"))
        self.tree_menu.entryconfigure("Copy Playlist To Server", state=("normal" if self.require_playlist_loaded(silent=True) else "disabled"))
        self.tree_menu.entryconfigure("Remove Selected From Playlist", state=("normal" if has_selection else "disabled"))
        self.tree_menu.entryconfigure("Delete Selected From Plex", state=("normal" if has_selection else "disabled"))
        try:
            self.tree_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.tree_menu.grab_release()

    def _prompt_db_backup_guard_dialog(self, server_name: str, db_path: str) -> Tuple[bool, bool, bool]:
        dialog = tk.Toplevel(self.root)
        dialog.title("Recommended: Back Up Plex Database")
        dialog.transient(self.root)
        dialog.resizable(False, False)
        dialog.grab_set()

        remember_var = tk.BooleanVar(value=False)
        result = {"action": "cancel", "remember": False}

        frame = ttk.Frame(dialog, padding=14)
        frame.pack(fill="both", expand=True)

        if db_path:
            message = (
                f"It is STRONGLY recommended that you back up the Plex database for '{server_name}' before making playlist changes.\n\n"
                f"Configured DB path:\n{db_path}\n\n"
                "Choose whether to back it up now or continue without a database backup."
            )
        else:
            message = (
                f"It is STRONGLY recommended that you back up the Plex database for '{server_name}' before making playlist changes.\n\n"
                "No Plex DB path is configured for this server, so the app cannot back it up automatically.\n\n"
                "Choose whether to continue without an automatic database backup."
            )

        ttk.Label(frame, text=message, justify="left", wraplength=520).pack(anchor="w")
        ttk.Checkbutton(frame, text="No, not this session", variable=remember_var).pack(anchor="w", pady=(10, 0))

        btns = ttk.Frame(frame)
        btns.pack(fill="x", pady=(14, 0))

        def finish(action: str):
            result["action"] = action
            result["remember"] = bool(remember_var.get())
            try:
                dialog.grab_release()
            except Exception:
                pass
            dialog.destroy()

        if db_path:
            ttk.Button(btns, text="Back Up Now", command=lambda: finish("backup")).pack(side="left")
            ttk.Button(btns, text="Continue Without Backup", command=lambda: finish("skip")).pack(side="left", padx=(8, 0))
        else:
            ttk.Button(btns, text="Continue", command=lambda: finish("skip")).pack(side="left")
        ttk.Button(btns, text="Cancel", command=lambda: finish("cancel")).pack(side="right")

        dialog.protocol("WM_DELETE_WINDOW", lambda: finish("cancel"))
        dialog.update_idletasks()
        x = self.root.winfo_rootx() + max((self.root.winfo_width() - dialog.winfo_width()) // 2, 0)
        y = self.root.winfo_rooty() + max((self.root.winfo_height() - dialog.winfo_height()) // 2, 0)
        dialog.geometry(f"+{x}+{y}")
        self.root.wait_window(dialog)

        action = result.get("action", "cancel")
        remember = bool(result.get("remember", False))
        if action == "backup":
            return True, True, False
        if action == "skip":
            return True, False, remember
        return False, False, False

    def confirm_db_backup_guard(self, server: PlexServer):
        """
        Returns (should_continue, should_backup_now)
        """
        if self.copy_items and self.skip_db_backup_prompt_for_copy_buffer_session:
            return True, False

        path = server.plex_db_path()
        name = server.name
        should_continue, should_backup, remember_skip = self._prompt_db_backup_guard_dialog(name, path)
        if not should_continue:
            return False, False

        if remember_skip and self.copy_items:
            self.skip_db_backup_prompt_for_copy_buffer_session = True

        if should_backup:
            return True, True

        if path:
            second = messagebox.askyesno(
                "Proceed At Your Own Risk",
                f"You declined the Plex database backup for '{name}'.\n\n"
                "Proceed at your own risk?",
                parent=self.root,
            )
        else:
            second = messagebox.askyesno(
                "Proceed At Your Own Risk",
                f"No Plex DB path is configured for '{name}', and no automatic database backup will be made.\n\n"
                "Proceed at your own risk?",
                parent=self.root,
            )
        if not second:
            return False, False
        return True, False

    def run_db_guarded_task(self, label: str, server: PlexServer, func, on_success=None, journal_context: Optional[Dict[str, Any]] = None):
        should_continue, should_backup = self.confirm_db_backup_guard(server)
        if not should_continue:
            self.set_status("Action cancelled.")
            return

        journal_context = dict(journal_context or {})

        def task():
            db_backup_path = None
            if journal_context.get("create_safety_backup") and journal_context.get("playlist_title") and journal_context.get("playlist_items") is not None:
                self.update_task_progress(f"Creating silent playlist safety backup for {journal_context.get('playlist_title')}...", always_show=True)
                safety_backup = server.export_backup(f"{journal_context.get('playlist_title')}_auto_safety", journal_context.get("playlist_items") or [])
                self._set_write_journal_backup_path(safety_backup)
            if should_backup:
                self.update_task_progress(f"Running Plex DB backup for {server.name}...", always_show=True)
                db_backup_path = server.backup_plex_database(retention=self.config.get("db_backup_retention", 5))
                save_config(self.config)
            result = func()
            return db_backup_path, result

        def done(payload):
            db_backup_path, result = payload
            if on_success:
                on_success(result, db_backup_path)

        self.run_task(label, task, done, journal_context=journal_context)

    def open_config_dialog(self, require_save: bool = False):
        dialog = ConfigDialog(self.root, self.config, require_save=require_save)
        self.root.wait_window(dialog)
        if dialog.result_config is None:
            if require_save:
                self.root.destroy()
            return

        self.config = normalize_config(dialog.result_config)
        save_config(self.config)
        self.suppress_confirmations_var.set(bool(self.config.get("suppress_confirmations", False)))
        self.server_map = {server["name"]: server for server in self.config["servers"]}
        self.server_combo["values"] = list(self.server_map.keys())

        if self.server_name_var.get() not in self.server_map:
            self.server_name_var.set(self.config["servers"][0]["name"])

        self.initialize_server()
        self.set_status("Configuration saved.")

    def initialize_server(self):
        if not self.server_map:
            self.open_config_dialog(require_save=True)
            return
        if self.server_name_var.get() not in self.server_map:
            self.server_name_var.set(self.config["servers"][0]["name"])
        self.set_active_server(self.server_name_var.get())
        self.load_playlists()

    def set_active_server(self, server_name: str):
        if server_name not in self.server_map:
            self.open_config_dialog(require_save=True)
            return
        self.server = PlexServer(self.server_map[server_name], self.config)
        self.server.progress_callback = self._server_progress
        self.server_label.config(text=f"Server URL: {self.server.base_url}")
        self.log_event(f"Active server set to {server_name} ({self.server.base_url})")
        self.clear_cut_buffer()
        self.imported_csv_path = None
        self.imported_csv_rows = []
        self.imported_csv_var.set("Imported CSV: none")
        self.playlist_rating_key = None
        self.playlist_list = []
        self.playlist_combo["values"] = []
        self.playlist_title_var.set("")
        self.all_items = []
        self.filtered_items = []
        self.display_rows = []
        self.search_result_var.set("Filtered: 0")
        self.populate_tree([])

    def on_server_changed(self, _event=None):
        self.set_active_server(self.server_name_var.get())
        self.load_playlists()

    def on_toggle_confirmations(self):
        self.set_status("Confirmations suppressed." if self.suppress_confirmations_var.get() else "Confirmations enabled.")

    def should_confirm(self, prompt: str) -> bool:
        if self.suppress_confirmations_var.get():
            return True
        return messagebox.askyesno("Confirm", prompt)

    def _show_progress_dialog(self, label: str):
        self.progress_label_var.set(label)
        if self.progress_dialog and self.progress_dialog.winfo_exists():
            self.progress_dialog.deiconify()
            self.progress_dialog.lift()
            self.progress_dialog.update_idletasks()
            return

        dialog = tk.Toplevel(self.root)
        dialog.title("Working")
        dialog.transient(self.root)
        dialog.resizable(False, False)
        dialog.protocol("WM_DELETE_WINDOW", lambda: None)

        fixed_width = 520
        fixed_height = 150
        body = ttk.Frame(dialog, padding=14, width=fixed_width, height=fixed_height)
        body.pack(fill="both", expand=True)
        body.pack_propagate(False)

        status_label = ttk.Label(
            body,
            textvariable=self.progress_label_var,
            justify="center",
            anchor="center",
            wraplength=fixed_width - 40,
        )
        status_label.pack(fill="x", padx=8, pady=(0, 10))

        bar = ttk.Progressbar(body, mode="indeterminate", length=fixed_width - 80)
        bar.pack(fill="x", padx=12)

        detail_label = ttk.Label(
            body,
            text="Please wait while the current Plex operation finalizes.",
            justify="center",
            anchor="center",
            wraplength=fixed_width - 40,
        )
        detail_label.pack(fill="x", pady=(10, 0), padx=8)

        dialog.update_idletasks()
        x = self.root.winfo_rootx() + max((self.root.winfo_width() - fixed_width) // 2, 0)
        y = self.root.winfo_rooty() + max((self.root.winfo_height() - fixed_height) // 2, 0)
        dialog.geometry(f"{fixed_width}x{fixed_height}+{x}+{y}")
        dialog.minsize(fixed_width, fixed_height)
        dialog.maxsize(fixed_width, fixed_height)
        try:
            dialog.grab_set()
        except Exception:
            pass
        bar.start(12)
        self.progress_dialog = dialog
        self.progress_bar = bar

    def _hide_progress_dialog(self):
        if self.progress_bar is not None:
            try:
                self.progress_bar.stop()
            except Exception:
                pass
        if self.progress_dialog and self.progress_dialog.winfo_exists():
            try:
                self.progress_dialog.grab_release()
            except Exception:
                pass
            self.progress_dialog.destroy()
        self.progress_dialog = None
        self.progress_bar = None

    def run_task(self, label: str, func, on_success=None, journal_context: Optional[Dict[str, Any]] = None):
        if self.active_task_count > 0:
            messagebox.showwarning("Task already in progress", "Task already in progress. Please wait for the current operation to finish.")
            self.log_event(f"Blocked overlapping task request: {label}")
            return
        if journal_context:
            self._begin_write_journal(label, journal_context)
        self.current_task_label = label
        self.current_task_started_at = monotonic()
        self.last_progress_at = self.current_task_started_at
        self.last_progress_message = label
        self.set_status(label)
        self.root.config(cursor="watch")
        self.active_task_count += 1
        self._show_progress_dialog(label)
        self.log_event(f"Started task: {label}")
        self.root.after(1000, self._check_task_stall)
        self.root.update_idletasks()

        def worker():
            try:
                result = func()
                self.root.after(0, lambda: self._task_success(result, on_success))
            except Exception as exc:
                tb = traceback.format_exc()
                self.root.after(0, lambda exc=exc, tb=tb: self._task_error(exc, tb))

        threading.Thread(target=worker, daemon=True).start()

    def _task_success(self, result, on_success):
        elapsed = monotonic() - self.current_task_started_at if self.current_task_started_at else 0
        self.log_event(f"Completed task: {self.current_task_label} in {elapsed:.1f}s")
        self._finish_write_journal("completed")
        self.active_task_count = max(0, self.active_task_count - 1)
        if self.active_task_count == 0:
            self.root.config(cursor="")
            self._hide_progress_dialog()
        if on_success:
            on_success(result)

    def _task_error(self, exc, tb):
        self.log_event(f"Task failed: {self.current_task_label} :: {exc}")
        self._finish_write_journal("failed", str(exc))
        self.active_task_count = max(0, self.active_task_count - 1)
        if self.active_task_count == 0:
            self.root.config(cursor="")
            self._hide_progress_dialog()
        self.set_status(f"Error: {exc}")
        messagebox.showerror("Error", f"{exc}\n\n{tb}")

    def on_root_close(self):
        if self.active_task_count > 0:
            current = self.current_task_label or "A playlist operation"
            self.log_event(f"User attempted to close app during active task: {current}")
            should_exit = messagebox.askyesno(
                "Operation still in progress",
                f"{current} is still in progress.\n\n"
                "Closing the app now may leave the playlist or Plex database in a partially updated state and can increase the risk of corruption or require a restore from backup.\n\n"
                "Wait for the current process to finish before closing.\n\n"
                "Do you still want to exit?"
            )
            if not should_exit:
                return
            self.log_event(f"User confirmed forced exit during active task: {current}")
        self.root.destroy()

    def set_status(self, text: str):
        self.status_var.set(text)
        self.root.update_idletasks()

    def visible_items(self) -> List[PlaylistItem]:
        return self.filtered_items if self.filtered_items else self.all_items

    def tree_item_for_iid(self, iid: str) -> Optional[PlaylistItem]:
        try:
            idx = int(iid)
        except ValueError:
            return None
        if 0 <= idx < len(self.display_rows):
            kind, payload = self.display_rows[idx]
            if kind == "item":
                return payload
        return None

    def get_selected_indices(self) -> List[int]:
        result = []
        for iid in self.tree.selection():
            try:
                result.append(int(iid))
            except ValueError:
                continue
        result.sort()
        return result

    def selected_items(self) -> List[PlaylistItem]:
        picked: List[PlaylistItem] = []
        seen = set()
        for iid in self.tree.selection():
            item = self.tree_item_for_iid(iid)
            if item and item.playlist_item_id not in seen:
                picked.append(item)
                seen.add(item.playlist_item_id)
        picked.sort(key=lambda x: x.position)
        return picked

    def selected_item(self) -> Optional[PlaylistItem]:
        items = self.selected_items()
        return items[0] if items else None

    def update_selection_label(self):
        items = self.selected_items()
        if not items:
            text = "Selected: none"
        elif len(items) == 1:
            item = items[0]
            extra = f" | Genre: {item.primary_genre}" if item.primary_genre else ""
            text = f"Selected: {item.display}{extra}"
        else:
            text = f"Selected: {len(items)} items | First: {items[0].display} | Last: {items[-1].display}"
        self.selected_summary_var.set(text)

    def sort_items(self, items: List[PlaylistItem]) -> List[PlaylistItem]:
        def key(item: PlaylistItem):
            col = self.sort_column
            if col == "title":
                return (str(item.title or "").lower(), item.position)
            if col == "genre":
                return (str(item.primary_genre or "").lower(), str(item.title or "").lower(), item.position)
            if col == "year":
                return (item.year if item.year is not None else -1, str(item.title or "").lower(), item.position)
            if col == "studio":
                return (str(item.studio or "").lower(), str(item.title or "").lower(), item.position)
            if col == "content_rating":
                return (str(item.content_rating or "").lower(), str(item.title or "").lower(), item.position)
            if col == "artist":
                return (str(item.artist or "").lower(), str(item.title or "").lower(), item.position)
            if col == "album":
                return (str(item.album or "").lower(), str(item.title or "").lower(), item.position)
            if col == "duration":
                return (int(item.duration_ms or 0), str(item.title or "").lower(), item.position)
            if col == "date_added":
                return (int(item.date_added or 0), str(item.title or "").lower(), item.position)
            if col == "last_played":
                return (int(item.last_played or 0), str(item.title or "").lower(), item.position)
            return (item.position, str(item.title or "").lower())
        return sorted(list(items), key=key, reverse=self.sort_reverse)

    def on_sort_column(self, column: str):
        if self.sort_column == column:
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_column = column
            self.sort_reverse = False
        selected_keys = [item.rating_key for item in self.selected_items()]
        items = self.filtered_items if self.filtered_items else self.all_items
        self.populate_tree(items, selected_rating_keys=selected_keys)
        direction = "descending" if self.sort_reverse else "ascending"
        self.set_status(f"Sorted by {column.title()} ({direction}).")

    def build_display_rows(self, items: List[PlaylistItem]) -> List[Tuple[str, Any]]:
        group_by = self.group_by_var.get()
        rows: List[Tuple[str, Any]] = []
        sorted_items = self.sort_items(items)
        if group_by in {"None", ""}:
            for item in sorted_items:
                rows.append(("item", item))
            return rows

        def group_value(item: PlaylistItem) -> str:
            if group_by == "Genre":
                return item.primary_genre or "Unspecified"
            if group_by == "Year":
                return str(item.year or "Unknown")
            if group_by == "Artist":
                return item.artist or "Unknown Artist"
            if group_by == "Album":
                return item.album or "Unknown Album"
            return "Other"

        current = None
        for item in sorted_items:
            value = group_value(item)
            if value != current:
                current = value
                rows.append(("heading", f"{group_by}: {value}"))
            rows.append(("item", item))
        return rows

    def populate_tree(self, items: List[PlaylistItem], selected_rating_keys: Optional[List[str]] = None):
        self.tree.delete(*self.tree.get_children())
        selected_rating_keys = selected_rating_keys or []
        selected_iids = []
        self.display_rows = self.build_display_rows(items)
        for idx, (kind, payload) in enumerate(self.display_rows):
            iid = str(idx)
            if kind == "heading":
                heading_values = []
                for col in self.visible_columns:
                    heading_values.append(f"── {payload} ──" if col == "title" else "")
                self.tree.insert("", "end", iid=iid, values=tuple(heading_values), tags=("heading",))
            else:
                item = payload
                values = tuple(self.format_tree_value(item, col) for col in self.visible_columns)
                self.tree.insert("", "end", iid=iid, values=values)
                if item.rating_key in selected_rating_keys:
                    selected_iids.append(iid)
        self.tree.tag_configure("heading", foreground="#e5a00d")
        self.tree.selection_remove(*self.tree.selection())
        if selected_iids:
            self.tree.selection_set(selected_iids)
            self.tree.focus(selected_iids[0])
            self.tree.see(selected_iids[0])
        self.update_selection_label()
        self.tree.update_idletasks()
        self.root.update_idletasks()

    def field_options_for_type(self, playlist_type: str) -> List[str]:
        if playlist_type == "Music":
            return ["Title", "Artist", "Album", "Genre", "Year", "Position", "Date Added", "Last Played", "Duration"]
        if playlist_type == "TV Show":
            return ["Title", "Genre", "Year", "Studio", "Content Rating", "Position", "Date Added", "Last Played", "Duration"]
        return ["Title", "Genre", "Year", "Studio", "Content Rating", "Position", "Date Added", "Last Played", "Duration"]

    def group_options_for_type(self, playlist_type: str) -> List[str]:
        if playlist_type == "Music":
            return ["None", "Genre", "Artist", "Album", "Year"]
        return ["None", "Genre", "Year"]

    def on_filter_type_changed(self):
        options = self.field_options_for_type(self.smart_playlist_type_var.get())
        groups = self.group_options_for_type(self.smart_playlist_type_var.get())
        self.group_by_combo["values"] = groups
        if self.group_by_var.get() not in groups:
            self.group_by_var.set(groups[0])
        for i, combo in enumerate(self.rule_field_combos, start=1):
            combo["values"] = options
            if self.rule_field_vars[i].get() not in options:
                self.rule_field_vars[i].set(options[0] if i == 1 else "")
            if not self.rule_op_vars[i].get():
                self.rule_op_vars[i].set("contains" if self.rule_field_vars[i].get() not in {"Year", "Position", "Date Added", "Last Played", "Duration"} else "equals")
        self.apply_smart_filter()

    def on_rule_field_changed(self, idx: int):
        field = self.rule_field_vars[idx].get()
        self.rule_op_vars[idx].set("equals" if field in {"Year", "Position", "Date Added", "Last Played", "Duration"} else ("any of" if field == "Genre" else "contains"))
        self.apply_smart_filter()

    def item_field_value(self, item: PlaylistItem, field_name: str) -> Any:
        if field_name == "Title":
            return item.title
        if field_name == "Genre":
            return ", ".join(item.genres)
        if field_name == "Year":
            return item.year or 0
        if field_name == "Position":
            return item.position
        if field_name == "Artist":
            return item.artist
        if field_name == "Album":
            return item.album
        if field_name == "Studio":
            return item.studio
        if field_name == "Content Rating":
            return item.content_rating
        if field_name == "Date Added":
            return item.date_added or 0
        if field_name == "Last Played":
            return item.last_played or 0
        if field_name == "Duration":
            return int((item.duration_ms or 0) / 60000)
        return ""

    def rule_matches(self, item: PlaylistItem, field_name: str, op: str, value: str) -> bool:
        if not field_name or not value.strip():
            return True
        actual = self.item_field_value(item, field_name)
        value = value.strip()
        if field_name in {"Year", "Position", "Date Added", "Last Played", "Duration"}:
            try:
                actual_num = int(actual or 0)
            except Exception:
                actual_num = 0
            if op == "between":
                parts = [p.strip() for p in value.replace("-", ",").split(",") if p.strip()]
                if len(parts) != 2:
                    return False
                try:
                    low, high = int(parts[0]), int(parts[1])
                except Exception:
                    return False
                return low <= actual_num <= high
            try:
                target = int(value)
            except Exception:
                return False
            return {"equals": actual_num == target, ">=": actual_num >= target, "<=": actual_num <= target, ">": actual_num > target, "<": actual_num < target}.get(op, False)

        if field_name == "Genre":
            actual_list = [normalized_compare(g) for g in item.genres]
            requested = [normalized_compare(v) for v in value.replace(";", ",").split(",") if normalized_compare(v)]
            if op == "any of":
                return any(r in actual_list for r in requested)
            if op == "none of":
                return all(r not in actual_list for r in requested)
        actual_text = normalized_compare(str(actual))
        value_text = normalized_compare(value)
        if op == "equals":
            return actual_text == value_text
        if op == "starts with":
            return actual_text.startswith(value_text)
        if op == "ends with":
            return actual_text.endswith(value_text)
        if op == "none of":
            return value_text not in actual_text
        return value_text in actual_text

    def apply_smart_filter(self):
        playlist_type = self.smart_playlist_type_var.get()
        type_map = {"Movie": {"movie", "video"}, "TV Show": {"show", "episode", "video"}, "Music": {"track", "audio", "album", "artist"}}
        allowed = type_map.get(playlist_type, {"movie", "video"})
        filtered = []
        for item in self.all_items:
            item_type = (item.item_type or "video").lower()
            if allowed and item_type not in allowed:
                if playlist_type == "TV Show" and item_type == "video":
                    pass
                elif playlist_type == "Movie" and item_type == "video":
                    pass
                else:
                    continue
            ok = True
            for idx in range(1, 4):
                if not self.rule_matches(item, self.rule_field_vars[idx].get(), self.rule_op_vars[idx].get(), self.rule_value_vars[idx].get()):
                    ok = False
                    break
            if ok:
                filtered.append(item)
        self.filtered_items = filtered
        self.populate_tree(self.filtered_items)
        self.search_result_var.set(f"Filtered: {len(filtered)} / {len(self.all_items)}")

    def clear_smart_filter(self):
        self.smart_playlist_type_var.set("Movie")
        for idx in range(1, 4):
            self.rule_field_vars[idx].set("")
            self.rule_op_vars[idx].set("contains")
            self.rule_value_vars[idx].set("")
        self.group_by_var.set("None")
        self.filter_preset_var.set("")
        self.filtered_items = list(self.all_items)
        self.on_filter_type_changed()

    def clear_cut_buffer(self):
        self.cut_item_ids = []
        self.cut_item_rating_keys = []
        self.cut_title_var.set("Move buffer: empty")
        self.set_status("Move buffer cleared.")

    def clear_copy_buffer(self):
        self.copy_item_ids = []
        self.copy_item_rating_keys = []
        self.copy_items = []
        self.copy_source_server_name = ""
        self.skip_db_backup_prompt_for_copy_buffer_session = False
        self.copy_title_var.set("Copy buffer: empty")
        self.set_status("Copy buffer cleared.")


    def set_last_playlist_backup(self, backup_path: Optional[Path], label: str = ""):
        if not backup_path:
            return
        try:
            self.last_playlist_backup_path = Path(backup_path)
        except Exception:
            return
        self.last_playlist_backup_label = label or self.playlist_title_var.get().strip()
        self.log_event(f"Undo point updated: {self.last_playlist_backup_path}", always_show=False)

    def on_undo_shortcut(self, event=None):
        self.undo_last_playlist_change()
        return "break"

    def undo_last_playlist_change(self):
        if self.active_task_count > 0:
            messagebox.showwarning("Task already in progress", "Task already in progress. Please wait for the current operation to finish.")
            return
        if not self.require_playlist_loaded():
            return
        if not self.last_playlist_backup_path or not Path(self.last_playlist_backup_path).exists():
            messagebox.showwarning("Nothing to Undo", "No playlist undo point is available yet.")
            return
        title = self.playlist_title_var.get().strip()
        backup_name = Path(self.last_playlist_backup_path).name
        if not self.should_confirm(
            f"Undo the last playlist change by restoring from:\n\n{backup_name}\n\n"
            "This will change the current playlist order/membership."
        ):
            return
        playlist_key = self.playlist_rating_key

        def task():
            self.update_task_progress(f"Undoing last playlist change from {backup_name}...", always_show=True)
            return self.server.restore_from_backup(title, playlist_key, self.all_items, Path(self.last_playlist_backup_path))

        def done(result, db_backup_path):
            items, moved_count, skipped_count, warnings, safety_backup = result
            self.all_items = items
            self.filtered_items = list(self.all_items)
            self.on_filter_type_changed()
            self.set_last_playlist_backup(safety_backup, title)
            status = f"Undo complete. Moved: {moved_count}, Skipped: {skipped_count}. Safety backup: {safety_backup}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            if warnings:
                status += " Warnings present."
                messagebox.showwarning("Undo Warnings", "\n".join(warnings))
            self.set_status(status)

        journal_context = {
            "operation_type": "undo_playlist_change",
            "server_name": self.server.name if self.server else self.server_name_var.get().strip(),
            "playlist_title": title,
            "playlist_rating_key": self.playlist_rating_key or "",
            "create_safety_backup": True,
            "playlist_items": list(self.all_items),
            "notes": f"Undo restore from {backup_name}",
        }
        self.run_db_guarded_task("Undoing last playlist change...", self.server, task, done, journal_context=journal_context)

    def ping_server(self):
        if not self.server:
            return
        self.run_task("Pinging server...", self.server.ping, on_success=lambda _r: self.set_status(f"Connected to {self.server.base_url}"))

    def load_playlists(self):
        if not self.server:
            return

        def task():
            self.server.ping()
            return self.server.get_playlists()

        def done(playlists):
            self.playlist_list = playlists
            titles = [str(p.get("title", "")) for p in playlists]
            self.playlist_combo["values"] = titles
            if titles:
                current = self.playlist_title_var.get().strip()
                if current not in titles:
                    self.playlist_title_var.set(titles[0])
                self.refresh_playlist()
            else:
                self.set_status("No playlists found on selected server.")
                self.playlist_title_var.set("")
                self.filtered_items = []
                self.populate_tree([])
                self.search_result_var.set("Filtered: 0")

        self.run_task("Loading playlists...", task, done)

    def refresh_playlist(self):
        if not self.server:
            return
        title = self.playlist_title_var.get().strip()
        if not title:
            messagebox.showwarning("Missing Playlist", "Choose a playlist first.")
            return

        def task():
            playlist = self.server.find_playlist(title)
            if not playlist:
                raise PlexError(f"Playlist not found on {self.server.name}: {title}")
            items = self.server.get_playlist_items(str(playlist["ratingKey"]))
            return str(playlist["ratingKey"]), items

        def done(result):
            self.playlist_rating_key, self.all_items = result
            self.sort_column = "position"
            self.sort_reverse = False
            self.filtered_items = list(self.all_items)
            self.on_filter_type_changed()
            timestamp = datetime.now().strftime("%I:%M:%S %p").lstrip("0")
            self.set_status(f"Loaded playlist '{title}' on {self.server_name_var.get()} with {len(self.all_items)} items at {timestamp}.")

        self.run_task(f"Loading playlist '{title}'...", task, done)

    def require_playlist_loaded(self, silent: bool = False) -> bool:
        if not self.server or not self.playlist_rating_key:
            if not silent:
                messagebox.showwarning("Not Loaded", "Load the playlist first.")
            return False
        return True

    def backup_playlist(self):
        if not self.require_playlist_loaded():
            return
        title = self.playlist_title_var.get().strip()
        self.run_task("Writing backup...", lambda: (self.update_task_progress(f"Creating playlist backup for {title}...", always_show=True) or self.server.export_backup(title, self.all_items)), on_success=lambda path: self.set_status(f"Backup written to {path}"))

    def export_csv(self):
        if not self.require_playlist_loaded():
            return
        title = self.playlist_title_var.get().strip()
        self.run_task("Exporting CSV...", lambda: (self.update_task_progress(f"Exporting CSV for {title}...", always_show=True) or self.server.export_csv(title, self.all_items)), on_success=lambda path: self.set_status(f"CSV written to {path}"))

    def import_csv(self):
        if not self.require_playlist_loaded():
            return
        csv_path = filedialog.askopenfilename(
            title="Select CSV file",
            initialdir=str(self.server.export_dir()),
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
        )
        if not csv_path:
            return

        def task():
            self.update_task_progress(f"Reading CSV from {Path(csv_path).name}...", always_show=True)
            rows = self.server.load_csv_order(Path(csv_path))
            if len(rows) > len(self.all_items):
                raise PlexError(f"Imported CSV has {len(rows)} rows, but playlist only has {len(self.all_items)} items.")
            return Path(csv_path), rows

        def done(result):
            path, rows = result
            self.imported_csv_path = path
            self.imported_csv_rows = rows
            self.imported_csv_var.set(f"Imported CSV: {path.name} ({len(rows)}/{len(self.all_items)} rows)")
            self.set_status(f"Imported CSV '{path.name}' with {len(rows)} rows.")

        self.run_task("Importing CSV...", task, done)

    def apply_imported_csv(self):
        if not self.require_playlist_loaded():
            return
        if not self.imported_csv_rows or not self.imported_csv_path:
            messagebox.showwarning("No CSV Imported", "Import a CSV file first.")
            return
        if not self.should_confirm(f"Apply imported CSV order from '{self.imported_csv_path.name}' to the current playlist?"):
            return

        title = self.playlist_title_var.get().strip()
        playlist_key = self.playlist_rating_key

        def task():
            self.update_task_progress(f"Applying imported CSV to {title}...", always_show=True)
            self.server.bind_playlist_context(playlist_key)
            return self.server.apply_order_rows(title, playlist_key, self.all_items, self.imported_csv_rows)

        def done(result, db_backup_path):
            items, moved_count, skipped_count, warnings, backup_path = result
            self.all_items = items
            self.filtered_items = list(self.all_items)
            self.on_filter_type_changed()
            status = f"Applied imported CSV. Moved: {moved_count}, Skipped: {skipped_count}. Backup: {backup_path}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            if warnings:
                status += " Warnings present."
                messagebox.showwarning("Import Warnings", "\n".join(warnings))
            self.set_status(status)

        journal_context = {"operation_type": "import_csv", "server_name": self.server.name, "playlist_title": title, "playlist_rating_key": playlist_key, "create_safety_backup": True, "playlist_items": list(self.all_items)}
        self.run_db_guarded_task("Applying imported CSV order...", self.server, task, done, journal_context=journal_context)

    def _candidate_label(self, candidate: Dict[str, Any]) -> str:
        title = str(candidate.get("title", "") or "<untitled>")
        year = candidate.get("year")
        item_type = str(candidate.get("type", "") or "").lower()
        parts = [title]
        if year:
            parts.append(f"({year})")
        if item_type:
            parts.append(f"[{item_type}]")
        return " ".join(parts)

    def _candidate_allowed_for_item(self, source_item: Dict[str, Any], candidate: Dict[str, Any]) -> bool:
        source_type = str(source_item.get("item_type", "") or "").lower()
        candidate_type = str(candidate.get("type", "") or "").lower()
        if source_type in {"movie", "video"}:
            return candidate_type in {"movie", "video"}
        if source_type in {"show", "episode"}:
            return candidate_type in {"show", "episode"}
        if source_type in {"track", "audio", "album", "artist"}:
            return candidate_type in {"track", "audio", "album", "artist"}
        return True

    def prompt_reconcile_item(self, dest_server: PlexServer, source_item: Dict[str, Any], playlist_name: str) -> Optional[str]:
        title = str(source_item.get("title", "") or "").strip()
        if not title:
            return None
        candidates = [c for c in dest_server.candidate_results_for_item(PlaylistItem(position=0, title=title, year=source_item.get("year"), rating_key="", playlist_item_id="", item_type=str(source_item.get("item_type", "video") or "video"), artist=str(source_item.get("artist", "") or ""), album=str(source_item.get("album", "") or ""))) if self._candidate_allowed_for_item(source_item, c)]
        status = str(source_item.get("status", "") or "").strip().lower()

        # Missing items with zero candidates should not open a blank reconcile dialog.
        if status == "missing" and not candidates:
            return None

        dialog = tk.Toplevel(self.root)
        dialog.title("Reconcile Match")
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.geometry("720x420")
        dialog.minsize(680, 380)
        dialog.update_idletasks()
        width = 720
        height = 420
        x = max(0, (dialog.winfo_screenwidth() - width) // 2)
        y = max(0, (dialog.winfo_screenheight() - height) // 2)
        dialog.geometry(f"{width}x{height}+{x}+{y}")
        dialog.columnconfigure(0, weight=1)
        dialog.rowconfigure(1, weight=1)

        desc = f"Playlist: {playlist_name}\nIssue: {source_item.get('status', 'unresolved').title()}\nSource: {source_item.get('display', title)}\nChoose the correct match on {dest_server.name}, or skip."
        ttk.Label(dialog, text=desc, justify="left", wraplength=660).grid(row=0, column=0, sticky="ew", padx=12, pady=(12, 8))

        frame = ttk.Frame(dialog, padding=(12, 0, 12, 0))
        frame.grid(row=1, column=0, sticky="nsew")
        frame.columnconfigure(0, weight=1)
        frame.rowconfigure(0, weight=1)

        listbox = tk.Listbox(frame, exportselection=False)
        listbox.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(frame, orient="vertical", command=listbox.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        listbox.configure(yscrollcommand=scroll.set)

        candidate_map: List[Dict[str, Any]] = []
        for cand in candidates:
            candidate_map.append(cand)
            listbox.insert(tk.END, self._candidate_label(cand))
        if candidate_map:
            listbox.selection_set(0)

        selected: Dict[str, Any] = {"rating_key": None}

        def use_selected():
            sel = listbox.curselection()
            if not sel:
                messagebox.showwarning("Choose Match", "Select a destination item or click Skip.", parent=dialog)
                return
            selected["rating_key"] = str(candidate_map[int(sel[0])].get("rating_key", "") or "")
            dialog.destroy()

        def skip_item():
            selected["rating_key"] = None
            dialog.destroy()

        btns = ttk.Frame(dialog, padding=12)
        btns.grid(row=2, column=0, sticky="e")
        ttk.Button(btns, text="Skip", command=skip_item).grid(row=0, column=0, padx=4)
        ttk.Button(btns, text="Use Selected Match", command=use_selected).grid(row=0, column=1, padx=4)

        if not candidate_map:
            ttk.Label(dialog, text="No candidates found on the destination server.", foreground="firebrick").grid(row=3, column=0, sticky="w", padx=12, pady=(0, 12))

        self.root.wait_window(dialog)
        value = selected.get("rating_key")
        return str(value) if value else None

    def reconcile_unresolved_items(self, dest_server: PlexServer, playlist_name: str, unresolved: List[Dict[str, Any]]) -> Tuple[int, int]:
        if not unresolved:
            return 0, 0

        # Only show the interactive reconcile flow for items that are actionable:
        # ambiguous matches or missing items that actually have candidate matches.
        actionable: List[Dict[str, Any]] = []
        non_actionable = 0
        for item in unresolved:
            status = str(item.get("status", "") or "").strip().lower()
            candidates = item.get("candidates") or []
            if status == "ambiguous" or candidates:
                actionable.append(item)
            else:
                non_actionable += 1

        if not actionable:
            return 0, len(unresolved)

        if not messagebox.askyesno("Reconcile Matches", f"{len(actionable)} item(s) need review for '{playlist_name}'.\n\nWould you like to reconcile them now?", parent=self.root):
            return 0, len(unresolved)

        chosen_keys: List[str] = []
        skipped = non_actionable
        for item in actionable:
            rating_key = self.prompt_reconcile_item(dest_server, item, playlist_name)
            if rating_key:
                chosen_keys.append(rating_key)
            else:
                skipped += 1

        if chosen_keys:
            self._add_rating_keys_to_playlist_on_server(dest_server, playlist_name, chosen_keys, self.copy_items or self.all_items)
        return len(chosen_keys), skipped

    def _add_rating_keys_to_playlist_on_server(self, server: PlexServer, playlist_name: str, rating_keys: List[str], reference_items: Optional[List[PlaylistItem]] = None) -> str:
        playlist = server.find_playlist(playlist_name)
        if playlist:
            server.add_items_to_playlist(str(playlist["ratingKey"]), rating_keys)
            return "added"
        media_items = reference_items or []
        media_type = playlist_media_type(media_items)
        server.create_playlist_from_rating_keys(playlist_name, rating_keys, media_type)
        return "created"

    def maybe_trigger_pretransfer_refresh(self, source_server: PlexServer, dest_server: PlexServer, playlist_type: str, refresh_mode: str) -> None:
        mode = (refresh_mode or "none").strip().lower()
        if mode == "none":
            return
        force = mode == "deep_refresh_both"
        label = "deep refresh" if force else "scan refresh"
        self.log_event(f"Triggering pre-transfer {label} for {source_server.name} and {dest_server.name}...")
        self._server_progress(f"Triggering pre-transfer {label}...")
        src_count = source_server.refresh_relevant_library_sections(playlist_type, force=force)
        dst_count = dest_server.refresh_relevant_library_sections(playlist_type, force=force)
        self.log_event(
            f"Triggered {label} for playlist type '{playlist_type}': {source_server.name} sections={src_count}, {dest_server.name} sections={dst_count}."
        )
        self._server_progress(f"Triggered pre-transfer {label}: {source_server.name}={src_count}, {dest_server.name}={dst_count}")

    def copy_playlist_to_server(self):
        if not self.require_playlist_loaded():
            return

        server_names = list(self.server_map.keys())
        dialog = CopyPlaylistDialog(self.root, self.server_name_var.get(), self.playlist_title_var.get().strip(), server_names)
        self.root.wait_window(dialog)
        if not dialog.result:
            return

        dest_server_name = dialog.result["dest_server"]
        playlist_name = dialog.result["playlist_name"]
        refresh_mode = dialog.result.get("refresh_mode", "none")

        if dest_server_name == self.server_name_var.get():
            if not messagebox.askyesno("Same Server", "Destination server is the same as the source. Continue anyway?"):
                return

        dest_server = PlexServer(self.server_map[dest_server_name], self.config)
        dest_server.progress_callback = self._server_progress

        existing = None
        try:
            existing = dest_server.find_playlist(playlist_name)
        except Exception:
            pass

        overwrite_existing = False
        if existing:
            overwrite_existing = messagebox.askyesno(
                "Playlist Exists",
                f"The destination server already has a playlist named '{playlist_name}'.\n\nOverwrite it?"
            )
            if not overwrite_existing:
                self.set_status("Copy cancelled because destination playlist already exists.")
                return

        selected = self.selected_items()
        if selected:
            source_items = list(selected)
        elif self.filtered_items and len(self.filtered_items) != len(self.all_items):
            source_items = list(self.filtered_items)
        else:
            source_items = list(self.all_items)

        def task():
            self.maybe_trigger_pretransfer_refresh(self.server, dest_server, self.smart_playlist_type_var.get(), refresh_mode)
            self.update_task_progress(
                f"Starting copy path: {self.server.name} -> {dest_server.name} | playlist='{playlist_name}' | items={len(source_items)}",
                always_show=True,
            )
            return dest_server.copy_playlist_from_source(
                source_items,
                playlist_name,
                overwrite_existing,
                source_server_name=self.server.name,
            )

        def done(result, db_backup_path):
            matched_count, missing_count, ambiguous_count, missing, ambiguous, unresolved, verification = result
            reconciled_count = 0
            skipped_count = 0
            notes = []
            if missing:
                preview = "\n".join(missing[:20])
                if missing_count > 20:
                    preview += f"\n...and {missing_count - 20} more."
                notes.append("Missing:\n" + preview)
            if ambiguous:
                preview = "\n".join(ambiguous[:20])
                if ambiguous_count > 20:
                    preview += f"\n...and {ambiguous_count - 20} more."
                notes.append("Ambiguous:\n" + preview)
            if notes:
                messagebox.showwarning("Copy Playlist Report", "\n\n".join(notes))
                reconciled_count, skipped_count = self.reconcile_unresolved_items(dest_server, playlist_name, unresolved)
            final_added = matched_count + reconciled_count
            status = f"Copied {len(source_items)} item(s) from {self.server.name} to {dest_server_name}. Matched: {matched_count}, Missing: {missing_count}, Ambiguous: {ambiguous_count}. Added total: {final_added}."
            if reconciled_count:
                status += f" Reconciled: {reconciled_count}."
            if skipped_count:
                status += f" Unresolved skipped: {skipped_count}."
            if db_backup_path:
                status += f" DB backup: {db_backup_path}"
            self.set_status(status)

        journal_note = f"Source server: {self.server_name_var.get().strip()}"
        if refresh_mode and refresh_mode != "none":
            journal_note += f" | Pre-transfer refresh: {refresh_mode}"
        journal_context = {"operation_type": "copy_playlist_to_server", "server_name": dest_server.name, "playlist_title": playlist_name, "notes": journal_note}
        self.run_db_guarded_task(f"Copying playlist to {dest_server_name}...", dest_server, task, done, journal_context=journal_context)

    def run_mutation(self, prompt: str, func, success_builder, preserve_rating_keys: Optional[List[str]] = None):
        if not self.require_playlist_loaded():
            return
        if not self.should_confirm(prompt):
            return
        try:
            preserve_rating_keys = preserve_rating_keys or []
        except Exception:
            preserve_rating_keys = []

        def done(result, db_backup_path):
            items, backup_path = result
            self.all_items = items
            self.filtered_items = list(self.all_items)
            self.populate_tree(self.filtered_items, selected_rating_keys=preserve_rating_keys)
            self.apply_smart_filter()
            self.set_last_playlist_backup(backup_path, self.playlist_title_var.get().strip())
            message = success_builder(backup_path)
            if db_backup_path:
                message += f" Plex DB backup: {db_backup_path}"
            self.set_status(message)

        journal_context = {
            "operation_type": "playlist_write",
            "server_name": self.server.name if self.server else self.server_name_var.get().strip(),
            "playlist_title": self.playlist_title_var.get().strip(),
            "playlist_rating_key": self.playlist_rating_key or "",
            "create_safety_backup": True,
            "playlist_items": list(self.all_items),
        }
        self.run_db_guarded_task("Applying change...", self.server, func, done, journal_context=journal_context)

    def move_to_position(self):
        items = self.selected_items()
        if len(items) != 1:
            messagebox.showwarning("Select One Title", "Select exactly one title for Move To Slot.")
            return
        item = items[0]
        raw_pos = self.move_position_var.get().strip()
        if not raw_pos.isdigit():
            messagebox.showwarning("Invalid Position", "Enter a numeric target slot.")
            return
        target_position = int(raw_pos)
        title = self.playlist_title_var.get().strip()
        playlist_key = self.playlist_rating_key

        def task():
            self.server.bind_playlist_context(playlist_key)
            return self.server.apply_move_to_position(title, self.all_items, item.playlist_item_id, target_position)

        self.run_mutation(
            f"Move '{item.title}' to slot {target_position}?",
            task,
            lambda backup_path: f"Moved '{item.title}' to slot {target_position}. Backup: {backup_path}",
            preserve_rating_keys=[item.rating_key],
        )

    def move_up_one(self):
        items = self.selected_items()
        if len(items) != 1:
            messagebox.showwarning("Select One Title", "Select exactly one title for Move Up One.")
            return
        item = items[0]
        if item.position <= 1:
            self.set_status(f"'{item.title}' is already at the top.")
            return
        title = self.playlist_title_var.get().strip()
        playlist_key = self.playlist_rating_key

        def task():
            self.server.bind_playlist_context(playlist_key)
            return self.server.apply_move_to_position(title, self.all_items, item.playlist_item_id, item.position - 1)

        self.run_mutation(
            f"Move '{item.title}' up one slot?",
            task,
            lambda backup_path: f"Moved '{item.title}' up one slot. Backup: {backup_path}",
            preserve_rating_keys=[item.rating_key],
        )

    def move_down_one(self):
        items = self.selected_items()
        if len(items) != 1:
            messagebox.showwarning("Select One Title", "Select exactly one title for Move Down One.")
            return
        item = items[0]
        if item.position >= len(self.all_items):
            self.set_status(f"'{item.title}' is already at the bottom.")
            return
        title = self.playlist_title_var.get().strip()
        playlist_key = self.playlist_rating_key

        def task():
            self.server.bind_playlist_context(playlist_key)
            return self.server.apply_move_to_position(title, self.all_items, item.playlist_item_id, item.position + 1)

        self.run_mutation(
            f"Move '{item.title}' down one slot?",
            task,
            lambda backup_path: f"Moved '{item.title}' down one slot. Backup: {backup_path}",
            preserve_rating_keys=[item.rating_key],
        )

    def cut_selected_block(self):
        items = self.selected_items()
        if not items:
            messagebox.showwarning("Select Title(s)", "Select one or more titles first.")
            return
        self.cut_item_ids = [item.playlist_item_id for item in items]
        self.cut_item_rating_keys = [item.rating_key for item in items]

        if len(items) == 1:
            self.cut_title_var.set(f"Move buffer: {items[0].display}")
            self.set_status(f"Stored '{items[0].title}' in the move buffer.")
        else:
            self.cut_title_var.set(f"Move buffer: {len(items)} items")
            self.set_status(f"Stored {len(items)} selected item(s) in the move buffer.")


    def copy_selected_block(self):
        items = self.selected_items()
        if not items:
            messagebox.showwarning("Select Title(s)", "Select one or more titles first.")
            return

        if not self.copy_items:
            self.skip_db_backup_prompt_for_copy_buffer_session = False

        existing_keys = {(item.rating_key, item.title, item.year, self.copy_source_server_name) for item in self.copy_items}
        added = 0
        for item in items:
            dedupe_key = (item.rating_key, item.title, item.year, self.server.name if self.server else "")
            if dedupe_key in existing_keys:
                continue
            self.copy_item_ids.append(item.playlist_item_id)
            self.copy_item_rating_keys.append(item.rating_key)
            self.copy_items.append(deepcopy(item))
            existing_keys.add(dedupe_key)
            added += 1

        if not self.copy_source_server_name:
            self.copy_source_server_name = self.server.name if self.server else ""

        total = len(self.copy_items)
        if total == 0:
            self.copy_title_var.set("Copy buffer: empty")
            self.set_status("No new titles were added to the copy buffer.")
            return
        if total == 1:
            self.copy_title_var.set(f"Copy buffer: {self.copy_items[0].display}")
        else:
            self.copy_title_var.set(f"Copy buffer: {total} items")

        if added == 0:
            self.set_status("Selected titles were already in the copy buffer.")
        elif added == 1:
            self.set_status(f"Added 1 title to the copy buffer. Total buffered: {total}.")
        else:
            self.set_status(f"Added {added} titles to the copy buffer. Total buffered: {total}.")

    def prompt_playlist_name(self, title: str, prompt: str, initial: str = "") -> Optional[str]:
        value = simpledialog.askstring(title, prompt, initialvalue=initial, parent=self.root)
        if value is None:
            return None
        value = value.strip()
        return value or None

    def get_server_playlist_names(self, server_name: str) -> List[str]:
        server_cfg = self.server_map.get(server_name)
        if not server_cfg:
            return []
        server = PlexServer(server_cfg, self.config)
        server.progress_callback = self._server_progress
        server.ping()
        playlists = server.get_playlists()
        if self.server and self.server.name == server_name:
            self.playlist_list = list(playlists)
            titles = [str(p.get("title", "") or "").strip() for p in playlists if str(p.get("title", "") or "").strip()]
            self.playlist_combo["values"] = titles
            current = self.playlist_title_var.get().strip()
            if current and current not in titles:
                self.playlist_title_var.set("")
            return titles
        return [str(p.get("title", "") or "").strip() for p in playlists if str(p.get("title", "") or "").strip()]

    def prompt_copy_buffer_destination(self) -> Optional[Dict[str, str]]:
        current_playlist = self.playlist_title_var.get().strip()
        current_server = self.server.name if self.server else self.server_name_var.get().strip()
        dialog = PlaylistTargetDialog(self.root, current_server, current_playlist, list(self.server_map.keys()), self.get_server_playlist_names)
        self.root.wait_window(dialog)
        return dialog.result

    def add_rating_keys_to_playlist_by_name(self, playlist_name: str, rating_keys: List[str], target_server: Optional[PlexServer] = None, playlist_cache: Optional[List[Dict[str, Any]]] = None, media_items: Optional[List[PlaylistItem]] = None) -> str:
        target_server = target_server or self.server
        if target_server is None:
            raise PlexError("No destination server is active.")
        cache = playlist_cache if playlist_cache is not None else (self.playlist_list if target_server is self.server else [])
        playlist = None
        normalized_name = playlist_name.strip().lower()
        for entry in cache or []:
            if str(entry.get("title", "")).strip().lower() == normalized_name:
                playlist = entry
                break
        if playlist is None:
            playlist = target_server.find_playlist(playlist_name)
            if playlist and playlist_cache is not None and not any(str(p.get("ratingKey", "")) == str(playlist.get("ratingKey", "")) for p in playlist_cache):
                playlist_cache.append(playlist)
            elif playlist and target_server is self.server and not any(str(p.get("ratingKey", "")) == str(playlist.get("ratingKey", "")) for p in self.playlist_list):
                self.playlist_list.append(playlist)
        if playlist:
            target_server.add_items_to_playlist(str(playlist["ratingKey"]), rating_keys)
            return "added"
        source_media_items = media_items if media_items is not None else [item for item in self.all_items if item.rating_key in set(rating_keys)]
        media_type = playlist_media_type(source_media_items)
        target_server.create_playlist_from_rating_keys(playlist_name, rating_keys, media_type)
        return "created"

    def add_selected_to_playlist(self):
        items = self.selected_items()
        if not items:
            messagebox.showwarning("Select Title(s)", "Select one or more titles first.")
            return
        playlist_name = self.prompt_playlist_name("Add Selected To Playlist", "Destination playlist name:")
        if not playlist_name:
            return
        rating_keys = [item.rating_key for item in items]
        def task():
            return self.add_rating_keys_to_playlist_by_name(playlist_name, rating_keys)
        def done(result):
            verb = "Created" if result == "created" else "Added to"
            self.set_status(f"{verb} playlist '{playlist_name}' from current selection.")
        journal_context = {"operation_type": "add_selected_to_playlist", "server_name": self.server.name, "playlist_title": playlist_name}
        self.run_task(f"Adding selected titles to '{playlist_name}'...", task, done, journal_context=journal_context)

    def add_copy_buffer_to_playlist(self):
        if not self.copy_items:
            selected = self.selected_items()
            if not selected:
                messagebox.showwarning("Copy Buffer Empty", "Copy one or more titles first.")
                return
            self.copy_selected_block()
            if not self.copy_items:
                return
        target = self.prompt_copy_buffer_destination()
        if not target:
            return
        playlist_name = str(target.get("playlist_name", "") or "").strip()
        target_server_name = str(target.get("target_server_name", "") or "").strip()
        if not playlist_name or not target_server_name:
            return
        source_server_name = self.copy_source_server_name or ""
        target_server_cfg = self.server_map.get(target_server_name)
        if not target_server_cfg:
            messagebox.showerror("Destination Server", f"Unknown destination server: {target_server_name}")
            return
        target_server = self.server if self.server and self.server.name == target_server_name else PlexServer(target_server_cfg, self.config)
        target_playlist_cache = self.playlist_list if target_server is self.server else []
        same_server = bool(target_server and source_server_name and target_server.name == source_server_name)

        def task():
            if target_server is not self.server:
                target_server.ping()
                target_playlist_cache[:] = target_server.get_playlists()
            if same_server:
                rating_keys = [item.rating_key for item in self.copy_items if item.rating_key]
                return self.add_rating_keys_to_playlist_by_name(playlist_name, rating_keys, target_server=target_server, playlist_cache=target_playlist_cache, media_items=list(self.copy_items)), [], [], [], []

            matched_keys: List[str] = []
            missing: List[str] = []
            ambiguous: List[str] = []
            unresolved: List[Dict[str, Any]] = []
            total = len(self.copy_items)
            target_server._candidate_cache = {}
            target_server._relevant_section_cache = {}
            for index, item in enumerate(self.copy_items, start=1):
                self._server_progress(f"Resolving copy buffer item {index}/{total} on destination server {target_server.name}: {item.title}")
                match_key, status, candidates, match_reason = target_server.match_item_robust(item)
                if match_key:
                    matched_keys.append(match_key)
                elif status == "ambiguous":
                    ambiguous.append(item.display)
                    unresolved.append({"status": "ambiguous", "display": item.display, "title": item.title, "year": item.year, "item_type": item.item_type, "artist": item.artist, "album": item.album, "candidates": candidates[:10] if candidates else [], "match_reason": match_reason})
                else:
                    missing.append(item.display)
                    unresolved.append({"status": "missing", "display": item.display, "title": item.title, "year": item.year, "item_type": item.item_type, "artist": item.artist, "album": item.album, "candidates": candidates[:10] if candidates else [], "match_reason": match_reason})

            if not matched_keys and not unresolved:
                raise PlexError("No matching titles from the copy buffer were found on the destination server.")

            action = None
            if matched_keys:
                action = self.add_rating_keys_to_playlist_by_name(playlist_name, matched_keys, target_server=target_server, playlist_cache=target_playlist_cache, media_items=list(self.copy_items))
            return action, matched_keys, missing, ambiguous, unresolved

        def done(result):
            action, matched_keys, missing, ambiguous, unresolved = result
            reconciled_count = 0
            skipped_count = 0
            notes = []
            if missing:
                preview = "\n".join(missing[:20])
                if len(missing) > 20:
                    preview += f"\n...and {len(missing) - 20} more."
                notes.append("Missing:\n" + preview)
            if ambiguous:
                preview = "\n".join(ambiguous[:20])
                if len(ambiguous) > 20:
                    preview += f"\n...and {len(ambiguous) - 20} more."
                notes.append("Ambiguous:\n" + preview)
            if notes:
                messagebox.showwarning("Copy Buffer Report", "\n\n".join(notes))
                reconciled_count, skipped_count = self.reconcile_unresolved_items(target_server, playlist_name, unresolved)
            total_added = len(matched_keys) + reconciled_count
            if total_added == 0:
                self.set_status(f"No copy buffer items were added to '{playlist_name}' on {target_server_name}.")
            else:
                verb = "Created" if action == "created" else "Added to"
                self.set_status(f"{verb} playlist '{playlist_name}' on {target_server_name} from the copy buffer. Added: {total_added}. Reconciled: {reconciled_count}. Skipped: {skipped_count}.")

        journal_context = {
            "operation_type": "add_copy_buffer_to_playlist",
            "server_name": target_server_name,
            "playlist_title": playlist_name,
            "source_server_name": source_server_name,
        }
        self.run_task(f"Adding copy buffer to '{playlist_name}' on {target_server_name}...", task, done, journal_context=journal_context)

    def new_playlist_from_selected(self):
        items = self.selected_items()
        if not items:
            messagebox.showwarning("Select Title(s)", "Select one or more titles first.")
            return
        name = self.prompt_playlist_name("New Playlist From Selected", "Enter new playlist name:")
        if not name:
            return
        rating_keys = [item.rating_key for item in items]
        media_type = playlist_media_type(items)
        def task():
            self.server.create_playlist_from_rating_keys(name, rating_keys, media_type)
            return name
        journal_context = {"operation_type": "create_playlist_from_selected", "server_name": self.server.name, "playlist_title": name}
        self.run_task("Creating playlist from selected titles...", task, on_success=lambda nm: self.set_status(f"Created new playlist '{nm}' from current selection."), journal_context=journal_context)

    def export_selected_to_csv(self):
        items = self.selected_items()
        if not items:
            messagebox.showwarning("Select Title(s)", "Select one or more titles first.")
            return
        name = simpledialog.askstring("Export Selection", "Name for exported selection:", parent=self.root) or "selected_titles"
        self.run_task("Exporting selected titles...", lambda: self.server.export_csv(name, items), on_success=lambda path: self.set_status(f"Selected titles exported to {path}"))

    def move_selected_relative(self, selected_playlist_item_ids: List[str], anchor: PlaylistItem, where: str):
        if not selected_playlist_item_ids:
            return
        title = self.playlist_title_var.get().strip()
        playlist_key = self.playlist_rating_key
        count = len(selected_playlist_item_ids)
        selected_id_set = set(selected_playlist_item_ids)
        selected_keys = [item.rating_key for item in self.all_items if item.playlist_item_id in selected_id_set]

        # Fast path: a single drag/drop move should use the same direct one-item reorder
        # logic as the restored fast build instead of going through block-reorder logic.
        if count == 1:
            moving_id = selected_playlist_item_ids[0]
            work = [item for item in self.all_items if item.playlist_item_id != moving_id]
            anchor_index = next((i for i, item in enumerate(work) if item.playlist_item_id == anchor.playlist_item_id), None)
            if anchor_index is None:
                messagebox.showwarning("Invalid Move", "Anchor item was not found.")
                return
            target_position = anchor_index + 1 if where == "before" else anchor_index + 2

            def task():
                self.server.bind_playlist_context(playlist_key)
                return self.server.apply_move_to_position(title, self.all_items, moving_id, target_position)

            prompt = f"Move selected item {where} '{anchor.title}'?"
            success = lambda backup_path: f"Moved selected item {where} '{anchor.title}'. Backup: {backup_path}"
            self.run_mutation(prompt, task, success, preserve_rating_keys=selected_keys)
            return

        def task():
            self.server.bind_playlist_context(playlist_key)
            return self.server.apply_move_block_relative(title, self.all_items, selected_playlist_item_ids, anchor.playlist_item_id, where)

        prompt = f"Move {count} selected item(s) {where} '{anchor.title}'?"
        success = lambda backup_path: f"Moved {count} selected item(s) {where} '{anchor.title}'. Backup: {backup_path}"

        self.run_mutation(prompt, task, success, preserve_rating_keys=selected_keys)

    def paste_cut_block(self, where: str):
        if not self.cut_item_ids:
            messagebox.showwarning("Move Buffer Empty", "Store one or more titles in the move buffer first.")
            return
        anchor = self.selected_item()
        if not anchor:
            messagebox.showwarning("Select Anchor", "Select the anchor title in the list.")
            return
        if anchor.playlist_item_id in set(self.cut_item_ids):
            messagebox.showwarning("Invalid Paste", "Anchor cannot be inside the selected items.")
            return

        title = self.playlist_title_var.get().strip()
        playlist_key = self.playlist_rating_key
        count = len(self.cut_item_ids)

        def task():
            self.server.bind_playlist_context(playlist_key)
            return self.server.apply_move_block_relative(title, self.all_items, self.cut_item_ids, anchor.playlist_item_id, where)

        if count == 1:
            prompt = f"Paste selected item {where} '{anchor.title}'?"
            success = lambda backup_path: f"Pasted selected item {where} '{anchor.title}'. Backup: {backup_path}"
        else:
            prompt = f"Paste {count} selected item(s) {where} '{anchor.title}'?"
            success = lambda backup_path: f"Pasted {count} selected item(s) {where} '{anchor.title}'. Backup: {backup_path}"

        self.run_mutation(prompt, task, success, preserve_rating_keys=list(self.cut_item_rating_keys))

    def new_playlist_from_cut(self):
        if not self.cut_item_rating_keys:
            messagebox.showwarning("Move Buffer Empty", "Store one or more titles in the move buffer first.")
            return
        name = simpledialog.askstring("New Playlist", "Enter new playlist name:", parent=self.root)
        if not name:
            return
        media_type = playlist_media_type([item for item in self.all_items if item.rating_key in set(self.cut_item_rating_keys)])
        def task():
            self.server.create_playlist_from_rating_keys(name.strip(), self.cut_item_rating_keys, media_type)
            return name.strip()
        journal_context = {"operation_type": "create_playlist_from_move_buffer", "server_name": self.server.name, "playlist_title": name.strip()}
        self.run_task("Creating playlist from move buffer...", task, on_success=lambda nm: self.set_status(f"Created new playlist '{nm}' from the move buffer."), journal_context=journal_context)

    def export_cut_to_csv(self):
        if not self.cut_item_rating_keys:
            messagebox.showwarning("Move Buffer Empty", "Store one or more titles in the move buffer first.")
            return
        items = [item for item in self.all_items if item.rating_key in set(self.cut_item_rating_keys)]
        name = simpledialog.askstring("Export Move Buffer", "Name for exported move-buffer selection:", parent=self.root) or "cut_block"
        self.run_task("Exporting move buffer...", lambda: self.server.export_csv(name, items), on_success=lambda path: self.set_status(f"Move buffer exported to {path}"))

    def remove_selected_from_playlist(self):
        items = self.selected_items()
        if not items:
            messagebox.showwarning("Select Title(s)", "Select one or more titles first.")
            return
        if not self.should_confirm(f"Remove {len(items)} selected title(s) from this playlist only? This does not modify the real media files on disk."):
            return
        playlist_key = self.playlist_rating_key
        item_ids = [item.playlist_item_id for item in items]
        rating_keys = [item.rating_key for item in items]
        def task():
            backup_path = self.server.export_backup(f"{self.playlist_title_var.get().strip()}_pre_remove", self.all_items)
            self.server.remove_items_from_playlist(playlist_key, item_ids)
            remaining = [item for item in self.all_items if item.playlist_item_id not in set(item_ids)]
            for i, item in enumerate(remaining, start=1):
                item.position = i
            return remaining, backup_path
        def done(result, db_backup_path):
            items, backup_path = result
            self.all_items = items
            self.filtered_items = list(self.all_items)
            self.apply_smart_filter()
            self.set_last_playlist_backup(backup_path, self.playlist_title_var.get().strip())
            status = f"Removed {len(item_ids)} title(s) from playlist. Safety backup: {backup_path}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            self.set_status(status)
        journal_context = {"operation_type": "remove_from_playlist", "server_name": self.server.name, "playlist_title": self.playlist_title_var.get().strip(), "playlist_rating_key": self.playlist_rating_key or "", "create_safety_backup": True, "playlist_items": list(self.all_items)}
        self.run_db_guarded_task("Removing selected items from playlist...", self.server, task, done, journal_context=journal_context)

    def delete_selected_from_plex(self):
        items = self.selected_items()
        if not items:
            messagebox.showwarning("Select Title(s)", "Select one or more titles first.")
            return
        if not self.should_confirm(f"Delete {len(items)} selected title(s) from Plex library? This is destructive to Plex library state, but Powr Playlist does not modify your real media files directly."):
            return
        item_ids = [item.playlist_item_id for item in items]
        rating_keys = [item.rating_key for item in items]
        def task():
            for rk in rating_keys:
                self.server.delete_library_item(rk)
            remaining = [item for item in self.all_items if item.rating_key not in set(rating_keys)]
            for i, item in enumerate(remaining, start=1):
                item.position = i
            return remaining
        def done(result, db_backup_path):
            self.all_items = result
            self.filtered_items = list(self.all_items)
            self.apply_smart_filter()
            status = f"Deleted {len(rating_keys)} title(s) from Plex library."
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            self.set_status(status)
        journal_context = {"operation_type": "delete_from_plex", "server_name": self.server.name, "playlist_title": self.playlist_title_var.get().strip(), "playlist_rating_key": self.playlist_rating_key or "", "create_safety_backup": True, "playlist_items": list(self.all_items)}
        self.run_db_guarded_task("Deleting selected media from Plex...", self.server, task, done, journal_context=journal_context)

    def restore_latest(self):
        if not self.require_playlist_loaded():
            return
        title = self.playlist_title_var.get().strip()
        if not self.should_confirm("Restore this playlist from the latest backup?"):
            return
        playlist_key = self.playlist_rating_key

        def task():
            self.update_task_progress(f"Loading latest backup for {title}...", always_show=True)
            latest = self.server.latest_backup_path(title)
            return self.server.restore_from_backup(title, playlist_key, self.all_items, latest)

        def done(result, db_backup_path):
            items, moved_count, skipped_count, warnings, backup_path = result
            self.all_items = items
            self.filtered_items = list(self.all_items)
            self.on_filter_type_changed()
            self.set_last_playlist_backup(backup_path, title)
            status = f"Restored from latest backup. Moved: {moved_count}, Skipped: {skipped_count}. Safety backup: {backup_path}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            if warnings:
                status += " Warnings present."
                messagebox.showwarning("Restore Warnings", "\n".join(warnings))
            self.set_status(status)

        journal_context = {"operation_type": "restore_latest", "server_name": self.server.name, "playlist_title": title, "playlist_rating_key": playlist_key or "", "create_safety_backup": True, "playlist_items": list(self.all_items)}
        self.run_db_guarded_task("Restoring from latest backup...", self.server, task, done, journal_context=journal_context)

    def restore_file(self):
        if not self.require_playlist_loaded():
            return
        title = self.playlist_title_var.get().strip()
        backup_path = filedialog.askopenfilename(
            title="Select backup file",
            initialdir=str(self.server.backup_dir()),
            filetypes=[("JSON backup", "*.json"), ("All files", "*.*")],
        )
        if not backup_path:
            return
        if not self.should_confirm(f"Restore from this backup?\n\n{backup_path}"):
            return
        playlist_key = self.playlist_rating_key

        def task():
            self.update_task_progress(f"Loading backup file {Path(backup_path).name}...", always_show=True)
            return self.server.restore_from_backup(title, playlist_key, self.all_items, Path(backup_path))

        def done(result, db_backup_path):
            items, moved_count, skipped_count, warnings, safety_backup = result
            self.all_items = items
            self.filtered_items = list(self.all_items)
            self.on_filter_type_changed()
            self.set_last_playlist_backup(safety_backup, title)
            status = f"Restored from file. Moved: {moved_count}, Skipped: {skipped_count}. Safety backup: {safety_backup}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            if warnings:
                status += " Warnings present."
                messagebox.showwarning("Restore Warnings", "\n".join(warnings))
            self.set_status(status)

        journal_context = {"operation_type": "restore_from_file", "server_name": self.server.name, "playlist_title": title, "playlist_rating_key": playlist_key or "", "create_safety_backup": True, "playlist_items": list(self.all_items), "notes": str(backup_path)}
        self.run_db_guarded_task("Restoring from selected backup...", self.server, task, done, journal_context=journal_context)

    def show_about(self):
        version = APP_VERSION if "APP_VERSION" in globals() else "unknown"
        message = (
            f"Plex Playlist Organizer {version}\n\n"
            "A Windows tool for managing large Plex playlists without fighting the Plex GUI.\n\n"
            "Built for single-admin, multi-server playlist management.\n"
            "Features include cut/paste moves, smart search and filtering, CSV import/export, backup/restore, and cross-server playlist copy.\n\n"
            "Powr Playlist never modifies your real media files on disk. It only changes Plex playlist/library state and app backup/export files.\n\n"
            "Created by Marvin and HAL.\n"
            "Python build and engineering by HAL."
        )
        messagebox.showinfo("About Plex Playlist Organizer", message)


def main(argv: Optional[List[str]] = None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--scheduled-db-backup" in argv:
        try:
            return run_scheduled_db_backup_job()
        except Exception as exc:
            print(str(exc), file=sys.stderr)
            return 1

    root = tk.Tk()
    apply_plex_theme(root)
    OrganizerApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
