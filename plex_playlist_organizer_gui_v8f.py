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
import threading
import traceback
from copy import deepcopy
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from time import sleep
from typing import Any, Dict, List, Optional, Tuple
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

import tkinter as tk
from tkinter import filedialog, messagebox, ttk


CONFIG_PATH = Path("config.json")
DEFAULT_CONFIG = {
    "plex_token": "",
    "backup_root": r"W:\MediaServer\PlaylistOrganizer",
    "timeout_seconds": 20,
    "restore_pause_ms": 150,
    "suppress_confirmations": False,
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
    "timeout_seconds": 20,
    "restore_pause_ms": 150,
    "suppress_confirmations": False,
    "servers": [
        {
            "name": "",
            "base_url": "",
            "plex_db_path": ""
        }
    ]
}

APP_VERSION = "v8f"


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

    @property
    def display(self) -> str:
        year_text = f" ({self.year})" if self.year else ""
        return f"#{self.position:03d} {self.title}{year_text}"


def now_stamp() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def safe_name(text: str) -> str:
    return "".join(ch if ch.isalnum() or ch in ("-", "_") else "_" for ch in text).strip("_") or "item"


def normalize_base_url(url: str) -> str:
    value = str(url).strip()
    if not value:
        return ""
    if "://" not in value:
        value = "http://" + value
    return value.rstrip("/")


def is_valid_base_url(url: str) -> bool:
    value = normalize_base_url(url)
    return value.startswith("http://") or value.startswith("https://")


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

    if "backup_root" not in cfg:
        cfg["backup_root"] = DEFAULT_CONFIG["backup_root"]

    if "timeout_seconds" not in cfg:
        cfg["timeout_seconds"] = DEFAULT_CONFIG["timeout_seconds"]

    if "restore_pause_ms" not in cfg:
        cfg["restore_pause_ms"] = DEFAULT_CONFIG["restore_pause_ms"]

    if "suppress_confirmations" not in cfg:
        cfg["suppress_confirmations"] = DEFAULT_CONFIG["suppress_confirmations"]

    cleaned = []
    for server in cfg["servers"]:
        if not isinstance(server, dict):
            continue
        cleaned.append({
            "name": str(server.get("name", "")).strip(),
            "base_url": normalize_base_url(server.get("base_url", "")),
            "plex_db_path": str(server.get("plex_db_path", "")).strip(),
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
        self.timeout = int(app_config.get("timeout_seconds", 20))
        self.restore_pause_ms = int(app_config.get("restore_pause_ms", 150))

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

        try:
            with urlopen(req, timeout=self.timeout) as response:
                body = response.read().decode("utf-8", errors="replace")
        except HTTPError as exc:
            try:
                detail = exc.read().decode("utf-8", errors="replace")
            except Exception:
                detail = str(exc)
            raise PlexError(f"HTTP error {exc.code}: {detail}") from exc
        except URLError as exc:
            raise PlexError(f"Connection error: {exc}") from exc

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

    def get_playlist_items(self, playlist_rating_key: str) -> List[PlaylistItem]:
        data = self._request("GET", f"/playlists/{playlist_rating_key}/items")
        metadata = data.get("MediaContainer", {}).get("Metadata", [])
        items: List[PlaylistItem] = []
        for idx, item in enumerate(metadata, start=1):
            items.append(
                PlaylistItem(
                    position=idx,
                    title=str(item.get("title", "<untitled>")),
                    year=item.get("year"),
                    rating_key=str(item.get("ratingKey", "")),
                    playlist_item_id=str(item.get("playlistItemID", "")),
                )
            )
        return items

    def backup_dir(self) -> Path:
        path = Path(self.app_config["backup_root"]) / "Backups"
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

    def backup_plex_database(self) -> Path:
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

    def create_playlist_from_rating_keys(self, title: str, rating_keys: List[str]) -> None:
        keys = [str(k).strip() for k in rating_keys if str(k).strip()]
        if not keys:
            raise PlexError("No matched titles were found on the destination server, so no playlist was created.")
        # Use the same URI style PlexAPI uses for regular playlist creation.
        uri = f"{self.base_url}/library/metadata/{','.join(keys)}"
        self._request("POST", "/playlists", expect_json=False, type="video", title=title, smart=0, uri=uri)

    def search_movies(self, query: str) -> List[Dict[str, Any]]:
        data = self._request("GET", "/search", query=query)
        meta = data.get("MediaContainer", {}).get("Metadata", [])
        results = []
        for item in meta:
            item_type = str(item.get("type", "")).lower()
            if item_type not in {"movie", "video"}:
                continue
            results.append({
                "title": str(item.get("title", "")),
                "year": item.get("year"),
                "rating_key": str(item.get("ratingKey", "")),
            })
        return results

    def match_title(self, title: str, year: Optional[int]) -> Optional[str]:
        results = self.search_movies(title)
        exact = [r for r in results if r["title"].strip().lower() == title.strip().lower()]
        if not exact:
            return None
        if len(exact) == 1:
            return exact[0]["rating_key"]
        if year is not None:
            exact_year = [r for r in exact if r.get("year") == year]
            if len(exact_year) == 1:
                return exact_year[0]["rating_key"]
        # Title-first, then title+year when duplicates exist. If still ambiguous, return None.
        return None

    def copy_playlist_from_source(
        self,
        source_items: List[PlaylistItem],
        playlist_name: str,
        overwrite_existing: bool,
    ) -> Tuple[int, int, List[str]]:
        existing = self.find_playlist(playlist_name)
        if existing and overwrite_existing:
            self.delete_playlist(str(existing["ratingKey"]))
        elif existing and not overwrite_existing:
            raise PlexError(f"Destination playlist '{playlist_name}' already exists.")

        matched_keys: List[str] = []
        missing: List[str] = []

        for item in source_items:
            match_key = self.match_title(item.title, item.year)
            if match_key:
                matched_keys.append(match_key)
            else:
                missing.append(item.display)

        if matched_keys:
            self.create_playlist_from_rating_keys(playlist_name, matched_keys)

        return len(matched_keys), len(missing), missing

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
        backup_path = self.export_backup(playlist_title, items)
        if current.position == target_position:
            return list(items), backup_path

        work = list(items)
        if target_position == 1:
            pivot_after = "0"
        else:
            work_without = [i for i in work if i.playlist_item_id != playlist_item_id]
            pivot_after = work_without[target_position - 2].playlist_item_id

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
            raise PlexError("Anchor cannot be inside the selected block.")

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
        for target_index, desired_item in enumerate(desired_order, start=1):
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

        for target_index, desired in enumerate(desired_rows, start=1):
            match = None
            desired_rating_key = str(desired.get("rating_key", "") or "").strip()
            desired_title = str(desired.get("title", "") or "").strip()
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
        self.geometry("940x560")
        self.minsize(900, 540)
        self.transient(parent)
        self.grab_set()
        self.require_save = require_save
        self.result_config = None
        self.working = normalize_config(config)
        self.is_first_run = require_save
        if self.is_first_run:
            # keep timeout and restore pause defaults, but start all other fields blank
            self.working["plex_token"] = ""
            self.working["backup_root"] = ""
            self.working["servers"] = [{"name": "", "base_url": ""}]

        self.plex_token_var = tk.StringVar(value="" if self.require_save and not str(self.working.get("plex_token", "")).strip() else str(self.working.get("plex_token", "")))
        self.backup_root_var = tk.StringVar(value="" if self.require_save and not str(self.working.get("backup_root", "")).strip() else str(self.working.get("backup_root", "")))
        self.timeout_var = tk.StringVar(value=str(self.working.get("timeout_seconds", 20)))
        self.restore_pause_var = tk.StringVar(value=str(self.working.get("restore_pause_ms", 150)))
        self.suppress_confirmations_var = tk.BooleanVar(value=bool(self.working.get("suppress_confirmations", False)))

        self.server_name_var = tk.StringVar()
        self.server_url_var = tk.StringVar()
        self.server_db_path_var = tk.StringVar()

        self.columnconfigure(1, weight=1)
        self.rowconfigure(0, weight=1)

        self._build_ui()
        self._refresh_server_list()

        if self.require_save:
            self.protocol("WM_DELETE_WINDOW", self._cancel_required)

    def _build_ui(self):
        left = ttk.LabelFrame(self, text="Servers", padding=10)
        left.grid(row=0, column=0, sticky="nsw", padx=(10, 6), pady=10)
        left.rowconfigure(1, weight=1)

        self.server_listbox = tk.Listbox(left, height=14, exportselection=False)
        self.server_listbox.grid(row=1, column=0, sticky="nsw")
        self.server_listbox.bind("<<ListboxSelect>>", lambda _e: self._load_selected_server())

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

        ttk.Button(right, text="Apply Server Changes", command=self._apply_server_changes).grid(row=2, column=1, sticky="e", pady=(6, 10))

        general = ttk.LabelFrame(right, text="General", padding=10)
        general.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(8, 0))
        general.columnconfigure(1, weight=1)

        ttk.Label(general, text="Plex Token:").grid(row=0, column=0, sticky="w", pady=4)
        self.token_entry = PlaceholderEntry(general, textvariable=self.plex_token_var, placeholder="Paste your Plex token here", show="*")
        self.token_entry.grid(row=0, column=1, sticky="ew", pady=4)

        ttk.Label(general, text="Backup Root:").grid(row=1, column=0, sticky="w", pady=4)
        self.backup_root_entry = PlaceholderEntry(general, textvariable=self.backup_root_var, placeholder=r"Example: W:\MediaServer\PlaylistOrganizer")
        self.backup_root_entry.grid(row=1, column=1, sticky="ew", pady=4)

        ttk.Label(general, text="Timeout Seconds:").grid(row=2, column=0, sticky="w", pady=4)
        ttk.Entry(general, textvariable=self.timeout_var).grid(row=2, column=1, sticky="ew", pady=4)

        ttk.Label(general, text="Restore Pause ms:").grid(row=3, column=0, sticky="w", pady=4)
        ttk.Entry(general, textvariable=self.restore_pause_var).grid(row=3, column=1, sticky="ew", pady=4)

        ttk.Checkbutton(
            general,
            text="Suppress confirmations on startup",
            variable=self.suppress_confirmations_var
        ).grid(row=4, column=0, columnspan=2, sticky="w", pady=(8, 0))

        bottom = ttk.Frame(right)
        bottom.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(14, 0))
        bottom.columnconfigure(0, weight=1)

        ttk.Button(bottom, text="Reset to Defaults", command=self._reset_defaults).grid(row=0, column=0, sticky="w")
        ttk.Button(bottom, text="Cancel", command=self._cancel).grid(row=0, column=1, sticky="e", padx=6)
        ttk.Button(bottom, text="Save", command=self._save).grid(row=0, column=2, sticky="e")

    def _cancel_required(self):
        messagebox.showwarning("Configuration Required", "You must save configuration before using the app.", parent=self)

    def _cancel(self):
        if self.require_save:
            self._cancel_required()
        else:
            self.destroy()

    def _selected_index(self):
        sel = self.server_listbox.curselection()
        return int(sel[0]) if sel else None

    def _refresh_server_list(self):
        self.server_listbox.delete(0, tk.END)
        for server in self.working["servers"]:
            self.server_listbox.insert(tk.END, server.get("name") or "<unnamed>")
        if self.working["servers"]:
            idx = self._selected_index()
            if idx is None or idx >= len(self.working["servers"]):
                idx = 0
                self.server_listbox.selection_set(idx)
            self._load_selected_server()

    def _load_selected_server(self):
        idx = self._selected_index()
        if idx is None:
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

    def _apply_server_changes(self):
        idx = self._selected_index()
        if idx is None:
            return
        name = self.server_name_entry.get_actual().strip()
        url = normalize_base_url(self.server_url_entry.get_actual().strip())
        db_path = self.server_db_path_entry.get_actual().strip()
        if not name:
            messagebox.showwarning("Invalid Server", "Server name cannot be empty.", parent=self)
            return
        if not url:
            messagebox.showwarning("Invalid Server", "Base URL cannot be empty.", parent=self)
            return
        if not is_valid_base_url(url):
            messagebox.showwarning("Invalid Server", "Base URL must look like http://host:port or https://host:port.", parent=self)
            return
        for i, server in enumerate(self.working["servers"]):
            if i != idx and server.get("name", "").strip().lower() == name.lower():
                messagebox.showwarning("Duplicate Server", "Server names must be unique.", parent=self)
                return
        self.working["servers"][idx]["name"] = name
        self.working["servers"][idx]["base_url"] = url
        self.working["servers"][idx]["plex_db_path"] = db_path
        self.server_url_var.set(url)
        self.server_db_path_var.set(db_path)
        self._refresh_server_list()
        self.server_listbox.selection_clear(0, tk.END)
        self.server_listbox.selection_set(idx)
        self._load_selected_server()

    def _add_server(self):
        new_name = f"Server{len(self.working['servers']) + 1}"
        self.working["servers"].append({"name": new_name, "base_url": "http://127.0.0.1:32400", "plex_db_path": ""})
        self._refresh_server_list()
        idx = len(self.working["servers"]) - 1
        self.server_listbox.selection_clear(0, tk.END)
        self.server_listbox.selection_set(idx)
        self._load_selected_server()

    def _remove_server(self):
        idx = self._selected_index()
        if idx is None:
            return
        if len(self.working["servers"]) <= 1:
            messagebox.showwarning("Cannot Remove", "At least one server is required.", parent=self)
            return
        self.working["servers"].pop(idx)
        self._refresh_server_list()

    def _reset_defaults(self):
        self.working = normalize_config(FIRST_RUN_CONFIG)
        self.plex_token_var.set("")
        self.backup_root_var.set("")
        self.timeout_var.set("20")
        self.restore_pause_var.set("150")
        self.suppress_confirmations_var.set(False)
        self.token_entry._show_placeholder_if_needed()
        self.backup_root_entry._show_placeholder_if_needed()
        self._refresh_server_list()

    def _save(self):
        if self._selected_index() is not None:
            self._apply_server_changes()

        if not self.working["servers"]:
            messagebox.showwarning("Invalid Config", "At least one server is required.", parent=self)
            return

        plex_token = self.token_entry.get_actual().strip()
        backup_root = self.backup_root_entry.get_actual().strip()
        if not plex_token:
            messagebox.showwarning("Invalid Config", "Global Plex token cannot be empty.", parent=self)
            return
        if not backup_root:
            messagebox.showwarning("Invalid Config", "Backup root cannot be empty.", parent=self)
            return

        try:
            timeout_seconds = int(self.timeout_var.get().strip())
            restore_pause_ms = int(self.restore_pause_var.get().strip())
        except ValueError:
            messagebox.showwarning("Invalid Config", "Timeout and restore pause must be numeric.", parent=self)
            return

        names = [s.get("name", "").strip() for s in self.working["servers"]]
        if any(not name for name in names):
            messagebox.showwarning("Invalid Config", "All servers must have names.", parent=self)
            return
        if len(set(name.lower() for name in names)) != len(names):
            messagebox.showwarning("Invalid Config", "Server names must be unique.", parent=self)
            return
        for server in self.working["servers"]:
            server["base_url"] = normalize_base_url(server.get("base_url", ""))
            if not server.get("base_url", "").strip():
                messagebox.showwarning("Invalid Config", f"Server '{server.get('name', '<unnamed>')}' must have a Base URL.", parent=self)
                return
            if not is_valid_base_url(server.get("base_url", "")):
                messagebox.showwarning("Invalid Config", f"Server '{server.get('name', '<unnamed>')}' has an invalid Base URL.", parent=self)
                return

        self.result_config = {
            "plex_token": plex_token,
            "backup_root": backup_root,
            "timeout_seconds": timeout_seconds,
            "restore_pause_ms": restore_pause_ms,
            "suppress_confirmations": bool(self.suppress_confirmations_var.get()),
            "servers": deepcopy(self.working["servers"]),
        }
        self.destroy()


class CopyPlaylistDialog(tk.Toplevel):
    def __init__(self, parent, current_server_name: str, current_playlist_name: str, server_names: List[str]) -> None:
        super().__init__(parent)
        self.title("Copy Playlist To Server")
        self.geometry("560x250")
        self.transient(parent)
        self.grab_set()
        self.result = None

        self.source_server_var = tk.StringVar(value=current_server_name)
        self.source_playlist_var = tk.StringVar(value=current_playlist_name)
        self.dest_server_var = tk.StringVar(value=server_names[0] if server_names else "")
        if self.dest_server_var.get() == current_server_name and len(server_names) > 1:
            self.dest_server_var.set(server_names[1])
        self.playlist_name_var = tk.StringVar(value=current_playlist_name)

        frm = ttk.Frame(self, padding=12)
        frm.pack(fill="both", expand=True)
        frm.columnconfigure(1, weight=1)

        ttk.Label(frm, text="Source Server:").grid(row=0, column=0, sticky="w", pady=4)
        ttk.Entry(frm, textvariable=self.source_server_var, state="readonly").grid(row=0, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="Source Playlist:").grid(row=1, column=0, sticky="w", pady=4)
        ttk.Entry(frm, textvariable=self.source_playlist_var, state="readonly").grid(row=1, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="Destination Server:").grid(row=2, column=0, sticky="w", pady=4)
        ttk.Combobox(frm, textvariable=self.dest_server_var, values=server_names, state="readonly").grid(row=2, column=1, sticky="ew", pady=4)

        ttk.Label(frm, text="New Playlist Name:").grid(row=3, column=0, sticky="w", pady=4)
        ttk.Entry(frm, textvariable=self.playlist_name_var).grid(row=3, column=1, sticky="ew", pady=4)

        note = ttk.Label(frm, text="If the destination playlist already exists, the app will ask whether to overwrite it.", wraplength=500, justify="left")
        note.grid(row=4, column=0, columnspan=2, sticky="w", pady=(10, 0))

        btns = ttk.Frame(frm)
        btns.grid(row=5, column=0, columnspan=2, sticky="e", pady=(16, 0))
        ttk.Button(btns, text="Cancel", command=self.destroy).grid(row=0, column=0, padx=6)
        ttk.Button(btns, text="Copy", command=self._copy).grid(row=0, column=1)

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
        }
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
        self.search_var = tk.StringVar()
        self.status_var = tk.StringVar(value="Ready.")
        self.move_position_var = tk.StringVar()
        self.cut_title_var = tk.StringVar(value="Cut buffer: empty")
        self.imported_csv_var = tk.StringVar(value="Imported CSV: none")
        self.search_nav_var = tk.StringVar(value="Matches: 0")
        self.suppress_confirmations_var = tk.BooleanVar(value=bool(self.config.get("suppress_confirmations", False)))

        self.server: Optional[PlexServer] = None
        self.playlist_rating_key: Optional[str] = None
        self.playlist_list: List[Dict[str, Any]] = []
        self.all_items: List[PlaylistItem] = []

        self.cut_item_ids: List[str] = []
        self.cut_item_rating_keys: List[str] = []

        self.imported_csv_path: Optional[Path] = None
        self.imported_csv_rows: List[Dict[str, str]] = []

        self.search_match_indices: List[int] = []
        self.search_match_cursor: int = -1

        self._build_ui()

        if self.config_missing or not self.config.get("plex_token"):
            self.root.after(100, lambda: self.open_config_dialog(require_save=True))
        else:
            self.root.after(100, self.initialize_server)

    def _build_ui(self) -> None:
        self.root.columnconfigure(1, weight=1)
        self.root.rowconfigure(1, weight=1)

        top = ttk.Frame(self.root, padding=10)
        top.grid(row=0, column=0, columnspan=2, sticky="nsew")
        top.columnconfigure(9, weight=1)

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

        ttk.Label(top, text="Search:").grid(row=0, column=8, sticky="e", padx=(0, 6))
        self.search_entry = ttk.Entry(top, textvariable=self.search_var, width=28)
        self.search_entry.grid(row=0, column=9, sticky="ew", padx=(0, 6))
        self.search_entry.bind("<KeyRelease>", lambda _e: self.on_search_changed())
        self.search_entry.bind("<Return>", lambda _e: self.find_next_match())

        ttk.Button(top, text="Prev", command=self.find_previous_match).grid(row=0, column=10, sticky="w", padx=(0, 4))
        ttk.Button(top, text="Next", command=self.find_next_match).grid(row=0, column=11, sticky="w", padx=(0, 4))
        ttk.Button(top, text="Clear", command=self.clear_search).grid(row=0, column=12, sticky="w")

        self.server_label = ttk.Label(top, text="")
        self.server_label.grid(row=1, column=0, columnspan=9, sticky="w", pady=(8, 0))
        ttk.Label(top, textvariable=self.search_nav_var).grid(row=1, column=9, columnspan=4, sticky="e", pady=(8, 0))

        left = ttk.Frame(self.root, padding=(10, 0, 10, 10))
        left.grid(row=1, column=0, sticky="nsw")
        left.columnconfigure(0, weight=1)

        right = ttk.Frame(self.root, padding=(0, 0, 10, 10))
        right.grid(row=1, column=1, sticky="nsew")
        right.columnconfigure(0, weight=1)
        right.rowconfigure(1, weight=1)

        action_box = ttk.LabelFrame(left, text="Actions", padding=10)
        action_box.grid(row=0, column=0, sticky="new", pady=(0, 10))
        action_box.columnconfigure(0, weight=1)
        ttk.Button(action_box, text="Backup", command=self.backup_playlist).grid(row=0, column=0, sticky="ew", pady=2)
        ttk.Button(action_box, text="Export CSV", command=self.export_csv).grid(row=1, column=0, sticky="ew", pady=2)
        ttk.Button(action_box, text="Import CSV", command=self.import_csv).grid(row=2, column=0, sticky="ew", pady=2)
        ttk.Button(action_box, text="Apply Imported CSV", command=self.apply_imported_csv).grid(row=3, column=0, sticky="ew", pady=2)
        ttk.Button(action_box, text="Copy Playlist To Server", command=self.copy_playlist_to_server).grid(row=4, column=0, sticky="ew", pady=2)
        ttk.Button(action_box, text="Restore Latest Backup", command=self.restore_latest).grid(row=5, column=0, sticky="ew", pady=2)
        ttk.Button(action_box, text="Restore From File", command=self.restore_file).grid(row=6, column=0, sticky="ew", pady=2)
        ttk.Label(action_box, textvariable=self.imported_csv_var, wraplength=320, justify="left").grid(row=7, column=0, sticky="w", pady=(8, 0))

        move_box = ttk.LabelFrame(left, text="Move Selected Title(s)", padding=10)
        move_box.grid(row=1, column=0, sticky="new", pady=(0, 10))
        move_box.columnconfigure(1, weight=1)
        ttk.Label(move_box, text="To slot:").grid(row=0, column=0, sticky="w", padx=(0, 6))
        ttk.Entry(move_box, textvariable=self.move_position_var, width=10).grid(row=0, column=1, sticky="ew")
        ttk.Button(move_box, text="Move To Slot", command=self.move_to_position).grid(row=1, column=0, columnspan=2, sticky="ew", pady=(6, 2))
        ttk.Button(move_box, text="Move Up One", command=self.move_up_one).grid(row=2, column=0, columnspan=2, sticky="ew", pady=2)
        ttk.Button(move_box, text="Move Down One", command=self.move_down_one).grid(row=3, column=0, columnspan=2, sticky="ew", pady=2)

        cut_box = ttk.LabelFrame(left, text="Cut / Paste", padding=10)
        cut_box.grid(row=2, column=0, sticky="new", pady=(0, 10))
        cut_box.columnconfigure(0, weight=1)
        ttk.Label(cut_box, textvariable=self.cut_title_var, wraplength=320, justify="left").grid(row=0, column=0, sticky="w", pady=(0, 8))
        ttk.Button(cut_box, text="Cut Selected Block", command=self.cut_selected_block).grid(row=1, column=0, sticky="ew", pady=2)
        ttk.Button(cut_box, text="Paste Block Before Selected", command=lambda: self.paste_cut_block("before")).grid(row=2, column=0, sticky="ew", pady=2)
        ttk.Button(cut_box, text="Paste Block After Selected", command=lambda: self.paste_cut_block("after")).grid(row=3, column=0, sticky="ew", pady=2)
        ttk.Button(cut_box, text="Clear Cut Buffer", command=self.clear_cut_buffer).grid(row=4, column=0, sticky="ew", pady=2)

        options_box = ttk.LabelFrame(left, text="Options", padding=10)
        options_box.grid(row=3, column=0, sticky="new", pady=(0, 10))
        ttk.Checkbutton(options_box, text="Suppress confirmations", variable=self.suppress_confirmations_var, command=self.on_toggle_confirmations).grid(row=0, column=0, sticky="w")

        info_box = ttk.LabelFrame(left, text="Selected", padding=10)
        info_box.grid(row=4, column=0, sticky="new")
        self.selected_label = ttk.Label(info_box, text="Selected: none", justify="left", wraplength=320)
        self.selected_label.grid(row=0, column=0, sticky="w")

        ttk.Label(right, text="Playlist Items").grid(row=0, column=0, sticky="w", pady=(0, 6))
        columns = ("position", "title", "year")
        self.tree = ttk.Treeview(right, columns=columns, show="headings", selectmode="extended")
        self.tree.heading("position", text="#")
        self.tree.heading("title", text="Title")
        self.tree.heading("year", text="Year")
        self.tree.column("position", width=70, anchor="center")
        self.tree.column("title", width=760, anchor="w")
        self.tree.column("year", width=90, anchor="center")
        self.tree.grid(row=1, column=0, sticky="nsew")

        yscroll = ttk.Scrollbar(right, orient="vertical", command=self.tree.yview)
        yscroll.grid(row=1, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=yscroll.set)
        self.tree.bind("<<TreeviewSelect>>", lambda _e: self.update_selection_label())
        self.tree.bind("<Double-1>", lambda _e: self.cut_selected_block())

        status = ttk.Label(self.root, textvariable=self.status_var, relief="sunken", anchor="w", padding=6)
        status.grid(row=2, column=0, columnspan=2, sticky="ew")


    def confirm_db_backup_guard(self, server: PlexServer):
        """
        Returns (should_continue, should_backup_now)
        """
        path = server.plex_db_path()
        name = server.name

        if path:
            first = messagebox.askyesno(
                "Recommended: Back Up Plex Database",
                f"It is strongly recommended that you back up the Plex database for '{name}' before making playlist changes.\n\n"
                f"Configured DB path:\n{path}\n\n"
                "Back up the Plex database now?"
            )
            if first:
                return True, True

            second = messagebox.askyesno(
                "Proceed At Your Own Risk",
                f"You declined the Plex database backup for '{name}'.\n\n"
                "Proceed at your own risk?"
            )
            return second, False

        first = messagebox.askyesno(
            "Recommended: Back Up Plex Database",
            f"It is strongly recommended that you back up the Plex database for '{name}' before making playlist changes.\n\n"
            "No Plex DB path is configured for this server, so the app cannot back it up automatically.\n\n"
            "Continue without an automatic database backup?"
        )
        if not first:
            return False, False

        second = messagebox.askyesno(
            "Proceed At Your Own Risk",
            f"No Plex DB path is configured for '{name}', and no automatic database backup will be made.\n\n"
            "Proceed at your own risk?"
        )
        return second, False

    def run_db_guarded_task(self, label: str, server: PlexServer, func, on_success=None):
        should_continue, should_backup = self.confirm_db_backup_guard(server)
        if not should_continue:
            self.set_status("Action cancelled.")
            return

        def task():
            db_backup_path = None
            if should_backup:
                db_backup_path = server.backup_plex_database()
            result = func()
            return db_backup_path, result

        def done(payload):
            db_backup_path, result = payload
            if on_success:
                on_success(result, db_backup_path)

        self.run_task(label, task, done)

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
        self.server_label.config(text=f"Server URL: {self.server.base_url}")
        self.clear_cut_buffer()
        self.imported_csv_path = None
        self.imported_csv_rows = []
        self.imported_csv_var.set("Imported CSV: none")
        self.playlist_rating_key = None
        self.all_items = []
        self.search_match_indices = []
        self.search_match_cursor = -1
        self.search_nav_var.set("Matches: 0")
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

    def run_task(self, label: str, func, on_success=None):
        self.set_status(label)
        self.root.config(cursor="watch")
        self.root.update_idletasks()

        def worker():
            try:
                result = func()
                self.root.after(0, lambda: self._task_success(result, on_success))
            except Exception as exc:
                tb = traceback.format_exc()
                self.root.after(0, lambda: self._task_error(exc, tb))

        threading.Thread(target=worker, daemon=True).start()

    def _task_success(self, result, on_success):
        self.root.config(cursor="")
        if on_success:
            on_success(result)

    def _task_error(self, exc, tb):
        self.root.config(cursor="")
        self.set_status(f"Error: {exc}")
        messagebox.showerror("Error", f"{exc}\n\n{tb}")

    def set_status(self, text: str):
        self.status_var.set(text)
        self.root.update_idletasks()

    def visible_items(self) -> List[PlaylistItem]:
        return self.all_items

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
        items = self.visible_items()
        return [items[idx] for idx in self.get_selected_indices() if 0 <= idx < len(items)]

    def selected_item(self) -> Optional[PlaylistItem]:
        items = self.selected_items()
        return items[0] if items else None

    def update_selection_label(self):
        items = self.selected_items()
        if not items:
            self.selected_label.config(text="Selected: none")
        elif len(items) == 1:
            self.selected_label.config(text=f"Selected: {items[0].display}")
        else:
            self.selected_label.config(text=f"Selected block: {len(items)} items\nFirst: {items[0].display}\nLast: {items[-1].display}")

    def populate_tree(self, items: List[PlaylistItem], selected_rating_keys: Optional[List[str]] = None):
        self.tree.delete(*self.tree.get_children())
        selected_rating_keys = selected_rating_keys or []
        selected_iids = []
        for idx, item in enumerate(items):
            iid = str(idx)
            self.tree.insert("", "end", iid=iid, values=(item.position, item.title, item.year or ""))
            if item.rating_key in selected_rating_keys:
                selected_iids.append(iid)
        self.tree.selection_remove(*self.tree.selection())
        if selected_iids:
            self.tree.selection_set(selected_iids)
            self.tree.focus(selected_iids[0])
            self.tree.see(selected_iids[0])
        self.update_selection_label()
        self.tree.update_idletasks()
        self.root.update_idletasks()

    def rebuild_search_matches(self):
        query = self.search_var.get().strip().lower()
        items = self.visible_items()
        if not query:
            self.search_match_indices = []
            self.search_match_cursor = -1
            self.search_nav_var.set("Matches: 0")
            return
        self.search_match_indices = [idx for idx, item in enumerate(items) if query in item.title.lower()]
        self.search_match_cursor = -1
        self.search_nav_var.set(f"Matches: {len(self.search_match_indices)}")

    def focus_match_at_cursor(self):
        if not self.search_match_indices or self.search_match_cursor < 0:
            return
        idx = self.search_match_indices[self.search_match_cursor]
        iid = str(idx)
        if iid in self.tree.get_children():
            self.tree.selection_remove(*self.tree.selection())
            self.tree.selection_set(iid)
            self.tree.focus(iid)
            self.tree.see(iid)
            self.update_selection_label()
            self.search_nav_var.set(f"Match {self.search_match_cursor + 1} of {len(self.search_match_indices)}")

    def on_search_changed(self):
        self.rebuild_search_matches()
        if self.search_match_indices:
            self.search_match_cursor = 0
            self.focus_match_at_cursor()

    def find_next_match(self):
        if not self.search_match_indices:
            self.rebuild_search_matches()
        if not self.search_match_indices:
            self.set_status("No search matches.")
            return
        self.search_match_cursor = (self.search_match_cursor + 1) % len(self.search_match_indices)
        self.focus_match_at_cursor()

    def find_previous_match(self):
        if not self.search_match_indices:
            self.rebuild_search_matches()
        if not self.search_match_indices:
            self.set_status("No search matches.")
            return
        self.search_match_cursor = (self.search_match_cursor - 1) % len(self.search_match_indices)
        self.focus_match_at_cursor()

    def clear_search(self):
        self.search_var.set("")
        self.search_match_indices = []
        self.search_match_cursor = -1
        self.search_nav_var.set("Matches: 0")

    def clear_cut_buffer(self):
        self.cut_item_ids = []
        self.cut_item_rating_keys = []
        self.cut_title_var.set("Cut buffer: empty")
        self.set_status("Cut buffer cleared.")

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
            self.populate_tree(self.all_items)
            self.rebuild_search_matches()
            timestamp = datetime.now().strftime("%I:%M:%S %p").lstrip("0")
            self.set_status(f"Loaded playlist '{title}' on {self.server_name_var.get()} with {len(self.all_items)} items at {timestamp}.")

        self.run_task(f"Loading playlist '{title}'...", task, done)

    def require_playlist_loaded(self) -> bool:
        if not self.server or not self.playlist_rating_key:
            messagebox.showwarning("Not Loaded", "Load the playlist first.")
            return False
        return True

    def backup_playlist(self):
        if not self.require_playlist_loaded():
            return
        title = self.playlist_title_var.get().strip()
        self.run_task("Writing backup...", lambda: self.server.export_backup(title, self.all_items), on_success=lambda path: self.set_status(f"Backup written to {path}"))

    def export_csv(self):
        if not self.require_playlist_loaded():
            return
        title = self.playlist_title_var.get().strip()
        self.run_task("Exporting CSV...", lambda: self.server.export_csv(title, self.all_items), on_success=lambda path: self.set_status(f"CSV written to {path}"))

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
            self.server.bind_playlist_context(playlist_key)
            return self.server.apply_order_rows(title, playlist_key, self.all_items, self.imported_csv_rows)

        def done(result, db_backup_path):
            items, moved_count, skipped_count, warnings, backup_path = result
            self.all_items = items
            self.populate_tree(self.all_items)
            self.rebuild_search_matches()
            status = f"Applied imported CSV. Moved: {moved_count}, Skipped: {skipped_count}. Backup: {backup_path}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            if warnings:
                status += " Warnings present."
                messagebox.showwarning("Import Warnings", "\n".join(warnings))
            self.set_status(status)

        self.run_db_guarded_task("Applying imported CSV order...", self.server, task, done)

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

        if dest_server_name == self.server_name_var.get():
            if not messagebox.askyesno("Same Server", "Destination server is the same as the source. Continue anyway?"):
                return

        dest_server = PlexServer(self.server_map[dest_server_name], self.config)

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

        source_items = list(self.all_items)

        def task():
            return dest_server.copy_playlist_from_source(source_items, playlist_name, overwrite_existing)

        def done(result, db_backup_path):
            matched_count, missing_count, missing = result
            status = f"Copied playlist to {dest_server_name}. Matched: {matched_count}, Missing: {missing_count}."
            if db_backup_path:
                status += f" DB backup: {db_backup_path}"
            if missing:
                preview = "\n".join(missing[:20])
                if missing_count > 20:
                    preview += f"\n...and {missing_count - 20} more."
                messagebox.showwarning("Missing Titles", preview)
            self.set_status(status)

        self.run_db_guarded_task(f"Copying playlist to {dest_server_name}...", dest_server, task, done)

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
            self.populate_tree(self.all_items, selected_rating_keys=preserve_rating_keys)
            self.rebuild_search_matches()
            message = success_builder(backup_path)
            if db_backup_path:
                message += f" Plex DB backup: {db_backup_path}"
            self.set_status(message)

        self.run_db_guarded_task("Applying change...", self.server, func, done)

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
            self.cut_title_var.set(f"Cut buffer: {items[0].display}")
            self.set_status(f"Cut '{items[0].title}'. Now select an anchor and paste before or after.")
        else:
            self.cut_title_var.set(f"Cut buffer: {len(items)} items\nFirst: {items[0].display}\nLast: {items[-1].display}")
            self.set_status(f"Cut block of {len(items)} items. Now select an anchor and paste before or after.")

    def paste_cut_block(self, where: str):
        if not self.cut_item_ids:
            messagebox.showwarning("Cut Buffer Empty", "Cut one or more titles first.")
            return
        anchor = self.selected_item()
        if not anchor:
            messagebox.showwarning("Select Anchor", "Select the anchor title in the list.")
            return
        if anchor.playlist_item_id in set(self.cut_item_ids):
            messagebox.showwarning("Invalid Paste", "Anchor cannot be inside the selected block.")
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
            prompt = f"Paste block of {count} items {where} '{anchor.title}'?"
            success = lambda backup_path: f"Pasted block of {count} items {where} '{anchor.title}'. Backup: {backup_path}"

        self.run_mutation(prompt, task, success, preserve_rating_keys=list(self.cut_item_rating_keys))

    def restore_latest(self):
        if not self.require_playlist_loaded():
            return
        title = self.playlist_title_var.get().strip()
        if not self.should_confirm("Restore this playlist from the latest backup?"):
            return
        playlist_key = self.playlist_rating_key

        def task():
            latest = self.server.latest_backup_path(title)
            return self.server.restore_from_backup(title, playlist_key, self.all_items, latest)

        def done(result, db_backup_path):
            items, moved_count, skipped_count, warnings, backup_path = result
            self.all_items = items
            self.populate_tree(self.all_items)
            self.rebuild_search_matches()
            status = f"Restored from latest backup. Moved: {moved_count}, Skipped: {skipped_count}. Safety backup: {backup_path}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            if warnings:
                status += " Warnings present."
                messagebox.showwarning("Restore Warnings", "\n".join(warnings))
            self.set_status(status)

        self.run_db_guarded_task("Restoring from latest backup...", self.server, task, done)

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
            return self.server.restore_from_backup(title, playlist_key, self.all_items, Path(backup_path))

        def done(result, db_backup_path):
            items, moved_count, skipped_count, warnings, safety_backup = result
            self.all_items = items
            self.populate_tree(self.all_items)
            self.rebuild_search_matches()
            status = f"Restored from file. Moved: {moved_count}, Skipped: {skipped_count}. Safety backup: {safety_backup}"
            if db_backup_path:
                status += f" Plex DB backup: {db_backup_path}"
            if warnings:
                status += " Warnings present."
                messagebox.showwarning("Restore Warnings", "\n".join(warnings))
            self.set_status(status)

        self.run_db_guarded_task("Restoring from selected backup...", self.server, task, done)

    def show_about(self):
        version = APP_VERSION if "APP_VERSION" in globals() else "unknown"
        message = (
            f"Plex Playlist Organizer {version}\n\n"
            "A Windows tool for managing large Plex playlists without fighting the Plex GUI.\n\n"
            "Built for single-admin, multi-server playlist management.\n"
            "Features include block moves, search navigation, CSV import/export, backup/restore, and cross-server playlist copy.\n\n"
            "Created by Marvin and HAL.\n"
            "Python build and engineering by HAL."
        )
        messagebox.showinfo("About Plex Playlist Organizer", message)


def main():
    root = tk.Tk()
    try:
        ttk.Style().theme_use("vista")
    except Exception:
        pass
    OrganizerApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
