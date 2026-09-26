import discord
from discord import app_commands
from discord.ext import tasks
from discord.ui import View, Button
import os
import re
import aiohttp
import aiosqlite
import asyncio
import logging
import io
import zipfile
import aiofiles
import uuid
import json
import sys
import random
from collections import defaultdict
from datetime import datetime, timezone
from html import unescape
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse, quote
from dotenv import load_dotenv
import internetarchive as ia

# --- Configuration & Setup ---

load_dotenv()

DISCORD_TOKEN = os.getenv('DISCORD_TOKEN')
OWNER_ID = os.getenv('OWNER_ID')
GITHUB_TOKEN = os.getenv('GITHUB_TOKEN')
REPO_OWNER = os.getenv('GITHUB_OWNER')
REPO_NAME = os.getenv('GITHUB_REPO')
WORKFLOW_FILE = 't.yml'
BOT_REQUEST_TRACE_ID = "bigdawg"

if not DISCORD_TOKEN:
    raise RuntimeError("Missing DISCORD_TOKEN in environment variables")
if not OWNER_ID:
    logging.warning("Missing OWNER_ID in environment variables, restart command will be disabled if not set")
    OWNER_ID = 0
else:
    OWNER_ID = int(OWNER_ID)

if not (GITHUB_TOKEN and REPO_OWNER and REPO_NAME):
    raise RuntimeError("Missing GitHub configuration (TOKEN/OWNER/REPO)")

DB_NAME = "archive_data.db"
EXCLUDED_DB_NAME = "excluded_urls.db"
LOG_FILE = "bot_logs.txt"
LOG_CHANNEL_ID = 1456758303085297675
STATE_FILE = "bot_state.json"

GITHUB_HEADERS = {
    "Authorization": f"Bearer {GITHUB_TOKEN}",
    "Accept": "application/vnd.github+json",
    "X-GitHub-Api-Version": "2022-11-28"
}

FILE_LOCK = asyncio.Lock()
HTTP_TIMEOUT = aiohttp.ClientTimeout(total=30)
MAX_CONCURRENT_JOBS = 4
MAX_QUEUED_JOBS = 4
JOB_TIMEOUT_SECONDS = 30 * 60
JOB_RETRY_DELAY_SECONDS = 2 * 60 * 60
RATE_LIMIT_EXCLUSION_SECONDS = 60 * 60
STANDARD_EXCLUSION_RETENTION_DAYS = 3
YOUTUBE_COOKIE_SECRETS = {
    1: "YOUTUBE_COOKIES_BASE64",
    2: "YOUTUBE_COOKIES_2_BASE64",
    3: "YOUTUBE_COOKIES_3_BASE64",
    4: "YOUTUBE_COOKIES_4_BASE64",
}


class YouTubeCookiesUnavailable(Exception):
    """Keep the request queued until an eligible cookie secret is available"""


def format_archive_complete(icon, status_text, archive_url, trace_id=None):
    message = (
        f"{icon} Archive Complete\n"
        f"Status: {status_text}\n"
        f"Archive URL: {archive_url}"
    )
    if trace_id:
        message += f"\n\n||Trace ID: `{trace_id}`||"
    return message


def format_existing_archive(url_type, archive_url, trace_id=None):
    return format_archive_complete(
        "<:minus:1455628978584027228>",
        f"{url_type} is already archived", archive_url, trace_id
    )


def has_invalid_youtube_cookies(log_text):
    return bool(re.search(
        r"the\s+provided\s+youtube\s+account\s+cookies\s+are\s+no\s+longer\s+valid\b",
        log_text, re.IGNORECASE
    ))

# Categories for excluded_urls.txt
CAT_VIDEOS = "[Videos]"
CAT_PLAYLISTS = "[Playlists]"
CAT_CHANNELS = "[Channels]"

logging.basicConfig(level=logging.INFO, format='%(asctime)s | %(levelname)s | %(message)s')

# Add file handler to also log to file
file_handler = logging.FileHandler(LOG_FILE, mode='a', encoding='utf-8')
file_handler.setLevel(logging.INFO)
file_handler.setFormatter(logging.Formatter('%(asctime)s | %(levelname)s | %(message)s'))
logging.getLogger().addHandler(file_handler)

intents = discord.Intents.default()
intents.message_content = True

class ArchiveBot(discord.Client):
    def __init__(self):
        super().__init__(intents=intents)
        self.tree = app_commands.CommandTree(self)
        self.session = None
        self.active_jobs = defaultdict(int)
        self.queued_jobs = defaultdict(list)
        self.pending_traces = {} # trace_id -> context
        self.batch_jobs = {} # batch_id -> aggregate multi-link context
        self.bot_trace_lock = asyncio.Lock()
        self.cookie_lock = asyncio.Lock()
        self.state_lock = asyncio.Lock()
        self.disabled_cookies = {}
        self.cookie_secret_versions = {}
        self.cookie_metadata_loaded = False
        self.shutdown_requested = False

    async def setup_hook(self):
        self.session = aiohttp.ClientSession(timeout=HTTP_TIMEOUT)
        await init_db()
        await self.load_disabled_cookies()
        await init_excluded_db()
        await remove_expired_global_exclusions()
        await self.load_state()
        if BOT_REQUEST_TRACE_ID in self.pending_traces and not self.bot_trace_lock.locked():
            await self.bot_trace_lock.acquire()
        await self.tree.sync()
        upload_logs.start()
        poll_github_runs.start()
        poll_cookie_secrets.start()
        cleanup_expired_exclusions.start()
        self.update_bot_status.start()
        logging.info("Commands synced, DB initialized, Session active, Log upload task started, Github polling started, exclusion cleanup started")

    async def on_ready(self):
        print(f'Logged in as {self.user}!')
        print('---')
        print('Currently in the following servers:')
        for guild in self.guilds:
            print(f'- {guild.name} (ID: {guild.id})')

    @tasks.loop(hours=1)
    async def update_bot_status(self):
        try:
            if self.is_closed():
                return

            query = 'scanner:"TubeUp Video Stream Mirroring Application" uploader:"thebigmujjahidlol88@protonmail.com" mediatype:"movies"'
            
            def get_stats():
                search_results = ia.search_items(query, fields=['item_size', 'identifier'])
                total_bytes = 0
                item_count = 0
                for result in search_results:
                    size = result.get('item_size')
                    if size:
                        total_bytes += int(size)
                    item_count += 1
                return item_count, total_bytes

            if hasattr(asyncio, 'to_thread'):
                count, total_bytes = await asyncio.to_thread(get_stats)
            else:
                loop = asyncio.get_running_loop()
                count, total_bytes = await loop.run_in_executor(None, get_stats)
                
            def format_size(size_bytes):
                if size_bytes == 0:
                    return "0 B"
                for unit in ['Bytes', 'KBs', 'MBs', 'GBs', 'TBs', 'PBs']:
                    if size_bytes < 1024.0:
                        return f"{size_bytes:.2f} {unit}"
                    size_bytes /= 1024.0
                return f"{size_bytes:.2f} PBs"

            size_str = format_size(total_bytes)
            
            activity = discord.Activity(type=discord.ActivityType.watching, name=f"{count} videos and {size_str} of data 🎥")
            await self.change_presence(activity=activity)

        except Exception as e:
            # Ignore AttributeError regarding change_presence
            if isinstance(e, AttributeError) and "object has no attribute 'change_presence'" in str(e):
                return
            logging.error(f"Failed to update bot status: {e}")

    @update_bot_status.before_loop
    async def before_update_bot_status(self):
        await self.wait_until_ready()

    async def save_state(self):
        async with self.state_lock:
            await self._save_state()

    async def _save_state(self):
        """Save the current state of pending traces and queued jobs to a file"""
        logging.info("Saving state")
        state = {
            "pending_traces": {},
            "queued_jobs": {},
            "active_jobs": dict(self.active_jobs),
            "batch_jobs": {}
        }

        # Serialize batch_jobs
        for batch_id, batch in self.batch_jobs.items():
            state["batch_jobs"][batch_id] = {
                "total": batch["total"],
                "completed": batch["completed"],
                "success": batch["success"],
                "failed": batch["failed"],
                "archive_urls": batch["archive_urls"],
                "status_msg_data": {
                    "channel_id": batch["status_msg"].channel.id,
                    "message_id": batch["status_msg"].id
                } if batch["status_msg"] else None
            }

        # Serialize pending_traces
        for trace_id, context in self.pending_traces.items():
            state["pending_traces"][trace_id] = {
                "user_id": context["user_id"],
                "target_url": context["target_url"],
                "url_type": context["url_type"],
                "is_silent": context["is_silent"],
                "history_run_id": context["history_run_id"],
                "guild_id": context.get("guild_id"),
                "free_space": context.get("free_space", False),
                "batch_id": context.get("batch_id"),
                "is_bot_request": context.get("is_bot_request", False),
                "is_cookie_retry": context.get("is_cookie_retry", False),
                "ignore_existing_item": context.get("ignore_existing_item", False),
                "github_run_id": context.get("github_run_id"),
                "youtube_account": context.get("youtube_account"),
                "cookie_secret_updated_at": context.get("cookie_secret_updated_at"),
                "start_time": context["start_time"].isoformat() if isinstance(context["start_time"], datetime) else context["start_time"],
                "status_msg_data": {
                    "channel_id": context["status_msg"].channel.id,
                    "message_id": context["status_msg"].id
                } if context["status_msg"] else None
            }

        # Serialize queued_jobs
        for user_id, jobs in self.queued_jobs.items():
            serialized_jobs = []
            for job in jobs:
                # job: (target_url, url_type, is_silent, original_message,
                #       guild_id, user_id, free_space, batch_id, is_bot_request)
                if len(job) == 6:
                    target_url, url_type, is_silent, msg, guild_id, uid = job
                    free_space = False
                    batch_id = None
                    is_bot_request = False
                elif len(job) == 7:
                    target_url, url_type, is_silent, msg, guild_id, uid, free_space = job
                    batch_id = None
                    is_bot_request = False
                elif len(job) == 8:
                    target_url, url_type, is_silent, msg, guild_id, uid, free_space, batch_id = job
                    is_bot_request = False
                else:
                    target_url, url_type, is_silent, msg, guild_id, uid, free_space, batch_id, is_bot_request = job[:9]
                serialized_jobs.append({
                    "target_url": target_url,
                    "url_type": url_type,
                    "is_silent": is_silent,
                    "guild_id": guild_id,
                    "user_id": uid,
                    "free_space": free_space,
                    "batch_id": batch_id,
                    "is_bot_request": is_bot_request,
                    "is_cookie_retry": bool(job[9]) if len(job) > 9 else False,
                    "ignore_existing_item": bool(job[10]) if len(job) > 10 else False,
                    "message_data": {
                        "channel_id": msg.channel.id,
                        "message_id": msg.id
                    } if msg else None
                })
            state["queued_jobs"][str(user_id)] = serialized_jobs

        try:
            async with aiofiles.open(STATE_FILE + '.tmp', 'w') as f:
                await f.write(json.dumps(state, indent=4))
            os.replace(STATE_FILE + '.tmp', STATE_FILE)
            logging.info("State saved successfully")
        except Exception as e:
            logging.error(f"Failed to save state: {e}")

    async def load_state(self):
        """Load the state from the file and restore objects"""
        if not os.path.exists(STATE_FILE):
            return

        logging.info("Loading state from file")
        try:
            async with aiofiles.open(STATE_FILE, 'r') as f:
                content = await f.read()
                if not content: return
                state = json.loads(content)

            # Restore active jobs count
            self.active_jobs = defaultdict(int, {int(k): v for k, v in state.get("active_jobs", {}).items()})

            # Restore batch_jobs
            self.batch_jobs = {}
            for batch_id, bdata in state.get("batch_jobs", {}).items():
                status_msg = None
                if bdata.get("status_msg_data"):
                    try:
                        channel = self.get_channel(bdata["status_msg_data"]["channel_id"]) or await self.fetch_channel(bdata["status_msg_data"]["channel_id"])
                        if channel:
                            status_msg = await channel.fetch_message(bdata["status_msg_data"]["message_id"])
                    except Exception as e:
                        logging.warning(f"Could not restore status message for batch {batch_id}: {e}")
                self.batch_jobs[batch_id] = {
                    "total": bdata["total"],
                    "completed": bdata["completed"],
                    "success": bdata["success"],
                    "failed": bdata["failed"],
                    "archive_urls": bdata["archive_urls"],
                    "status_msg": status_msg
                }

            # Restore pending_traces
            for trace_id, data in state.get("pending_traces", {}).items():
                status_msg = None
                if data.get("status_msg_data"):
                    try:
                        channel = self.get_channel(data["status_msg_data"]["channel_id"]) or await self.fetch_channel(data["status_msg_data"]["channel_id"])
                        if channel:
                            status_msg = await channel.fetch_message(data["status_msg_data"]["message_id"])
                    except Exception as e:
                        logging.warning(f"Could not restore status message for trace {trace_id}: {e}")

                self.pending_traces[trace_id] = {
                    "user_id": data["user_id"],
                    "target_url": data["target_url"],
                    "url_type": data["url_type"],
                    "is_silent": data["is_silent"],
                    "status_msg": status_msg,
                    "history_run_id": data["history_run_id"],
                    "guild_id": data.get("guild_id"),
                    "free_space": data.get("free_space", False),
                    "batch_id": data.get("batch_id"),
                    "is_bot_request": data.get("is_bot_request", trace_id == BOT_REQUEST_TRACE_ID),
                    "is_cookie_retry": data.get("is_cookie_retry", False),
                    "ignore_existing_item": data.get("ignore_existing_item", False),
                    "github_run_id": data.get("github_run_id"),
                    "youtube_account": data.get("youtube_account"),
                    "cookie_secret_updated_at": data.get("cookie_secret_updated_at"),
                    "start_time": datetime.fromisoformat(data["start_time"]) if data.get("start_time") else datetime.now(timezone.utc)
                }

            # Restore queued_jobs
            for user_id_str, jobs_data in state.get("queued_jobs", {}).items():
                user_id = int(user_id_str)
                restored_jobs = []
                for job_data in jobs_data:
                    msg = None
                    if job_data.get("message_data"):
                        try:
                            channel = self.get_channel(job_data["message_data"]["channel_id"]) or await self.fetch_channel(job_data["message_data"]["channel_id"])
                            if channel:
                                msg = await channel.fetch_message(job_data["message_data"]["message_id"])
                        except Exception as e:
                            logging.warning(f"Could not restore queue message for user {user_id}: {e}")
                    
                    # Reconstruct tuple
                    restored_jobs.append((
                        job_data["target_url"],
                        job_data["url_type"],
                        job_data["is_silent"],
                        msg,
                        job_data["guild_id"],
                        job_data["user_id"],
                        job_data.get("free_space", False),
                        job_data.get("batch_id"),
                        job_data.get("is_bot_request", False),
                        job_data.get("is_cookie_retry", False),
                        job_data.get("ignore_existing_item", False)
                    ))
                self.queued_jobs[user_id] = restored_jobs

            logging.info(f"State loaded: {len(self.pending_traces)} pending traces, {len(self.queued_jobs)} users in queue")
            
            # Remove state file after successful load to prevent loop on crash
            os.remove(STATE_FILE)

        except Exception as e:
            logging.error(f"Failed to load state: {e}")

    async def load_disabled_cookies(self):
        async with aiosqlite.connect(DB_NAME) as db:
            async with db.execute(
                "SELECT account, secret_updated_at, disabled_at, notified, run_id, trace_id "
                "FROM disabled_youtube_cookies"
            ) as cursor:
                for account, version, disabled_at, notified, run_id, trace_id in await cursor.fetchall():
                    self.disabled_cookies[account] = {
                        "secret_updated_at": version, "disabled_at": disabled_at,
                        "notified": bool(notified), "run_id": run_id, "trace_id": trace_id,
                    }

    def available_youtube_accounts(self):
        return [account for account in YOUTUBE_COOKIE_SECRETS
                if account in self.cookie_secret_versions and account not in self.disabled_cookies]

    async def notify_disabled_cookies(self):
        # Called with cookie_lock held, so simultaneous failures cannot spam DMs
        for account, state in self.disabled_cookies.items():
            if state["notified"] or not OWNER_ID:
                continue
            secret_name = YOUTUBE_COOKIE_SECRETS[account]
            message = (
                f"YouTube account {account}'s cookies have been disabled\n\n"
                "The provided YouTube account cookies are no longer valid\n\n"
                f"Update the `{secret_name}` Actions repository secret in "
                f"`{REPO_OWNER}/{REPO_NAME}` with fresh Base64-encoded cookies\n"
                "I check for secret updates every 35 minutes and will automatically use this "
                "account again after its secret is updated\n"
                "Other available accounts can continue, requests wait in the queue if none are available"
            )
            if state.get("run_id"):
                message += f"\n\nRun: https://github.com/{REPO_OWNER}/{REPO_NAME}/actions/runs/{state['run_id']}"
            try:
                owner = self.get_user(OWNER_ID) or await self.fetch_user(OWNER_ID)
                await owner.send(message)
                async with aiosqlite.connect(DB_NAME) as db:
                    await db.execute("UPDATE disabled_youtube_cookies SET notified = 1 WHERE account = ?", (account,))
                    await db.commit()
                state["notified"] = True
            except Exception as exc:
                # Leave notified false so the next poll retries a failed DM
                logging.warning("Could not DM OWNER_ID about YouTube account %s: %s", account, exc)

    async def refresh_cookie_secrets(self):
        """Read only secret names/timestamps, GitHub never returns secret values"""
        async with self.cookie_lock:
            await self.notify_disabled_cookies()
            versions = {}
            try:
                page = 1
                while True:
                    url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/secrets"
                    async with self.session.get(
                        url, headers=GITHUB_HEADERS, params={"per_page": 100, "page": page}
                    ) as response:
                        if response.status != 200:
                            logging.warning(
                                "Cannot check cookie secrets (HTTP %s), GITHUB_TOKEN needs repository "
                                "Secrets: read permission, or repo scope for a classic PAT, "
                                "disabled cookies remain disabled", response.status
                            )
                            return False
                        data = await response.json()
                    secrets = data.get("secrets", [])
                    by_name = {item["name"]: item.get("updated_at") for item in secrets}
                    for account, name in YOUTUBE_COOKIE_SECRETS.items():
                        if by_name.get(name):
                            versions[account] = by_name[name]
                    if len(secrets) < 100:
                        break
                    page += 1
            except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
                logging.warning("Could not check cookie secret updates: %s", exc)
                return False

            async with aiosqlite.connect(DB_NAME) as db:
                for account, state in list(self.disabled_cookies.items()):
                    current_version = versions.get(account)
                    if not current_version:
                        continue  # A missing/deleted secret does not enable the account
                    failed_version = state.get("secret_updated_at")
                    if failed_version is None:
                        # Legacy runs may not have a dispatch-time timestamp, establish
                        # a baseline without treating the first observation as an update
                        await db.execute(
                            "UPDATE disabled_youtube_cookies SET secret_updated_at = ? WHERE account = ?",
                            (current_version, account)
                        )
                        state["secret_updated_at"] = current_version
                    elif current_version > failed_version:
                        await db.execute("DELETE FROM disabled_youtube_cookies WHERE account = ?", (account,))
                        del self.disabled_cookies[account]
                        logging.info("YouTube account %s re-enabled after its secret was updated", account)
                await db.commit()
            self.cookie_secret_versions = versions
            self.cookie_metadata_loaded = True
            return True

    async def choose_youtube_cookie(self):
        # Capture a fresh revision for the secret used by this dispatch
        await self.refresh_cookie_secrets()
        async with self.cookie_lock:
            available = self.available_youtube_accounts()
            if not available:
                raise YouTubeCookiesUnavailable()
            account = random.choice(available)
            return account, self.cookie_secret_versions[account]

    async def disable_youtube_cookie(self, account, secret_updated_at, run_id, trace_id):
        async with self.cookie_lock:
            # Ignore late failures from a run that used a secret already replaced
            current_version = self.cookie_secret_versions.get(account)
            if secret_updated_at and current_version and current_version > secret_updated_at:
                logging.info("Ignoring expired cookies from an older revision of account %s", account)
                return
            if account not in self.disabled_cookies:
                state = {
                    "secret_updated_at": secret_updated_at or current_version,
                    "disabled_at": datetime.now(timezone.utc).isoformat(),
                    "notified": False, "run_id": run_id, "trace_id": trace_id,
                }
                async with aiosqlite.connect(DB_NAME) as db:
                    await db.execute(
                        "INSERT INTO disabled_youtube_cookies "
                        "(account, secret_updated_at, disabled_at, notified, run_id, trace_id) "
                        "VALUES (?, ?, ?, 0, ?, ?)",
                        (account, state["secret_updated_at"], state["disabled_at"], run_id, trace_id)
                    )
                    await db.commit()
                self.disabled_cookies[account] = state
                logging.warning("Disabled YouTube account %s until %s is updated", account, YOUTUBE_COOKIE_SECRETS[account])
            await self.notify_disabled_cookies()

    async def close(self):
        poll_cookie_secrets.cancel()
        if self.session:
            await self.session.close()
        await super().close()

    async def fetch_artifact_logs(self, run_id, trace_id):
        artifacts_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{run_id}/artifacts"
        expected_name = f"archive-logs-{trace_id}.txt"
        try:
            for _ in range(3):
                async with self.session.get(artifacts_url, headers=GITHUB_HEADERS) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        for artifact in data.get("artifacts", []):
                            if artifact["name"] == expected_name:
                                download_url = artifact["archive_download_url"]
                                async with self.session.get(download_url, headers=GITHUB_HEADERS) as d_resp:
                                    if d_resp.status == 200:
                                        log_data = await d_resp.read()
                                        if zipfile.is_zipfile(io.BytesIO(log_data)):
                                            with zipfile.ZipFile(io.BytesIO(log_data)) as archive:
                                                for name in archive.namelist():
                                                    if name.rsplit('/', 1)[-1] == expected_name:
                                                        return archive.read(name)
                                            continue
                                        return log_data
                await asyncio.sleep(2)
        except Exception as e:
            logging.error(f"Failed to fetch artifact for run {run_id}: {e}")
        # A failed artifact upload must not hide the expired-cookie warning
        try:
            logs_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{run_id}/logs"
            async with self.session.get(logs_url, headers=GITHUB_HEADERS) as response:
                if response.status == 200:
                    raw = await response.read()
                    if zipfile.is_zipfile(io.BytesIO(raw)):
                        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
                            return b'\n'.join(archive.read(name) for name in archive.namelist() if name.endswith('.txt'))
                    return raw
        except Exception as exc:
            logging.warning("Could not fetch workflow log fallback for run %s: %s", run_id, exc)
        return None

    async def handle_completion(self, context, exit_code, trace_id):
        user_id = context["user_id"]
        original_url = context["target_url"]
        url_type = context["url_type"]
        status_msg = context["status_msg"]
        is_silent = context["is_silent"]
        batch_id = context.get("batch_id")
        
        status = "completed" if exit_code == 0 else "failed"
        
        actual_run_id = context.get("github_run_id")
        # Fetch artifact logs once
        log_bytes = None
        log_text = ""
        if actual_run_id:
            log_bytes = await self.fetch_artifact_logs(actual_run_id, trace_id)
            if log_bytes:
                # Clean up yt-dlp carriage returns (\r) to prevent single-line logs
                try:
                    log_text = log_bytes.decode('utf-8', errors='replace')
                    log_text = re.sub(r'[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\.[a-zA-Z0-9-.]+', '***', log_text)
                    cleaned_lines = [line.split('\r')[-1] for line in log_text.split('\n')]
                    log_bytes = '\n'.join(cleaned_lines).encode('utf-8')
                except Exception as e:
                    logging.warning(f"Failed to clean log bytes for trace {trace_id}: {e}")

                # Send to log channel
                log_channel = self.get_channel(LOG_CHANNEL_ID)
                if log_channel:
                    try:
                        await log_channel.send(
                            content=f"Log for trace `{trace_id}`\n(Status: {status}):",
                            file=discord.File(fp=io.BytesIO(log_bytes), filename=f"archive_log_{trace_id}.txt")
                        )
                    except Exception as e:
                        logging.error(f"Failed to upload artifact to log channel for trace {trace_id}: {e}")

        invalid_cookies = has_invalid_youtube_cookies(log_text)
        history_status = "Archived" if exit_code == 0 and not invalid_cookies else "Failed"
        if actual_run_id:
            async with aiosqlite.connect(DB_NAME) as db:
                await db.execute("UPDATE history SET run_id = ?, status = ? WHERE run_id = ?", (actual_run_id, history_status, context["history_run_id"]))
                await db.commit()
        else:
            await update_history_status(context["history_run_id"], history_status)

        if invalid_cookies:
            account = context.get("youtube_account")
            if account not in YOUTUBE_COOKIE_SECRETS:
                match = re.search(r'\[youtube-cookie\] account=([1-4])\b', log_text)
                account = int(match.group(1)) if match else None
            if account in YOUTUBE_COOKIE_SECRETS:
                await self.disable_youtube_cookie(
                    account, context.get("cookie_secret_updated_at"), actual_run_id, trace_id
                )
                self.queued_jobs[user_id].insert(0, (
                    original_url, url_type, is_silent, status_msg, context.get("guild_id"), user_id,
                    context.get("free_space", False), batch_id, context.get("is_bot_request", False), True,
                    context.get("ignore_existing_item", False)
                ))
                waiting = not self.available_youtube_accounts()
                await update_history_status(
                    actual_run_id or context["history_run_id"], "Waiting for cookies" if waiting else "Retrying"
                )
                # The poller releases the slot before processing this retry, do
                # not exclude the URL permanently or count the batch as failed
                return
            logging.error("Expired YouTube cookies detected for trace %s but the account is unknown", trace_id)

        if log_text and "IOException: No space left on device" in log_text and not context.get("free_space", False):
            user_id = context["user_id"]
            queued_job = (
                context["target_url"],
                context["url_type"],
                context["is_silent"],
                context.get("status_msg"),
                context.get("guild_id"),
                user_id,
                True, # free_space
                context.get("batch_id"),
                context.get("is_bot_request", False),
                context.get("is_cookie_retry", False),
                context.get("ignore_existing_item", False)
            )
            client.queued_jobs[user_id].insert(0, queued_job)
            
            if actual_run_id:
                async with aiosqlite.connect(DB_NAME) as db:
                    await db.execute("UPDATE history SET status = ? WHERE run_id = ?", ("Retrying", actual_run_id))
                    await db.commit()
            else:
                await update_history_status(context["history_run_id"], "Retrying")
            
            if not is_silent and status_msg:
                try:
                    await status_msg.edit(
                        content=f"<a:loading:1455572437277348005> Storage limit reached for {url_type}, retrying with large file support\n\n||Trace ID: `{trace_id}`||"
                    )
                except Exception:
                    pass
            
            return

        video_id = get_video_id(original_url)
        youtube_rate_limited = bool(
            log_text
            and "Your account has been rate-limited by YouTube for up to an hour" in log_text
        )

        is_already_archived = False
        if log_text and "Item already exists. Not downloading." in log_text:
            is_already_archived = True

        archive_succeeded = exit_code == 0 or is_already_archived

        if archive_succeeded and video_id:
            try:
                await make_global_exclusion_permanent(video_id)
            except Exception as e:
                logging.error(f"Failed to make successful exclusion permanent for {video_id}: {e}")
        elif youtube_rate_limited and video_id:
            try:
                if await set_global_exclusion_expiry(video_id):
                    asyncio.create_task(remove_global_exclusion_after_expiry(video_id))
            except Exception as e:
                logging.error(f"Failed to set one-hour exclusion expiry for {video_id}: {e}")

        if archive_succeeded:
            if video_id and url_type in ["Video", "Short", "Live"]:
                asyncio.create_task(scan_and_dispatch_description_links(video_id, trace_id))

        archive_urls = []
        if log_text and not is_already_archived:
            archive_urls = re.findall(r'(https?://(?:www\.)?archive\.org/[^\s<>"\']+)', log_text)
            # Deduplicate while preserving order
            archive_urls = list(dict.fromkeys(archive_urls))

        if batch_id:
            await self.update_batch_progress(
                batch_id, 
                is_success=archive_succeeded,
                archive_urls=archive_urls
            )
            return

        if not is_silent and status_msg:
            display_url = original_url 

            if url_type == "Channel":
                query_string = f'channel:"{original_url}"'
                encoded_query = quote(query_string)
                display_url = f"https://archive.org/search?query={encoded_query}"
            elif video_id:
                display_url = f"https://archive.org/details/youtube-{video_id}"
            
            icon = "<:wrong:1455628187127120068>"
            status_text = f"Archive failed (Exit Code: {exit_code})"
            
            if exit_code == 0:
                icon = "<:checkmark:1455627640974344203>"
                status_text = "Archive succeeded"

            if is_already_archived:
                icon = "<:minus:1455628978584027228>"
                status_text = f"{url_type} is already archived"
            elif youtube_rate_limited:
                icon = "<:wrong:1455628187127120068>"
                status_text = "Bot's account has been rate-limited, please try again later in an hour or so"
            elif log_text and "Please reduce your request rate." in log_text:
                icon = "<:wrong:1455628187127120068>"
                status_text = f"This {url_type} has been rejected by the Internet Archive"
            elif log_text and "video unavailable" in log_text.casefold():
                icon = "<:wrong:1455628187127120068>"
                status_text = "Video unavailable"
            elif log_text and "the specified bucket is not valid" in log_text.casefold():
                icon = "<:wrong:1455628187127120068>"
                status_text = f"Most likely that this YouTube {url_type} is already archived"
            elif log_text and "IOException: No space left on device" in log_text:
                icon = "<:wrong:1455628187127120068>"
                status_text = f"This {url_type} is way too large"

            attachment_file = None
            if archive_urls:
                if len(archive_urls) == 1:
                    display_url = archive_urls[0]
                elif len(archive_urls) > 1:
                    display_url = f"Multiple items archived ({len(archive_urls)} URLs)"
                    urls_content = "\n".join(archive_urls).encode('utf-8')
                    attachment_file = discord.File(fp=io.BytesIO(urls_content), filename=f"urls_{trace_id}.txt")

            final_msg = format_archive_complete(icon, status_text, display_url, trace_id)
            
            try:
                edit_kwargs = {"content": final_msg, "embed": None}
                if attachment_file:
                    edit_kwargs["attachments"] = [attachment_file]
                await status_msg.edit(**edit_kwargs)
            except Exception as e:
                logging.error(f"Failed to edit status message: {e}")

    async def update_batch_progress(self, batch_id, is_success, archive_urls=None):
        if not batch_id:
            return
        batch = self.batch_jobs.get(batch_id)
        if batch is not None:
            batch["completed"] += 1
            if is_success:
                batch["success"] += 1
            else:
                batch["failed"] += 1
            if archive_urls:
                batch["archive_urls"].extend(archive_urls)

            if batch["completed"] >= batch["total"]:
                if batch["status_msg"]:
                    deduped = list(dict.fromkeys(batch["archive_urls"]))
                    batch_attachment = None
                    archive_summary = "No archive URLs were produced"
                    if deduped:
                        archive_summary = "Attached text file"
                        urls_content = "\n".join(deduped).encode('utf-8')
                        batch_attachment = discord.File(
                            fp=io.BytesIO(urls_content),
                            filename=f"archive_links_{batch_id}.txt"
                        )

                    final_batch_msg = (
                        "<:checkmark:1455627640974344203> Archive Batch Complete\n"
                        f"Processed: {batch['total']} links\n"
                        f"Successful: {batch['success']}\n"
                        f"Failed: {batch['failed']}\n"
                        f"Archive URLs: {archive_summary}\n\n"
                        f"||Batch ID: `{batch_id}`||"
                    )
                    try:
                        edit_kwargs = {"content": final_batch_msg}
                        if batch_attachment:
                            edit_kwargs["attachments"] = [batch_attachment]
                        await batch["status_msg"].edit(**edit_kwargs)
                    except Exception as e:
                        logging.error(f"Failed to edit batch status message: {e}")
                del self.batch_jobs[batch_id]

client = ArchiveBot()

def release_bot_trace_slot(context):
    """Release the shared fixed trace ID after a bot-authored request ends"""
    if context.get("is_bot_request") and client.bot_trace_lock.locked():
        client.bot_trace_lock.release()

async def schedule_timeout_retry(context):
    await asyncio.sleep(JOB_RETRY_DELAY_SECONDS)

    user_id = context["user_id"]
    queued_job = (
        context["target_url"],
        context["url_type"],
        context["is_silent"],
        context.get("status_msg"),
        context.get("guild_id"),
        user_id,
        context.get("free_space", False),
        context.get("batch_id"),
        context.get("is_bot_request", False),
        context.get("is_cookie_retry", False),
        True, # ignore_existing_item for retries after the 30-minute timeout
    )

    client.queued_jobs[user_id].append(queued_job)

    if client.active_jobs[user_id] < MAX_CONCURRENT_JOBS:
        await check_and_process_queue(user_id)

# --- GitHub Polling Task ---

@tasks.loop(seconds=15)
async def poll_github_runs():
    if not client.pending_traces:
        return
        
    runs_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/workflows/{WORKFLOW_FILE}/runs"
    try:
        async with client.session.get(runs_url, headers=GITHUB_HEADERS, params={"per_page": 100}) as resp:
            if resp.status == 200:
                data = await resp.json()
                for run in data.get("workflow_runs", []):
                    run_name = run.get("display_title") or run.get("name", "")
                    run_status = run.get("status")
                    conclusion = run.get("conclusion")
                    
                    match = re.search(r'\[trace-([a-zA-Z0-9-]+)\]', run_name)
                    if match:
                        trace_id = match.group(1)
                        if trace_id in client.pending_traces:
                            context = client.pending_traces[trace_id]

                            # Bot-authored requests intentionally reuse the
                            # fixed trace ID "bigdawg", ignore older workflow
                            # runs with that same name and bind this request to
                            # the first current run we observe
                            if context.get("is_bot_request"):
                                run_id = run.get("id")
                                bound_run_id = context.get("github_run_id")
                                if bound_run_id and run_id != bound_run_id:
                                    continue

                                created_at = run.get("created_at")
                                started_at = context.get("start_time")
                                if isinstance(created_at, str) and isinstance(started_at, datetime):
                                    try:
                                        run_created_at = datetime.fromisoformat(
                                            created_at.replace("Z", "+00:00")
                                        )
                                        if run_created_at.timestamp() + 5 < started_at.timestamp():
                                            continue
                                    except (TypeError, ValueError):
                                        pass

                                if not bound_run_id and run_status in ("queued", "in_progress"):
                                    context["github_run_id"] = run_id
                            
                            if run_status == "in_progress":
                                context["github_run_id"] = run.get("id")
                                started_at = context.get("start_time")
                                if isinstance(started_at, datetime):
                                    elapsed = (datetime.now(timezone.utc) - started_at).total_seconds()
                                    if elapsed > JOB_TIMEOUT_SECONDS and not context.get("retry_scheduled", False):
                                        context["retry_scheduled"] = True
                                        run_id = run.get("id")
                                        if run_id:
                                            cancel_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{run_id}/cancel"
                                            try:
                                                async with client.session.post(cancel_url, headers=GITHUB_HEADERS) as cancel_resp:
                                                    if cancel_resp.status not in (202, 409):
                                                        cancel_text = await cancel_resp.text()
                                                        logging.warning(f"Failed to cancel timed out run {run_id} for trace {trace_id}: {cancel_resp.status} {cancel_text}")
                                            except Exception as cancel_err:
                                                logging.warning(f"Error cancelling timed out run {run_id} for trace {trace_id}: {cancel_err}")

                                        await update_history_status(context["history_run_id"], "Retrying later")

                                        if not context["is_silent"] and context["status_msg"]:
                                            try:
                                                await context["status_msg"].edit(
                                                    content=f"<:warning:1492123648377618582> This archive job has taken longer than 30 minutes and will be retried in about 2 hours\n\n||Trace ID: `{trace_id}`||"
                                                )
                                            except Exception:
                                                pass

                                        user_id = context["user_id"]
                                        del client.pending_traces[trace_id]
                                        release_bot_trace_slot(context)
                                        client.active_jobs[user_id] = max(0, client.active_jobs[user_id] - 1)
                                        asyncio.create_task(schedule_timeout_retry(context))
                                        await check_and_process_queue(user_id)
                                        logging.info(f"Timed out trace {trace_id}, cancelled and scheduled retry in 2 hours")
                                        continue

                                if not context.get("is_processing", False):
                                    context["is_processing"] = True
                                    if not context["is_silent"] and context["status_msg"] and not context.get("is_cookie_retry"):
                                        try:
                                            await context["status_msg"].edit(content=f"<a:loading:1455572437277348005> YouTube {context['url_type']} is being preserved\n\n||Trace ID: `{trace_id}`||")
                                        except:
                                            pass
                            elif run_status == "completed":
                                exit_code = 0 if conclusion == "success" else 1
                                context["github_run_id"] = run.get("id")
                                
                                await client.handle_completion(context, exit_code, trace_id)
                                
                                user_id = context["user_id"]
                                del client.pending_traces[trace_id]
                                release_bot_trace_slot(context)
                                client.active_jobs[user_id] = max(0, client.active_jobs[user_id] - 1)
                                await check_and_process_queue(user_id)
                                await client.save_state()
                                logging.info(f"Cleaned up trace {trace_id}")
    except Exception as e:
        logging.error(f"Error polling github runs: {e}")

@poll_github_runs.before_loop
async def before_poll_github_runs():
    await client.wait_until_ready()


@tasks.loop(minutes=35)
async def poll_cookie_secrets():
    try:
        await client.refresh_cookie_secrets()
        # Wake paused queues even when no archive workflow is currently running
        if client.available_youtube_accounts():
            for user_id in list(client.queued_jobs):
                while client.queued_jobs[user_id] and client.active_jobs[user_id] < MAX_CONCURRENT_JOBS:
                    await check_and_process_queue(user_id)
        await client.save_state()
    except Exception as exc:
        logging.error("Error checking YouTube cookie secrets: %s", exc)


@poll_cookie_secrets.before_loop
async def before_poll_cookie_secrets():
    await client.wait_until_ready()

# --- Temporary Exclusion Cleanup Task ---

@tasks.loop(minutes=1)
async def cleanup_expired_exclusions():
    try:
        removed = await remove_expired_global_exclusions()
        if removed:
            logging.info(f"Removed {removed} expired global exclusion(s)")
    except Exception as e:
        logging.error(f"Failed to clean up expired global exclusions: {e}")

@cleanup_expired_exclusions.before_loop
async def before_cleanup_expired_exclusions():
    await client.wait_until_ready()

# --- Hourly Log Upload Task ---

@tasks.loop(hours=1)
async def upload_logs():
    """Upload terminal logs to the designated channel every hour"""
    channel = client.get_channel(LOG_CHANNEL_ID)
    if not channel:
        logging.warning(f"Could not find channel {LOG_CHANNEL_ID} for log upload")
        return
    
    # Generate filename with zero-padded datetime
    now = datetime.now(timezone.utc)
    filename = f"{now.year:04d}-{now.month:02d}-{now.day:02d} {now.hour:02d}-{now.minute:02d}-{now.second:02d} logs.txt"
    
    try:
        # Flush all file handlers to ensure logs are written
        for handler in logging.getLogger().handlers:
            if isinstance(handler, logging.FileHandler):
                handler.flush()
        
        # Check if log file exists and has content
        if not os.path.exists(LOG_FILE):
            return
        
        # Read current logs
        async with aiofiles.open(LOG_FILE, 'r', encoding='utf-8') as f:
            content = await f.read()
        
        if not content.strip():
            return  # No logs to upload
        
        # Write to new file with formatted name
        async with aiofiles.open(filename, 'w', encoding='utf-8') as f:
            await f.write(content)
        
        # Upload the file
        await channel.send(file=discord.File(filename))
        
        # Delete the uploaded file from system
        os.remove(filename)
        
        # Clear the original log file
        async with aiofiles.open(LOG_FILE, 'w', encoding='utf-8') as f:
            await f.write("")
    except Exception as e:
        logging.error(f"Failed to upload logs: {e}")
        # Clean up the temp file if it exists
        if os.path.exists(filename):
            try:
                os.remove(filename)
            except:
                pass

@upload_logs.before_loop
async def before_upload_logs():
    """Wait until the bot is ready before starting the log upload loop"""
    await client.wait_until_ready()

# --- Database Management ---

async def init_db():
    async with aiosqlite.connect(DB_NAME) as db:
        await db.execute("PRAGMA journal_mode=WAL;")
        await db.execute("PRAGMA synchronous=NORMAL;")
        await db.execute("PRAGMA busy_timeout=5000;")
        await db.execute("""
            CREATE TABLE IF NOT EXISTS disabled_youtube_cookies (
                account INTEGER PRIMARY KEY,
                secret_updated_at TEXT,
                disabled_at TEXT NOT NULL,
                notified INTEGER NOT NULL DEFAULT 0,
                run_id TEXT,
                trace_id TEXT
            )
        """)
        
        await db.execute("""
            CREATE TABLE IF NOT EXISTS exclusions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                guild_id INTEGER,
                type TEXT NOT NULL,
                value TEXT NOT NULL,
                added_by TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)
        
        await db.execute("""
            CREATE TABLE IF NOT EXISTS history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                guild_id INTEGER,
                user_id INTEGER,
                url TEXT,
                status TEXT,
                run_id INTEGER,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS global_user_exclusions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER UNIQUE,
                added_by TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Keep successful lifetime totals separate from history so users can
        # clear /history without losing their leaderboard progress, run_id
        # ensures that every completed archive is counted at most once
        await db.execute("""
            CREATE TABLE IF NOT EXISTS lifetime_jobs (
                run_id INTEGER PRIMARY KEY,
                guild_id INTEGER,
                user_id INTEGER NOT NULL,
                completed_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Cache whether a lifetime-jobs owner is a human, bot, or webhook
        # Leaderboard queries only include verified human accounts
        await db.execute("""
            CREATE TABLE IF NOT EXISTS leaderboard_accounts (
                user_id INTEGER PRIMARY KEY,
                account_type TEXT NOT NULL
                    CHECK (account_type IN ('human', 'bot', 'webhook')),
                checked_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Import successful jobs that existed before lifetime tracking was
        # introduced, INSERT OR IGNORE makes this safe on every startup
        await db.execute("""
            INSERT OR IGNORE INTO lifetime_jobs (run_id, guild_id, user_id, completed_at)
            SELECT run_id, guild_id, user_id, COALESCE(timestamp, CURRENT_TIMESTAMP)
            FROM history
            WHERE status = 'Archived'
              AND run_id IS NOT NULL
              AND user_id IS NOT NULL
        """)

        # Record new successful jobs automatically whenever their history
        # status changes to Archived
        await db.execute("""
            CREATE TRIGGER IF NOT EXISTS track_successful_lifetime_job
            AFTER UPDATE OF status ON history
            WHEN NEW.status = 'Archived'
                 AND NEW.run_id IS NOT NULL
                 AND NEW.user_id IS NOT NULL
            BEGIN
                INSERT OR IGNORE INTO lifetime_jobs (run_id, guild_id, user_id, completed_at)
                VALUES (NEW.run_id, NEW.guild_id, NEW.user_id, CURRENT_TIMESTAMP);
            END
        """)
        
        try:
            await db.execute("ALTER TABLE history ADD COLUMN trace_id TEXT")
        except Exception:
            pass

        # Requests using the dedicated automated trace ID are known bot or
        # webhook jobs and can be excluded without an API lookup
        await db.execute(
            """
            INSERT OR REPLACE INTO leaderboard_accounts
                (user_id, account_type, checked_at)
            SELECT DISTINCT user_id, 'bot', CURRENT_TIMESTAMP
            FROM history
            WHERE trace_id = ?
              AND user_id IS NOT NULL
            """,
            (BOT_REQUEST_TRACE_ID,)
        )
        
        await db.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_exclusions ON exclusions(guild_id, type, value);")
        await db.execute("CREATE INDEX IF NOT EXISTS ix_history_user ON history(user_id, id DESC);")
        await db.execute("CREATE INDEX IF NOT EXISTS ix_history_trace ON history(trace_id, id DESC);")
        await db.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_history_run ON history(run_id);")
        await db.execute("CREATE INDEX IF NOT EXISTS ix_lifetime_jobs_user ON lifetime_jobs(user_id);")
        
        await db.commit()

async def add_exclusion(guild_id, e_type, value, added_by):
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute("SELECT 1 FROM exclusions WHERE guild_id = ? AND type = ? AND value = ?", (guild_id, e_type, str(value)))
        if await cursor.fetchone():
            return False
        
        utc_now = datetime.now(timezone.utc).isoformat()
        await db.execute("INSERT INTO exclusions (guild_id, type, value, added_by, timestamp) VALUES (?, ?, ?, ?, ?)", 
                         (guild_id, e_type, str(value), str(added_by), utc_now))
        await db.commit()
        return True

async def remove_exclusion(guild_id, e_type, value):
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute("DELETE FROM exclusions WHERE guild_id = ? AND type = ? AND value = ?", (guild_id, e_type, str(value)))
        await db.commit()
        return cursor.rowcount > 0

async def is_user_or_channel_excluded(user_id, channel_id, guild_id):
    async with aiosqlite.connect(DB_NAME) as db:
        query = """
            SELECT 1 FROM exclusions
            WHERE guild_id = ?
            AND (
                (type='user' AND value=?)
                OR (type='channel' AND value=?)
            )
            LIMIT 1
        """
        async with db.execute(query, (guild_id, str(user_id), str(channel_id))) as cursor:
            return await cursor.fetchone() is not None

async def is_url_type_excluded(guild_id, url_type):
    async with aiosqlite.connect(DB_NAME) as db:
        query = "SELECT 1 FROM exclusions WHERE guild_id = ? AND type='url_type' AND value = ? LIMIT 1"
        async with db.execute(query, (guild_id, str(url_type))) as cursor:
            return await cursor.fetchone() is not None

async def add_global_user_exclusion(user_id, added_by):
    async with aiosqlite.connect(DB_NAME) as db:
        try:
            await db.execute(
                "INSERT INTO global_user_exclusions (user_id, added_by) VALUES (?, ?)",
                (user_id, str(added_by))
            )
            await db.commit()
            return True
        except aiosqlite.IntegrityError:
            return False

async def remove_global_user_exclusion(user_id):
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute(
            "DELETE FROM global_user_exclusions WHERE user_id = ?",
            (user_id,)
        )
        await db.commit()
        return cursor.rowcount > 0

async def is_user_globally_excluded(user_id):
    async with aiosqlite.connect(DB_NAME) as db:
        async with db.execute(
            "SELECT 1 FROM global_user_exclusions WHERE user_id = ?",
            (user_id,)
        ) as cursor:
            return await cursor.fetchone() is not None

async def set_allow_bot_messages(guild_id, added_by):
    """Enable processing of bot messages with YouTube URLs in a server"""
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute("SELECT 1 FROM exclusions WHERE guild_id = ? AND type = 'allow_bot_messages'", (guild_id,))
        if await cursor.fetchone():
            return False  # Already enabled
        
        utc_now = datetime.now(timezone.utc).isoformat()
        await db.execute("INSERT INTO exclusions (guild_id, type, value, added_by, timestamp) VALUES (?, ?, ?, ?, ?)", 
                         (guild_id, 'allow_bot_messages', 'enabled', str(added_by), utc_now))
        await db.commit()
        return True

async def unset_allow_bot_messages(guild_id):
    """Disable processing of bot messages with YouTube URLs in a server"""
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute("DELETE FROM exclusions WHERE guild_id = ? AND type = 'allow_bot_messages'", (guild_id,))
        await db.commit()
        return cursor.rowcount > 0

async def is_bot_messages_allowed(guild_id):
    """Check if bot messages are allowed to trigger archive requests in a server"""
    async with aiosqlite.connect(DB_NAME) as db:
        query = "SELECT 1 FROM exclusions WHERE guild_id = ? AND type = 'allow_bot_messages' LIMIT 1"
        async with db.execute(query, (guild_id,)) as cursor:
            return await cursor.fetchone() is not None

async def enable_all_messages(guild_id):
    """Enables reading all messages by removing the exclusion"""
    async with aiosqlite.connect(DB_NAME) as db:
        await db.execute("DELETE FROM exclusions WHERE guild_id = ? AND type = 'allmessages_disabled'", (guild_id,))
        await db.commit()
        return True

async def disable_all_messages(guild_id, added_by):
    """Disables reading all messages by adding the exclusion"""
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute("SELECT 1 FROM exclusions WHERE guild_id = ? AND type = 'allmessages_disabled'", (guild_id,))
        is_disabled = await cursor.fetchone()
        
        if not is_disabled:
            utc_now = datetime.now(timezone.utc).isoformat()
            await db.execute("INSERT INTO exclusions (guild_id, type, value, added_by, timestamp) VALUES (?, ?, ?, ?, ?)", 
                             (guild_id, 'allmessages_disabled', 'true', str(added_by), utc_now))
            await db.commit()
        return True

async def is_all_messages_enabled(guild_id):
    if not guild_id: return True
    async with aiosqlite.connect(DB_NAME) as db:
        query = "SELECT 1 FROM exclusions WHERE guild_id = ? AND type = 'allmessages_disabled' LIMIT 1"
        async with db.execute(query, (guild_id,)) as cursor:
            return await cursor.fetchone() is None

async def log_history(guild_id, user_id, url, status, run_id, trace_id=None):
    async with aiosqlite.connect(DB_NAME) as db:
        utc_now = datetime.now(timezone.utc).isoformat()
        if trace_id:
            await db.execute("INSERT INTO history (guild_id, user_id, url, status, run_id, timestamp, trace_id) VALUES (?, ?, ?, ?, ?, ?, ?)", 
                             (guild_id, user_id, url, status, run_id, utc_now, trace_id))
        else:
            await db.execute("INSERT INTO history (guild_id, user_id, url, status, run_id, timestamp) VALUES (?, ?, ?, ?, ?, ?)", 
                             (guild_id, user_id, url, status, run_id, utc_now))

        if trace_id == BOT_REQUEST_TRACE_ID:
            await db.execute(
                """
                INSERT INTO leaderboard_accounts
                    (user_id, account_type, checked_at)
                VALUES (?, 'bot', CURRENT_TIMESTAMP)
                ON CONFLICT(user_id) DO UPDATE SET
                    account_type = 'bot',
                    checked_at = CURRENT_TIMESTAMP
                """,
                (user_id,)
            )

        await db.commit()

async def update_history_status(run_id, status):
    async with aiosqlite.connect(DB_NAME) as db:
        await db.execute("UPDATE history SET status = ? WHERE run_id = ?", (status, run_id))
        await db.commit()

async def clear_user_history(user_id):
    async with aiosqlite.connect(DB_NAME) as db:
        await db.execute("DELETE FROM history WHERE user_id = ?", (user_id,))
        await db.commit()

async def get_history_page(user_id, page, per_page=5):
    offset = page * per_page
    async with aiosqlite.connect(DB_NAME) as db:
        # Get Total Count
        async with db.execute("SELECT COUNT(*) FROM history WHERE user_id = ?", (user_id,)) as cursor:
            total_count = (await cursor.fetchone())[0]
        
        # Get Data
        async with db.execute("SELECT url, status, timestamp, run_id, trace_id FROM history WHERE user_id = ? ORDER BY id DESC LIMIT ? OFFSET ?", (user_id, per_page, offset)) as cursor:
            rows = await cursor.fetchall()
            
    return rows, total_count

async def get_lifetime_job_count(user_id):
    async with aiosqlite.connect(DB_NAME) as db:
        async with db.execute(
            "SELECT COUNT(*) FROM lifetime_jobs WHERE user_id = ?",
            (user_id,)
        ) as cursor:
            return (await cursor.fetchone())[0]

async def classify_unclassified_leaderboard_accounts():
    """Classify lifetime-job owners once so automated accounts stay hidden"""
    async with aiosqlite.connect(DB_NAME) as db:
        async with db.execute(
            """
            SELECT DISTINCT jobs.user_id
            FROM lifetime_jobs AS jobs
            LEFT JOIN leaderboard_accounts AS accounts
                ON accounts.user_id = jobs.user_id
            WHERE accounts.user_id IS NULL
            ORDER BY jobs.user_id
            """
        ) as cursor:
            user_ids = [row[0] for row in await cursor.fetchall()]

    if not user_ids:
        return

    classifications = []
    for user_id in user_ids:
        discord_user = client.get_user(user_id)
        if discord_user is None:
            try:
                discord_user = await client.fetch_user(user_id)
            except discord.NotFound:
                # Webhook IDs do not resolve through Discord's user endpoint
                classifications.append((user_id, "webhook"))
                continue
            except discord.HTTPException as exc:
                logging.warning(
                    f"Could not classify leaderboard account {user_id}: {exc}"
                )
                continue

        is_automated = discord_user.bot or getattr(discord_user, "system", False)
        classifications.append((user_id, "bot" if is_automated else "human"))

    if not classifications:
        return

    async with aiosqlite.connect(DB_NAME) as db:
        await db.executemany(
            """
            INSERT INTO leaderboard_accounts
                (user_id, account_type, checked_at)
            VALUES (?, ?, CURRENT_TIMESTAMP)
            ON CONFLICT(user_id) DO UPDATE SET
                account_type = excluded.account_type,
                checked_at = CURRENT_TIMESTAMP
            """,
            classifications
        )
        await db.commit()

async def get_lifetime_leaderboard(user_id, limit=10):
    """Return the human-only top users, caller rank, and overall totals"""
    async with aiosqlite.connect(DB_NAME) as db:
        leaderboard_query = """
            WITH totals AS (
                SELECT
                    jobs.user_id,
                    COUNT(*) AS total_jobs,
                    MIN(jobs.completed_at) AS first_completed_at
                FROM lifetime_jobs AS jobs
                INNER JOIN leaderboard_accounts AS accounts
                    ON accounts.user_id = jobs.user_id
                WHERE accounts.account_type = 'human'
                GROUP BY jobs.user_id
            )
            SELECT user_id, total_jobs
            FROM totals
            ORDER BY total_jobs DESC, first_completed_at ASC, user_id ASC
            LIMIT ?
        """
        async with db.execute(leaderboard_query, (limit,)) as cursor:
            top_users = await cursor.fetchall()

        rank_query = """
            WITH totals AS (
                SELECT
                    jobs.user_id,
                    COUNT(*) AS total_jobs,
                    MIN(jobs.completed_at) AS first_completed_at
                FROM lifetime_jobs AS jobs
                INNER JOIN leaderboard_accounts AS accounts
                    ON accounts.user_id = jobs.user_id
                WHERE accounts.account_type = 'human'
                GROUP BY jobs.user_id
            ),
            ranked AS (
                SELECT
                    user_id,
                    total_jobs,
                    ROW_NUMBER() OVER (
                        ORDER BY total_jobs DESC, first_completed_at ASC, user_id ASC
                    ) AS position
                FROM totals
            )
            SELECT position, total_jobs
            FROM ranked
            WHERE user_id = ?
        """
        async with db.execute(rank_query, (user_id,)) as cursor:
            user_rank = await cursor.fetchone()

        async with db.execute(
            """
            SELECT COUNT(*), COUNT(DISTINCT jobs.user_id)
            FROM lifetime_jobs AS jobs
            INNER JOIN leaderboard_accounts AS accounts
                ON accounts.user_id = jobs.user_id
            WHERE accounts.account_type = 'human'
            """
        ) as cursor:
            total_jobs, total_users = await cursor.fetchone()

    return top_users, user_rank, total_jobs, total_users

# --- URL Handling ---

YOUTUBE_HOSTS = {
    'youtube.com',
    'www.youtube.com',
    'youtu.be',
    'www.youtu.be',
    'm.youtube.com',
    'music.youtube.com',
}
YOUTUBE_TIMESTAMP_PARAMS = {'t', 'start', 'time_continue', 'end'}
YOUTUBE_REMOVABLE_PARAMS = YOUTUBE_TIMESTAMP_PARAMS | {'si', 'pp'}
YOUTUBE_TIMESTAMP_FRAGMENT = re.compile(
    r'^(?:t=)?(?:\d+h)?(?:\d+m)?\d+(?:\.\d+)?s?$',
    re.IGNORECASE,
)

def clean_extracted_url(raw_url):
    """Decode and trim a URL extracted from messages or archived descriptions"""
    return unescape(raw_url).rstrip(').,;!?"\'')

def get_video_id(url):
    parsed = urlparse(url)
    if parsed.hostname in ('youtu.be', 'www.youtu.be'):
        path_parts = parsed.path.lstrip('/').split('/')
        return path_parts[0] if path_parts else None
        
    if parsed.hostname in ('youtube.com', 'www.youtube.com', 'm.youtube.com', 'music.youtube.com'):
        if parsed.path == '/watch':
            p = parse_qs(parsed.query)
            return p.get('v', [None])[0]
        if parsed.path.startswith('/shorts/'):
            parts = parsed.path.split('/')
            if len(parts) >= 3:
                return parts[2]
        if parsed.path.startswith('/live/'):
            parts = parsed.path.split('/')
            if len(parts) >= 3:
                return parts[2]
        if parsed.path.startswith('/playlist'):
            p = parse_qs(parsed.query)
            return p.get('list', [None])[0]
        if parsed.path.startswith('/channel/') or parsed.path.startswith('/c/') or parsed.path.startswith('/@'):
            parts = parsed.path.lstrip('/').split('/')
            if parts[0] in ('channel', 'c') and len(parts) >= 2:
                return f"{parts[0]}/{parts[1]}"
            elif parts[0].startswith('@'):
                return parts[0]
    return None

async def check_existing_archive(url):
    """Return a confirmed existing item URL, otherwise allow archiving to continue"""
    parsed = urlparse(url)
    # Collections contain many video items, they have no single youtube-ID item
    if parsed.path.startswith(('/playlist', '/channel/', '/c/', '/@')):
        return None
    video_id = get_video_id(url)
    if not video_id or not re.fullmatch(r'[A-Za-z0-9_-]+', video_id):
        return None
    identifier = f"youtube-{video_id}"
    try:
        async with client.session.get(
            f"https://archive.org/metadata/{identifier}",
            timeout=aiohttp.ClientTimeout(total=15)
        ) as response:
            if response.status != 200:
                raise ValueError(f"Metadata HTTP status {response.status}")
            data = await response.json()
        if data == {} or data == []:
            return None
        if isinstance(data, dict) and not data.get('error'):
            metadata = data.get('metadata')
            if isinstance(metadata, dict) and metadata.get('identifier') == identifier:
                return f"https://archive.org/details/{identifier}"
        raise ValueError("Unrecognized archive metadata response")
    except (aiohttp.ClientError, asyncio.TimeoutError, ValueError) as error:
        logging.warning("Archive preflight failed for %s, continuing normally: %s", identifier, error)
        return None


def determine_url_type(url):
    parsed = urlparse(url)
    path = parsed.path
    query = parse_qs(parsed.query)

    if "/shorts/" in path: return "Short"
    if "/live/" in path: return "Live"
    if "/playlist" in path or "list" in query: return "Playlist"
    if "/channel/" in path or "/c/" in path or "/@" in path: return "Channel"
    if "youtu.be" in parsed.hostname or "/watch" in path: return "Video"
    return "Link"

def get_category_for_url_type(url_type):
    if url_type in ["Short", "Live", "Video"]:
        return CAT_VIDEOS
    elif url_type == "Playlist":
        return CAT_PLAYLISTS
    elif url_type == "Channel":
        return CAT_CHANNELS
    return None

async def init_excluded_db():
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        await db.execute("PRAGMA journal_mode=WAL;")
        await db.execute("""
            CREATE TABLE IF NOT EXISTS excluded (
                video_id TEXT PRIMARY KEY,
                category TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                expires_at DATETIME
            )
        """)

        cursor = await db.execute("PRAGMA table_info(excluded)")
        columns = {row[1] for row in await cursor.fetchall()}
        if "expires_at" not in columns:
            await db.execute("ALTER TABLE excluded ADD COLUMN expires_at DATETIME")

        await db.execute("""
            CREATE INDEX IF NOT EXISTS idx_excluded_expires_at
            ON excluded(expires_at)
        """)
        await db.commit()

async def is_url_excluded_globally(video_id):
    if not video_id:
        return False

    await remove_expired_global_exclusions(video_id)

    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("SELECT 1 FROM excluded WHERE video_id = ?", (video_id,))
        return await cursor.fetchone() is not None

async def add_to_global_excluded_file(video_id, category):
    if not video_id or not category: return
    expiry_modifier = f"+{STANDARD_EXCLUSION_RETENTION_DAYS} days"
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        await db.execute("""
            INSERT INTO excluded (video_id, category, timestamp, expires_at)
            VALUES (?, ?, CURRENT_TIMESTAMP, datetime('now', ?))
            ON CONFLICT(video_id) DO UPDATE SET
                category = excluded.category,
                timestamp = CURRENT_TIMESTAMP,
                expires_at = datetime('now', ?)
        """, (video_id, category, expiry_modifier, expiry_modifier))
        await db.commit()

async def make_global_exclusion_permanent(video_id):
    if not video_id:
        return False

    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("""
            UPDATE excluded
            SET expires_at = NULL
            WHERE video_id = ?
        """, (video_id,))
        await db.commit()
        return cursor.rowcount > 0

async def set_global_exclusion_expiry(video_id):
    if not video_id:
        return False

    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("""
            UPDATE excluded
            SET expires_at = datetime('now', '+1 hour')
            WHERE video_id = ?
        """, (video_id,))
        await db.commit()
        return cursor.rowcount > 0

async def remove_expired_global_exclusions(video_id=None):
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        if video_id is None:
            cursor = await db.execute("""
                DELETE FROM excluded
                WHERE expires_at IS NOT NULL
                  AND expires_at <= CURRENT_TIMESTAMP
            """)
        else:
            cursor = await db.execute("""
                DELETE FROM excluded
                WHERE video_id = ?
                  AND expires_at IS NOT NULL
                  AND expires_at <= CURRENT_TIMESTAMP
            """, (video_id,))

        await db.commit()
        return cursor.rowcount

async def remove_global_exclusion_after_expiry(video_id):
    try:
        await asyncio.sleep(RATE_LIMIT_EXCLUSION_SECONDS)
        removed = await remove_expired_global_exclusions(video_id)
        if removed:
            logging.info(f"Removed expired rate-limit exclusion for {video_id}")
    except asyncio.CancelledError:
        raise
    except Exception as e:
        logging.error(f"Failed to remove expired rate-limit exclusion for {video_id}: {e}")

async def remove_from_global_excluded_file(video_id):
    if not video_id: return False
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("DELETE FROM excluded WHERE video_id = ?", (video_id,))
        await db.commit()
        return cursor.rowcount > 0

def clean_youtube_url(text):
    url_regex = r'(https?://[^\s<>"]+)'
    matches = re.findall(url_regex, text)
    
    for raw_url in matches:
        raw_url = clean_extracted_url(raw_url)
        parsed = urlparse(raw_url)
        
        if parsed.hostname not in YOUTUBE_HOSTS:
            continue

        query_params = parse_qs(parsed.query, keep_blank_values=True)
        is_valid_type = False
        if 'youtu.be' in parsed.hostname: is_valid_type = True
        elif parsed.path == '/watch' and 'v' in query_params: is_valid_type = True
        elif parsed.path.startswith('/shorts/'): is_valid_type = True
        elif parsed.path.startswith('/live/'): is_valid_type = True
        elif parsed.path.startswith('/playlist') and 'list' in query_params: is_valid_type = True
        elif parsed.path.startswith('/@') or parsed.path.startswith('/channel') or parsed.path.startswith('/c/'): is_valid_type = True
            
        if not is_valid_type: continue

        # We do NOT remove list param here yet if it exists, to allow detection in on_message
        for param in list(query_params):
            if param.lower() in YOUTUBE_REMOVABLE_PARAMS:
                del query_params[param]

        fragment = parsed.fragment
        if YOUTUBE_TIMESTAMP_FRAGMENT.fullmatch(fragment):
            fragment = ''
        else:
            fragment_params = parse_qs(fragment, keep_blank_values=True)
            if fragment_params:
                for param in list(fragment_params):
                    if param.lower() in YOUTUBE_TIMESTAMP_PARAMS:
                        del fragment_params[param]
                fragment = urlencode(fragment_params, doseq=True)
        
        new_query = urlencode(query_params, doseq=True)
        clean_url = urlunparse((parsed.scheme, parsed.netloc, parsed.path, parsed.params, new_query, fragment))
        
        return clean_url, get_video_id(clean_url)
    
    return None

def clean_youtube_urls(text):
    url_regex = r'(https?://[^\s<>"]+)'
    matches = re.findall(url_regex, text)
    cleaned_urls = []

    for raw_url in matches:
        result = clean_youtube_url(raw_url)
        if result:
            cleaned_urls.append(result)

    return cleaned_urls

# --- GitHub API & Archiving Logic ---

async def trigger_workflow(url, trace_id, free_space=False, ignore_existing_item=False):
    account, secret_updated_at = await client.choose_youtube_cookie()
    dispatch_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/workflows/{WORKFLOW_FILE}/dispatches"
    
    payload = {
        "ref": "main", 
        "inputs": {
            "url": url,
            "trace_id": trace_id,
            "free_space": str(free_space).lower(),
            "youtube_account": str(account),
            "ignore_existing_item": str(ignore_existing_item).lower()
        }
    }

    async with client.session.post(dispatch_url, json=payload, headers=GITHUB_HEADERS) as resp:
        if resp.status not in (204, 201):
            text = await resp.text()
            return False, f"Failed to dispatch workflow: {resp.status} {text}", None
    
    return True, None, (account, secret_updated_at)

async def scan_and_dispatch_description_links(parent_video_id, parent_trace_id):
    if not parent_video_id:
        return

    item_identifier = f"youtube-{parent_video_id}"
    metadata_url = f"https://archive.org/metadata/{item_identifier}"

    logging.info(f"Checking description links for {item_identifier}")

    try:
        async with client.session.get(metadata_url) as resp:
            if resp.status != 200:
                logging.warning(f"Failed to fetch metadata for {item_identifier}: {resp.status}")
                return
            
            data = await resp.json()
            
        description = data.get('metadata', {}).get('description', '')
        if not description:
            return

        url_regex = r'(https?://[^\s<>"]+)'
        matches = re.findall(url_regex, description)
        
        unique_links = set()
        git_links = set()
        git_domains = ['github.com', 'gitlab.com', 'bitbucket.org', 'codeberg.org', 'gitea.com']

        for raw_link in matches:
            cleaned_raw = clean_extracted_url(raw_link)
            parsed = urlparse(cleaned_raw)
            if parsed.hostname and any(domain in parsed.hostname for domain in git_domains):
                git_links.add(cleaned_raw)
                continue

            res = clean_youtube_url(cleaned_raw)
            if res:
                clean_url, new_video_id = res
                if new_video_id and new_video_id != parent_video_id:
                    unique_links.add((clean_url, new_video_id))

        for git_url in git_links:
            trace_id = parent_trace_id
            # using 'test' as the repo name per requirements for git dispatches
            dispatch_url = f"https://api.github.com/repos/{REPO_OWNER}/test/actions/workflows/t-git.yml/dispatches"
            payload = {
                "ref": "main", 
                "inputs": {"url": git_url, "trace_id": trace_id}
            }
            try:
                logging.info(f"Found new git link in description of {parent_video_id}: {git_url}, dispatching to t-git.yml")
                await client.session.post(dispatch_url, json=payload, headers=GITHUB_HEADERS)
                await asyncio.sleep(2)
            except Exception as e:
                logging.error(f"Failed to auto-dispatch git link {git_url}: {e}")

        for url, vid_id in unique_links:
            try:
                if await check_existing_archive(url):
                    continue
            except RuntimeError:
                continue
            if await is_url_excluded_globally(vid_id):
                continue
            
            logging.info(f"Found new link in description of {parent_video_id}: {url}, dispatching")
            
            # Determine category for sub-link (usually video)
            sub_type = determine_url_type(url)
            sub_cat = get_category_for_url_type(sub_type)
            await add_to_global_excluded_file(vid_id, sub_cat)
            
            # Description links need the same cookie selection, failure detection,
            # and silent retries as ordinary requests, rather than an untracked POST
            system_user_id = client.user.id
            client.queued_jobs[system_user_id].append(
                (url, sub_type, True, None, None, system_user_id, True, None, True)
            )
            await check_and_process_queue(system_user_id)
            await client.save_state()

    except Exception as e:
        logging.error(f"Error scanning description for {parent_video_id}: {e}")

# --- EXECUTION LOGIC (Extracted from on_message) ---

def extract_tasks_from_text(text):
    tasks_to_process = []
    seen_task_urls = set()

    def add_task(url, task_type, silent):
        if url in seen_task_urls:
            return
        seen_task_urls.add(url)
        tasks_to_process.append((url, task_type, silent))

    cleaned_results = clean_youtube_urls(text)
    for clean_url, _ in cleaned_results:
        parsed = urlparse(clean_url)
        qs = parse_qs(parsed.query)
        if 'v' in qs and 'list' in qs and parsed.path == '/watch':
            vid_id = qs['v'][0]
            list_id = qs['list'][0]
            
            video_url = f"https://www.youtube.com/watch?v={vid_id}"
            add_task(video_url, "Video", False)
            
            playlist_url = f"https://www.youtube.com/playlist?list={list_id}"
            add_task(playlist_url, "Playlist", True)
        else:
            url_type = determine_url_type(clean_url)
            add_task(clean_url, url_type, False)
            
    return tasks_to_process

async def complete_existing_archive(target_url, url_type, archive_url, guild_id, user_id,
                                    source=None, is_silent=False, batch_id=None, send_response=None):
    """Record a metadata match locally and show the normal completion sequence"""
    video_id = get_video_id(target_url)
    await add_to_global_excluded_file(video_id, get_category_for_url_type(url_type))
    await make_global_exclusion_permanent(video_id)
    trace_id = str(uuid.uuid4())[:8]
    # No GitHub run exists, the trace identifies this local history record
    await log_history(guild_id, user_id, target_url, "Already archived", None, trace_id)
    status_msg = None
    if not is_silent and not batch_id and source:
        initial = f"Sending request to preserve YouTube {url_type}\n\n[||Target||](<{target_url}>)"
        try:
            if send_response:
                status_msg = await send_response(initial)
            elif getattr(getattr(source, "author", None), "id", None) == client.user.id:
                status_msg = source
                await status_msg.edit(content=initial)
            else:
                status_msg = await source.reply(initial)
            await status_msg.edit(content=f"<a:loading:1455572437277348005> YouTube {url_type} is being preserved\n\n||Trace ID: `{trace_id}`||")
        except Exception as error:
            logging.warning("Could not show local archive status: %s", error)
    await asyncio.sleep(5)
    if status_msg:
        try:
            await status_msg.edit(content=format_existing_archive(url_type, archive_url, trace_id),
                                  embed=None, suppress=True)
        except Exception as error:
            logging.warning("Could not show existing archive completion: %s", error)
    if batch_id:
        await client.update_batch_progress(batch_id, is_success=True, archive_urls=[archive_url])


async def dispatch_archive_tasks(tasks_to_process, user, source, guild_id, free_space):
    is_interaction = isinstance(source, discord.Interaction)
    is_dm = guild_id is None
    is_bot_request = bool(getattr(user, "bot", False))

    async def send_response(text, ephemeral=False, suppress_embeds=False):
        if source.response.is_done():
            return await source.followup.send(text, ephemeral=ephemeral, wait=True, suppress_embeds=suppress_embeds)
        await source.response.send_message(text, ephemeral=ephemeral, suppress_embeds=suppress_embeds)
        return await source.original_response()

    if await is_user_globally_excluded(user.id):
        if is_interaction:
            await send_response(
                "You are globally banned from using this bot",
                ephemeral=True
            )
        return

    # Acknowledge slash commands before network I/O, no archive request is sent
    if is_interaction and not source.response.is_done():
        await source.response.defer()
    valid_tasks = []
    preflight_stopped = False
    for target_url, url_type, is_silent in tasks_to_process:
        if not is_dm and await is_url_type_excluded(guild_id, url_type):
            continue
        target_id = get_video_id(target_url)
        if await is_url_excluded_globally(target_id):
            continue
        archive_url = await check_existing_archive(target_url)
        if archive_url:
            preflight_stopped = True
            await complete_existing_archive(
                target_url, url_type, archive_url, guild_id, user.id,
                source=source, is_silent=is_silent and not is_interaction,
                send_response=send_response if is_interaction else None
            )
            continue
        valid_tasks.append((target_url, url_type, is_silent))

    tasks_to_process = valid_tasks
    if not tasks_to_process:
        if preflight_stopped:
            return
        if is_interaction:
            await send_response("The provided URL(s) are excluded from archiving", ephemeral=True)
        return

    if user.id != OWNER_ID and not is_bot_request:
        current_jobs = client.active_jobs[user.id]
        current_queue = len(client.queued_jobs[user.id])
        available_slots = max(0, MAX_CONCURRENT_JOBS - current_jobs) + max(0, MAX_QUEUED_JOBS - current_queue)
        
        user_active_channels = sum(
            1 for trace in client.pending_traces.values()
            if trace["user_id"] == user.id and trace["url_type"] == "Channel"
        )
        user_active_channels += sum(
            1 for job in client.queued_jobs[user.id]
            if job[1] == "Channel"
        )

        user_active_playlists = sum(
            1 for trace in client.pending_traces.values()
            if trace["user_id"] == user.id and trace["url_type"] == "Playlist"
        )
        user_active_playlists += sum(
            1 for job in client.queued_jobs[user.id]
            if job[1] == "Playlist"
        )
        
        filtered_tasks = []
        skipped_channels = False
        skipped_playlists = False
        for target_url, url_type, is_silent in tasks_to_process:
            if url_type == "Channel":
                if user_active_channels >= 1:
                    skipped_channels = True
                    continue
                user_active_channels += 1
            elif url_type == "Playlist":
                if user_active_playlists >= 1:
                    skipped_playlists = True
                    continue
                user_active_playlists += 1
            filtered_tasks.append((target_url, url_type, is_silent))
            
        if not filtered_tasks:
            if skipped_channels and skipped_playlists:
                msg = "You can only archive 1 channel and 1 playlist at a time"
            elif skipped_channels:
                msg = "You can only archive 1 channel at a time"
            elif skipped_playlists:
                msg = "You can only archive 1 playlist at a time"
            else:
                msg = None
                
            if msg:
                if is_interaction:
                    await send_response(msg, ephemeral=True)
                else:
                    await source.reply(msg, delete_after=10)
                return

        if filtered_tasks and not is_interaction:
            if skipped_channels and skipped_playlists:
                await source.reply("Some channel and playlist links were skipped because you can only archive 1 of each at a time", delete_after=10)
            elif skipped_channels:
                await source.reply("Some channel links were skipped because you can only archive 1 channel at a time", delete_after=10)
            elif skipped_playlists:
                await source.reply("Some playlist links were skipped because you can only archive 1 playlist at a time", delete_after=10)

        tasks_to_process = filtered_tasks

        if len(tasks_to_process) > available_slots:
            tasks_to_process = tasks_to_process[:available_slots]
            if not is_interaction:
                await source.reply(f"Some links were skipped because you reached the maximum limit of {MAX_CONCURRENT_JOBS} active and {MAX_QUEUED_JOBS} queued jobs", delete_after=10)

    if not tasks_to_process:
        if is_interaction:
            await send_response(f"You have reached the maximum limit of {MAX_CONCURRENT_JOBS} active and {MAX_QUEUED_JOBS} queued jobs", ephemeral=True)
        return

    batch_id = None
    if len(tasks_to_process) > 1:
        type_counts = defaultdict(int)
        for _, url_type, _ in tasks_to_process:
            type_counts[url_type] += 1

        def pluralize(kind, count):
            return kind if count == 1 else f"{kind}s"

        counts_text = ", ".join(f"{count} {pluralize(kind, count)}" for kind, count in sorted(type_counts.items()))
        batch_id = str(uuid.uuid4())[:8]
        batch_text = f"<a:loading:1455572437277348005> YouTube links are being preserved ({counts_text})\n\n||Batch ID: `{batch_id}`||"
        
        if is_interaction:
            batch_status_msg = await send_response(batch_text)
        else:
            batch_status_msg = await source.reply(batch_text)
            
        client.batch_jobs[batch_id] = {
            "status_msg": batch_status_msg,
            "total": len(tasks_to_process),
            "completed": 0,
            "success": 0,
            "failed": 0,
            "archive_urls": []
        }

    for target_url, url_type, is_silent in tasks_to_process:
        effective_silent = is_silent or batch_id is not None
        current_jobs = client.active_jobs[user.id]

        message_for_execution = None
        
        if batch_id:
            message_for_execution = None
        else:
            if is_interaction:
                if current_jobs >= MAX_CONCURRENT_JOBS:
                    queue_pos = len(client.queued_jobs[user.id]) + 1
                    text = (
                        f"Your request for the YouTube {url_type} has been added to the queue (Position: {queue_pos})\n\n"
                        f"||You have {current_jobs}/{MAX_CONCURRENT_JOBS} active archive requests running, please wait for one of them to finish||"
                    )
                else:
                    text = f"Sending request to preserve YouTube {url_type}\n\n[||Target||](<{target_url}>)"
                
                message_for_execution = await send_response(text)
            else:
                if current_jobs >= MAX_CONCURRENT_JOBS and not effective_silent:
                    queue_pos = len(client.queued_jobs[user.id]) + 1
                    await source.reply(
                        f"Your request for the YouTube {url_type} has been added to the queue (Position: {queue_pos})\n\n"
                        f"||You have {current_jobs}/{MAX_CONCURRENT_JOBS} active archive requests running, please wait for one of them to finish||",
                        delete_after=10
                    )
                message_for_execution = source
        
        if current_jobs >= MAX_CONCURRENT_JOBS:
            client.queued_jobs[user.id].append(
                (
                    target_url,
                    url_type,
                    effective_silent,
                    message_for_execution,
                    guild_id,
                    user.id,
                    free_space,
                    batch_id,
                    is_bot_request
                )
            )
            continue
        
        client.active_jobs[user.id] += 1
        
        await execute_archive_request(
            target_url,
            url_type,
            effective_silent,
            message_for_execution,
            guild_id,
            user.id,
            free_space=free_space,
            batch_id=batch_id,
            is_bot_request=is_bot_request
        )

async def execute_archive_request(
    target_url,
    url_type,
    is_silent,
    original_message,
    guild_id,
    user_id,
    free_space=False,
    batch_id=None,
    is_bot_request=False,
    is_cookie_retry=False,
    ignore_existing_item=False
):
    """
    Handles the actual execution: triggering workflow, updating UI, logging to DB, and starting monitor
    """
    # Recheck after a queue wait or retry before cookies or dispatch
    archive_url = await check_existing_archive(target_url)
    if archive_url:
        try:
            await complete_existing_archive(
                target_url, url_type, archive_url, guild_id, user_id,
                source=original_message, is_silent=is_silent, batch_id=batch_id
            )
        finally:
            client.active_jobs[user_id] = max(0, client.active_jobs[user_id] - 1)
            await client.save_state()
            await check_and_process_queue(user_id)
        return

    # Initial User Feedback (Only if not silent)
    status_msg = original_message if is_cookie_retry else None
    if not is_cookie_retry and not batch_id and not is_silent and original_message:
        try:
            if getattr(original_message, "author", None) and original_message.author.id == client.user.id:
                status_msg = original_message
            else:
                status_msg = await original_message.reply(f"Sending request to preserve YouTube {url_type}\n\n[||Target||](<{target_url}>)")
        except:
            pass

    bot_trace_slot_acquired = False
    if is_bot_request:
        await client.bot_trace_lock.acquire()
        bot_trace_slot_acquired = True

    request_started_at = datetime.now(timezone.utc)
    trace_id = BOT_REQUEST_TRACE_ID if is_bot_request else str(uuid.uuid4())[:8]
    
    try:
        success, error, cookie_selection = await trigger_workflow(
            target_url, trace_id, free_space=free_space, ignore_existing_item=ignore_existing_item
        )
        
        if success:
            # Add to exclusions with specific category
            category = get_category_for_url_type(url_type)
            target_id = get_video_id(target_url)
            await add_to_global_excluded_file(target_id, category)
            
            # Use a string UUID for the run_id to avoid integer overflow
            # The history table schema expects run_id to be INTEGER, but SQLite is dynamic
            # However, to be safe and cleaner, let's use a smaller random int
            history_run_id = int(uuid.uuid4().int % (2**63 - 1))
            
            await log_history(guild_id, user_id, target_url, "queued", history_run_id, trace_id)
            
            # Store context for WebSocket handler
            client.pending_traces[trace_id] = {
                "user_id": user_id,
                "target_url": target_url,
                "url_type": url_type,
                "is_silent": is_silent,
                "status_msg": status_msg,
                "history_run_id": history_run_id,
                "guild_id": guild_id,
                "free_space": free_space,
                "start_time": request_started_at,
                "batch_id": batch_id,
                "is_bot_request": is_bot_request,
                "is_cookie_retry": is_cookie_retry,
                "ignore_existing_item": ignore_existing_item,
                "youtube_account": cookie_selection[0],
                "cookie_secret_updated_at": cookie_selection[1]
            }
            bot_trace_slot_acquired = False
            await client.save_state()
            
            if not is_cookie_retry and not batch_id and not is_silent and status_msg:
                try:
                    await status_msg.edit(content=f"<a:loading:1455572437277348005> YouTube {url_type} is being preserved\n\n||Trace ID: `{trace_id}`||")
                except:
                    pass
            
            # No monitor_run task needed anymore, we wait for WS connection
        else:
            if not is_silent and status_msg:
                try:
                    await status_msg.edit(content=f"Error starting workflow: {error}")
                except:
                    pass
            # If failed to start, we must manually decrement here
            client.active_jobs[user_id] = max(0, client.active_jobs[user_id] - 1)
            await check_and_process_queue(user_id)
            if batch_id:
                await client.update_batch_progress(batch_id, is_success=False)

    except YouTubeCookiesUnavailable:
        # Preserve the original message and batch silently while all cookies wait
        client.queued_jobs[user_id].append((
            target_url, url_type, is_silent, status_msg or original_message, guild_id, user_id,
            free_space, batch_id, is_bot_request, is_cookie_retry, ignore_existing_item
        ))
        client.active_jobs[user_id] = max(0, client.active_jobs[user_id] - 1)
        await client.save_state()
    except Exception as e:
        logging.error(f"Critical error in processing {target_url}: {e}")
        if not is_silent and status_msg:
            try:
                await status_msg.edit(content=f"Bot internal error: {e}")
            except:
                pass
        
        client.active_jobs[user_id] = max(0, client.active_jobs[user_id] - 1)
        await check_and_process_queue(user_id)
        if batch_id:
            await client.update_batch_progress(batch_id, is_success=False)
    finally:
        if bot_trace_slot_acquired and client.bot_trace_lock.locked():
            client.bot_trace_lock.release()

async def check_and_process_queue(user_id):
    """Checks if there are queued jobs for the user and starts the next one"""
    if not client.available_youtube_accounts() or client.active_jobs[user_id] >= MAX_CONCURRENT_JOBS:
        return
    if client.queued_jobs[user_id]:
        next_job = client.queued_jobs[user_id].pop(0)
        # Increment active_jobs immediately so the slot is taken
        client.active_jobs[user_id] += 1
        
        # Unpack and run
        # job format: (target_url, url_type, is_silent, original_message, guild_id, user_id)
        # Note: execute_archive_request takes user_id as last arg, but it's in the tuple
        
        # Notify user their queued job is starting (optional, but good UX if not silent)
        if not next_job[2] and next_job[3]: # is_silent, original_message
             # We don't necessarily need to edit the old "queued" message, 
             # execute_archive_request reuses an existing status message when one is available
             pass

        asyncio.create_task(execute_archive_request(*next_job))

# --- Pagination View ---

class HistoryPaginationView(View):
    def __init__(self, user_id, current_page, total_count, per_page=5):
        super().__init__(timeout=180)
        self.user_id = user_id
        self.current_page = current_page
        self.total_count = total_count
        self.per_page = per_page
        self.update_buttons()

    def update_buttons(self):
        self.prev_button.disabled = self.current_page == 0
        
        max_pages = (self.total_count - 1) // self.per_page
        self.next_button.disabled = self.current_page >= max_pages

    @discord.ui.button(label="Previous", style=discord.ButtonStyle.primary, custom_id="hist_prev")
    async def prev_button(self, interaction: discord.Interaction, button: Button):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your history", ephemeral=True)
            return

        self.current_page -= 1
        await self.update_message(interaction)

    @discord.ui.button(label="Next", style=discord.ButtonStyle.primary, custom_id="hist_next")
    async def next_button(self, interaction: discord.Interaction, button: Button):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your history", ephemeral=True)
            return

        self.current_page += 1
        await self.update_message(interaction)

    async def update_message(self, interaction: discord.Interaction):
        rows, total = await get_history_page(self.user_id, self.current_page, self.per_page)
        self.total_count = total
        self.update_buttons()

        if not rows:
            embed = discord.Embed(title="Archive History Log", description="No logs found", color=discord.Color.blue())
        else:
            embed = discord.Embed(title=f"Archive History Log (Page {self.current_page + 1})", color=discord.Color.blue())
            for url, status, timestamp, run_id, trace_id in rows:
                trace_info = f"\nTrace ID: `{trace_id}`" if trace_id else ""
                embed.add_field(name=f"[{timestamp}]", value=f"Status: {status}\nTarget: {url}{trace_info}", inline=False)
        
        await interaction.response.edit_message(embed=embed, view=self)

# --- Slash Commands ---

@client.tree.command(name="help", description="Show information about the bot's commands")
async def help_cmd(interaction: discord.Interaction):
    embed = discord.Embed(
        title="YTMA Bot Help", 
        description="This bot mirrors YouTube links to the Internet Archive", 
        color=discord.Color.red()
    )
    embed.add_field(
        name="How It Works",
        value="Paste a YouTube URL in a designated channel and the bot will archive it automatically, You can also submit one manually with `/archive` or `!archive <url>`",
        inline=False
    )
    embed.add_field(
        name="Large Downloads",
        value="For large stuff, set `/archive`'s `free_space` option to `True`, or use `!archive <url> --large` (short form: `-l`), Large mode frees storage in the job but the job might take longer to start (approximately 2-3~ minutes)",
        inline=False
    )
    embed.add_field(
        name="User Commands",
        value="`/archive` - Manually archive a YouTube URL\n`/history` - View your archive history\n`/deletehistory` - Clear your archive history\n`/howmanyjobs [user]` - View a user's lifetime archive job count\n`/leaderboard` - View the archive leaderboard\n`/ping` - Check the bot's latency",
        inline=False
    )
    embed.add_field(
        name="Admin Commands",
        value="`/excludeurl` / `/unexcludeurl` - Manage archivable URL types in your server\n`/excludechannel` / `/unexcludechannel` - Manage excluded Discord channels\n`/excludeuser` / `/unexcludeuser` - Manage excluded users in your server\n`/enableallmessages` / `/disableallmessages` - Toggle automatic scanning of messages for YouTube URLs",
        inline=False
    )
    if interaction.user.id == OWNER_ID:
        embed.add_field(
            name="Owner Commands",
            value="`/restart` - Restart the bot\n`/shutdown` - Save state and stop the hosting workflow without starting another session",
            inline=False
        )
    await interaction.response.send_message(embed=embed, ephemeral=False)

@client.tree.command(name="excludeurl", description="Exclude a specific URL type from being archived in this server")
@app_commands.describe(url_type="The type of URL to exclude")
@app_commands.choices(url_type=[
    app_commands.Choice(name="Video", value="Video"),
    app_commands.Choice(name="Shorts", value="Short"),
    app_commands.Choice(name="Live Stream", value="Live"),
    app_commands.Choice(name="Playlist", value="Playlist"),
    app_commands.Choice(name="Channel", value="Channel"),
])
@app_commands.checks.has_permissions(manage_messages=True)
async def exclude_url(interaction: discord.Interaction, url_type: app_commands.Choice[str]):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return

    success = await add_exclusion(interaction.guild.id, "url_type", url_type.value, interaction.user.name)
    
    if success:
        await interaction.response.send_message(f"Type **{url_type.name}** has been excluded for this server", ephemeral=True)
    else:
        await interaction.response.send_message(f"Type **{url_type.name}** is already excluded in this server", ephemeral=True)

@client.tree.command(name="unexcludeurl", description="Allow a previously excluded URL type in this server")
@app_commands.describe(url_type="The type of URL to un-exclude")
@app_commands.choices(url_type=[
    app_commands.Choice(name="Video", value="Video"),
    app_commands.Choice(name="Shorts", value="Short"),
    app_commands.Choice(name="Live Stream", value="Live"),
    app_commands.Choice(name="Playlist", value="Playlist"),
    app_commands.Choice(name="Channel", value="Channel"),
])
@app_commands.checks.has_permissions(manage_messages=True)
async def unexclude_url(interaction: discord.Interaction, url_type: app_commands.Choice[str]):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return

    success = await remove_exclusion(interaction.guild.id, "url_type", url_type.value)
    
    if success:
        await interaction.response.send_message(f"Type **{url_type.name}** has been un-excluded", ephemeral=True)
    else:
        await interaction.response.send_message(f"Type **{url_type.name}** was not found in the exclusion list", ephemeral=True)

@client.tree.command(name="removeurl", description="Remove a video or URL from the global excluded urls database (BOT OWNER ONLY)")
@app_commands.describe(url="The YouTube URL or video ID to remove")
async def remove_url(interaction: discord.Interaction, url: str):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    video_id = get_video_id(url)
    if not video_id:
        video_id = url.strip()

    success = await remove_from_global_excluded_file(video_id)
    if success:
        await interaction.response.send_message(f"Successfully removed `{video_id}` from the global exclusion database", ephemeral=True)
    else:
        await interaction.response.send_message(f"Could not find `{video_id}` in the global exclusion database", ephemeral=True)

@client.tree.command(name="excludechannel", description="Add channel to exclusion")
@app_commands.checks.has_permissions(manage_channels=True)
async def exclude_channel(interaction: discord.Interaction, channel: discord.TextChannel):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return
    
    success = await add_exclusion(interaction.guild.id, "channel", channel.id, interaction.user.name)
    if success:
        await interaction.response.send_message(f"Channel {channel.mention} has been added to exclusion", ephemeral=True)
    else:
        await interaction.response.send_message("Channel is already in exclusion", ephemeral=True)

@client.tree.command(name="unexcludechannel", description="Remove channel from exclusion")
@app_commands.checks.has_permissions(manage_channels=True)
async def unexclude_channel(interaction: discord.Interaction, channel: discord.TextChannel):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return
    
    success = await remove_exclusion(interaction.guild.id, "channel", channel.id)
    if success:
        await interaction.response.send_message(f"Channel {channel.mention} has been removed from exclusion", ephemeral=True)
    else:
        await interaction.response.send_message("Channel was not excluded", ephemeral=True)

@client.tree.command(name="excludeuser", description="Add user to exclusion")
@app_commands.checks.has_permissions(ban_members=True)
async def exclude_user(interaction: discord.Interaction, user: discord.User):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return

    success = await add_exclusion(interaction.guild.id, "user", user.id, interaction.user.name)
    if success:
        await interaction.response.send_message(f"User ID `{user.id}` added to exclusion", ephemeral=True)
    else:
        await interaction.response.send_message("User already present in exclusion", ephemeral=True)

@client.tree.command(name="unexcludeuser", description="Remove user from exclusion")
@app_commands.checks.has_permissions(ban_members=True)
async def unexclude_user(interaction: discord.Interaction, user: discord.User):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return

    success = await remove_exclusion(interaction.guild.id, "user", user.id)
    if success:
        await interaction.response.send_message(f"User ID `{user.id}` removed from exclusion", ephemeral=True)
    else:
        await interaction.response.send_message("User was not excluded", ephemeral=True)

def parse_discord_user_id(value: str):
    """Parse a raw Discord user ID or copied user mention"""
    match = re.fullmatch(r"(?:<@!?(\d{17,20})>|(\d{17,20}))", value.strip())
    if not match:
        return None
    return int(match.group(1) or match.group(2))

@client.tree.command(name="globalexcludeuser", description="Globally exclude a user by Discord ID")
@app_commands.describe(user_id="The raw Discord user ID or a copied user mention")
async def global_exclude(interaction: discord.Interaction, user_id: str):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    target_user_id = parse_discord_user_id(user_id)
    if target_user_id is None:
        await interaction.response.send_message(
            "Invalid Discord user ID, enter a 17-20 digit ID or paste a user mention",
            ephemeral=True
        )
        return

    if await add_global_user_exclusion(target_user_id, interaction.user.name):
        await interaction.response.send_message(
            f"User ID `{target_user_id}` has been globally excluded",
            ephemeral=True
        )
    else:
        await interaction.response.send_message(
            f"User ID `{target_user_id}` is already globally excluded",
            ephemeral=True
        )

@client.tree.command(name="globalunexcludeuser", description="Remove a user ID from global exclusion")
@app_commands.describe(user_id="The raw Discord user ID or a copied user mention")
async def global_unexclude(interaction: discord.Interaction, user_id: str):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    target_user_id = parse_discord_user_id(user_id)
    if target_user_id is None:
        await interaction.response.send_message(
            "Invalid Discord user ID, enter a 17-20 digit ID or paste a user mention",
            ephemeral=True
        )
        return

    if await remove_global_user_exclusion(target_user_id):
        await interaction.response.send_message(
            f"User ID `{target_user_id}` has been removed from global exclusion",
            ephemeral=True
        )
    else:
        await interaction.response.send_message(
            f"User ID `{target_user_id}` is not in the global exclusion list",
            ephemeral=True
        )

@client.tree.command(name="allowbotmessages", description="Allow other bots' messages with YouTube URLs to trigger archive requests (BOT OWNER ONLY)")
async def allow_bot_messages(interaction: discord.Interaction):
    if not interaction.guild or interaction.guild.id != 1228824233224966276:
        await interaction.response.send_message("This command can only be used in the designated server", ephemeral=True)
        return

    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("Only the bot owner can use this command", ephemeral=True)
        return

    success = await set_allow_bot_messages(interaction.guild.id, interaction.user.name)
    
    if success:
        await interaction.response.send_message(
            "Bot messages with YouTube URLs will now trigger archive requests in this server",
            ephemeral=True
        )
    else:
        await interaction.response.send_message("Bot messages are already allowed in this server", ephemeral=True)

@client.tree.command(name="disallowbotmessages", description="Stop allowing other bots' messages to trigger archive requests (BOT OWNER ONLY)")
async def disallow_bot_messages(interaction: discord.Interaction):
    if not interaction.guild or interaction.guild.id != 1228824233224966276:
        await interaction.response.send_message("This command can only be used in the designated server", ephemeral=True)
        return

    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("Only the bot owner can use this command", ephemeral=True)
        return

    success = await unset_allow_bot_messages(interaction.guild.id)
    
    if success:
        await interaction.response.send_message("Bot messages will no longer trigger archive requests in this server", ephemeral=True)
    else:
        await interaction.response.send_message("Bot messages were already not allowed in this server", ephemeral=True)

@client.tree.command(name="history", description="Query your archive history logs")
async def history(interaction: discord.Interaction):
    rows, total_count = await get_history_page(interaction.user.id, 0, 5)
    
    if not rows:
        await interaction.response.send_message("No logs found for your account", ephemeral=True)
        return

    embed = discord.Embed(title="Archive History Log (Page 1)", color=discord.Color.blue())
    for url, status, timestamp, run_id, trace_id in rows:
        trace_info = f"\nTrace ID: `{trace_id}`" if trace_id else ""
        embed.add_field(name=f"[{timestamp}]", value=f"Status: {status}\nTarget: {url}{trace_info}", inline=False)
    
    view = HistoryPaginationView(interaction.user.id, 0, total_count, 5)
    await interaction.response.send_message(embed=embed, view=view, ephemeral=True)

@client.tree.command(name="deletehistory", description="Delete your archive log history")
async def delete_history(interaction: discord.Interaction):
    await clear_user_history(interaction.user.id)
    await interaction.response.send_message("Your archive history logs have successfully been deleted", ephemeral=True)

@client.tree.command(name="enableallmessages", description="Turn on reading all messages for YouTube URLs")
@app_commands.checks.has_permissions(manage_messages=True)
async def enableallmessages(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return
        
    await enable_all_messages(interaction.guild.id)
    await interaction.response.send_message("Reading all messages has been turned on", ephemeral=True)

@client.tree.command(name="disableallmessages", description="Turn off reading all messages for YouTube URLs")
@app_commands.checks.has_permissions(manage_messages=True)
async def disableallmessages(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return
        
    await disable_all_messages(interaction.guild.id, interaction.user.name)
    await interaction.response.send_message("Reading all messages has been turned off", ephemeral=True)

@client.tree.command(name="archive", description="Manually archive a YouTube URL")
@app_commands.describe(url="The YouTube URL to archive", free_space="Enable free space for large videos")
async def archive_cmd(interaction: discord.Interaction, url: str, free_space: bool = False):
    is_dm = interaction.guild is None
    guild_id = interaction.guild.id if interaction.guild else None

    if not is_dm:
        if await is_user_or_channel_excluded(interaction.user.id, interaction.channel.id, guild_id):
            await interaction.response.send_message("You or this channel are excluded from using the bot", ephemeral=True)
            return

    if not re.fullmatch(r'https?://[^\s<>"]+', url.strip(' <>')):
        await interaction.response.send_message("Invalid YouTube URL", ephemeral=True)
        return

    tasks_to_process = extract_tasks_from_text(url)
    if not tasks_to_process:
        await interaction.response.send_message("Invalid YouTube URL", ephemeral=True)
        return
        
    await dispatch_archive_tasks(tasks_to_process, interaction.user, interaction, guild_id, free_space)

@client.tree.command(name="ping", description="Test the bot's latency")
async def ping(interaction: discord.Interaction):
    await interaction.response.send_message(f"Pong! `{round(client.latency*1000)}ms`", ephemeral=False)

@client.tree.command(name="jobs", description="List every user with a currently active job")
async def jobs(interaction: discord.Interaction):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return
    
    active_users = {uid: count for uid, count in client.active_jobs.items() if count > 0}
    if not active_users:
        await interaction.response.send_message("No active jobs right now")
        return
        
    embed = discord.Embed(title="Current Active Jobs", color=discord.Color.blue())
    description = []
    for uid, count in active_users.items():
        user = client.get_user(uid)
        if not user:
            try:
                user = await client.fetch_user(uid)
            except discord.NotFound:
                pass
        username_str = f" ({user.name})" if user else ""
        description.append(f"<@{uid}>{username_str} ({count} active jobs)")
        
    embed.description = "\n".join(description)
    await interaction.response.send_message(embed=embed)

@client.tree.command(name="howmanyjobs", description="Show a user's archive jobs count")
@app_commands.describe(user="User to check (leave blank to check your job count)")
async def howmanyjobs(interaction: discord.Interaction, user: discord.User = None):
    target_user = user or interaction.user
    job_count = await get_lifetime_job_count(target_user.id)
    job_word = "job" if job_count == 1 else "jobs"

    if target_user.id == interaction.user.id:
        message = f"You did {job_count:,} archive {job_word} in your lifetime"
    else:
        username = discord.utils.escape_markdown(target_user.name)
        message = f"{username} did {job_count:,} archive {job_word} in their lifetime"

    await interaction.response.send_message(
        message,
        ephemeral=False,
        allowed_mentions=discord.AllowedMentions.none(),
    )

@client.tree.command(name="leaderboard", description="Show the archive jobs count leaderboard")
async def leaderboard(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=False)

    await classify_unclassified_leaderboard_accounts()

    top_users, user_rank, total_jobs, total_users = await get_lifetime_leaderboard(
        interaction.user.id,
        limit=10,
    )

    if not top_users:
        await interaction.followup.send("No successful archive jobs have been completed yet")
        return

    medals = {1: "🥇", 2: "🥈", 3: "🥉"}
    lines = []
    for position, (user_id, job_count) in enumerate(top_users, start=1):
        rank_label = medals.get(position, f"`#{position}`")
        job_word = "job" if job_count == 1 else "jobs"
        lines.append(f"{rank_label} <@{user_id}> - **{job_count:,}** {job_word}")

    embed = discord.Embed(
        title="Archive Leaderboard",
        description="\n".join(lines),
        color=discord.Color.blue(),
    )

    top_user_ids = {user_id for user_id, _ in top_users}
    if user_rank and interaction.user.id not in top_user_ids:
        position, job_count = user_rank
        job_word = "job" if job_count == 1 else "jobs"
        embed.add_field(
            name="Your Rank",
            value=f"**#{position:,}** with **{job_count:,}** {job_word}",
            inline=False,
        )

    user_word = "user" if total_users == 1 else "users"
    embed.set_footer(
        text=f"{total_jobs:,} jobs completed by {total_users:,} other {user_word}"
    )
    await interaction.followup.send(embed=embed)

@client.tree.command(name="traceinfo", description="Look up information about a trace ID (BOT OWNER ONLY)")
@app_commands.describe(trace_id="The trace ID to look up")
async def traceinfo(interaction: discord.Interaction, trace_id: str):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    if trace_id not in client.pending_traces:
        # Try to look up in database for past traces
        async with aiosqlite.connect(DB_NAME) as db:
            async with db.execute(
                """
                SELECT user_id, url, status, timestamp, run_id
                FROM history
                WHERE trace_id = ?
                ORDER BY id DESC
                LIMIT 1
                """,
                (trace_id,)
            ) as cursor:
                row = await cursor.fetchone()
                
        if not row:
            await interaction.response.send_message(f"Trace ID `{trace_id}` not found in pending traces or history", ephemeral=True)
            return
            
        user_id, url, status, timestamp, run_id = row
        uid = user_id
        user = client.get_user(uid)
        if not user:
            try:
                user = await client.fetch_user(uid)
            except discord.NotFound:
                pass
                
        username_str = f" ({user.name})" if user else ""
        user_display = f"<@{uid}>{username_str}"
        
        embed = discord.Embed(title=f"Trace Info: {trace_id} (Past)", color=discord.Color.light_grey())
        embed.add_field(name="User", value=user_display, inline=False)
        embed.add_field(name="Target URL", value=url, inline=False)
        embed.add_field(name="Status", value=status, inline=True)
        try:
            dt = datetime.fromisoformat(timestamp)
            timestamp_str = f"<t:{int(dt.timestamp())}:R>"
        except Exception:
            timestamp_str = timestamp
            
        embed.add_field(name="Timestamp", value=timestamp_str, inline=True)
        embed.add_field(name="Run ID", value=str(run_id) if run_id is not None else "No workflow started", inline=True)
        
        await interaction.response.send_message(embed=embed)
        return

    context = client.pending_traces[trace_id]
    
    uid = context.get('user_id')
    user = client.get_user(uid) if uid else None
    if uid and not user:
        try:
            user = await client.fetch_user(uid)
        except discord.NotFound:
            pass
            
    username_str = f" ({user.name})" if user else ""
    user_display = f"<@{uid}>{username_str}" if uid else "Unknown"

    embed = discord.Embed(title=f"Trace Info: {trace_id}", color=discord.Color.green())
    embed.add_field(name="User", value=user_display, inline=False)
    embed.add_field(name="Target URL", value=context.get('target_url', 'Unknown'), inline=False)
    embed.add_field(name="URL Type", value=context.get('url_type', 'Unknown'), inline=True)
    embed.add_field(name="Is Silent", value=str(context.get('is_silent', False)), inline=True)
    embed.add_field(name="Free Space", value=str(context.get('free_space', False)), inline=True)
    
    start_time = context.get('start_time')
    if isinstance(start_time, datetime):
        start_time_str = f"<t:{int(start_time.timestamp())}:R>"
    else:
        start_time_str = str(start_time)
    
    embed.add_field(name="Start Time", value=start_time_str, inline=False)
    embed.add_field(name="GitHub Run ID", value=str(context.get('github_run_id', 'Not started yet')), inline=True)
    embed.add_field(name="History Run ID", value=str(context.get('history_run_id', 'Unknown')), inline=True)
    embed.add_field(name="Batch ID", value=str(context.get('batch_id', 'None')), inline=True)
    
    await interaction.response.send_message(embed=embed)

@client.tree.command(name="restart", description="Restart the bot (BOT OWNER ONLY)")
async def restart(interaction: discord.Interaction):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    if client.shutdown_requested:
        await interaction.response.send_message("The bot workflow is already shutting down", ephemeral=True)
        return

    await interaction.response.send_message("Saving state and restarting", ephemeral=True)
    
    await client.save_state()
    
    # Close connections cleanly
    await client.close()
    
    # Restart the process
    logging.info("Restarting process")
    os.execv(sys.executable, [sys.executable] + sys.argv)


@client.tree.command(name="shutdown", description="Stop the bot workflow without starting another session (BOT OWNER ONLY)")
async def shutdown(interaction: discord.Interaction):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    shutdown_file = os.getenv("WORKFLOW_SHUTDOWN_FILE")
    if not shutdown_file:
        await interaction.response.send_message(
            "This command needs the updated bot hosting workflow", ephemeral=True
        )
        return

    if client.shutdown_requested:
        await interaction.response.send_message("The bot workflow is already shutting down", ephemeral=True)
        return

    client.shutdown_requested = True
    temporary_shutdown_file = shutdown_file + ".tmp"
    try:
        await interaction.response.defer(ephemeral=True)
        await client.save_state()
        with open(temporary_shutdown_file, "w", encoding="utf-8") as marker:
            marker.write("shutdown\n")
        # Deliver the reply before the supervisor can stop the Discord connection
        await interaction.followup.send(
            "Shutting down the bot workflow, state will be backed up to R2 and no new session will start",
            ephemeral=True
        )
        # The runner owns shutdown, final state validation, backups, and session control
        # This marker stays outside the app cache so a manual start works normally
        os.replace(temporary_shutdown_file, shutdown_file)
    except Exception:
        client.shutdown_requested = False
        logging.exception("Could not request bot workflow shutdown")
        try:
            os.remove(temporary_shutdown_file)
        except FileNotFoundError:
            pass
        except OSError:
            logging.exception("Could not remove the temporary shutdown marker")
        if interaction.response.is_done():
            await interaction.followup.send(
                "Could not request shutdown, the bot is still running", ephemeral=True
            )
        else:
            await interaction.response.send_message(
                "Could not request shutdown, the bot is still running", ephemeral=True
            )

# --- Event Listeners ---

@client.event
async def on_message(message):
    # Always ignore this bot's own messages
    if message.author.id == client.user.id:
        return

    is_dm = message.guild is None
    guild_id = message.guild.id if message.guild else None

    content = message.content
    has_archive_cmd = "!archive" in content

    all_enabled = True
    if not is_dm:
        all_enabled = await is_all_messages_enabled(guild_id)

    if not all_enabled:
        if not has_archive_cmd:
            return
        content = content[content.find("!archive") + len("!archive"):]
    elif has_archive_cmd:
        content = content[content.find("!archive") + len("!archive"):]

    free_space = bool(re.search(r'(?:^|\s)(?:--large|-l)(?:\s|$)', content))

    # Handle bot messages
    if message.author.bot:
        # In DMs, ignore all bot messages
        if is_dm:
            return
        # In servers, only process if bot messages are allowed
        if not await is_bot_messages_allowed(guild_id):
            return

    if not is_dm:
        if await is_user_or_channel_excluded(message.author.id, message.channel.id, guild_id):
            return

    tasks_to_process = extract_tasks_from_text(content)
    if not tasks_to_process:
        return

    await dispatch_archive_tasks(tasks_to_process, message.author, message, guild_id, free_space)

if __name__ == "__main__":
    client.run(DISCORD_TOKEN)
