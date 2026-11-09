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
import mimetypes
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from hashlib import sha256
from urllib.parse import urlsplit
from dotenv import load_dotenv
import internetarchive as ia

# --- Configuration & Setup ---

load_dotenv()

DISCORD_TOKEN = os.getenv('ARAB_NEWS_DISCORD_TOKEN')
OWNER_ID = os.getenv('OWNER_ID')
GITHUB_TOKEN = os.getenv('GITHUB_TOKEN')
REPO_OWNER = os.getenv('GITHUB_OWNER')
REPO_NAME = os.getenv('GITHUB_REPO')
WORKFLOW_FILE = 'arab-news-archive.yml'
BOT_REQUEST_TRACE_ID = "arab-news"  # Prefix for numbered bot requests

if not DISCORD_TOKEN:
    raise RuntimeError("Missing ARAB_NEWS_DISCORD_TOKEN in environment variables")
if not OWNER_ID:
    logging.warning("Missing OWNER_ID in environment variables, restart command will be disabled if not set")
    OWNER_ID = 0
else:
    OWNER_ID = int(OWNER_ID)

if not (GITHUB_TOKEN and REPO_OWNER and REPO_NAME):
    raise RuntimeError("Missing GitHub configuration (TOKEN/OWNER/REPO)")

DB_NAME = "arab_news_archive.db"
EXCLUDED_DB_NAME = "arab_news_excluded_urls.db"
LOG_FILE = "arab_news_bot_logs.txt"
LOG_CHANNEL_ID = int(os.getenv("ARAB_NEWS_LOG_CHANNEL_ID", "").strip() or "0")
STATE_FILE = "arab_news_bot_state.json"

GITHUB_HEADERS = {
    "Authorization": f"Bearer {GITHUB_TOKEN}",
    "Accept": "application/vnd.github+json",
    "X-GitHub-Api-Version": "2022-11-28"
}

FILE_LOCK = asyncio.Lock()
HTTP_TIMEOUT = aiohttp.ClientTimeout(total=30)
MAX_CONCURRENT_JOBS = 4
MAX_BOT_CONCURRENT_JOBS = 2
MAX_QUEUED_JOBS = 4
QUEUE_COOLDOWN_SECONDS = 5
JOB_TIMEOUT_SECONDS = 30 * 60
CRAWL_JOB_TIMEOUT_SECONDS = 45 * 60
JOB_RETRY_DELAY_SECONDS = 2 * 60 * 60
SPN_CAPTURE_COUNT = 5
SPN_CAPTURE_INTERVAL_SECONDS = 60 * 60
BOT_RETRY_SCHEDULE = (
    (60 * 60, "1 hour"),
    (2 * 60 * 60, "2 hours"),
    (3 * 60 * 60, "3 hours"),
)
STANDARD_EXCLUSION_RETENTION_DAYS = 3


def is_bot_trace_id(trace_id):
    return trace_id == BOT_REQUEST_TRACE_ID or bool(re.fullmatch(
        rf"{re.escape(BOT_REQUEST_TRACE_ID)}-[0-9]+", trace_id or ""
    ))


def format_archive_complete(icon, status_text, archive_url, trace_id=None):
    message = (
        f"{icon} Archive Complete\n"
        f"Status: {status_text}\n"
        f"Archive URL: {archive_url}"
    )
    if trace_id:
        message += f"\n\n||Trace ID: `{trace_id}`||"
    return message


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
        self.queue_cooldowns = {}
        self.pending_traces = {} # trace_id -> context
        self.starting_jobs = {} # trace_id -> job reserved by the queue dispatcher
        self.dispatch_tasks = set()
        self.dispatch_task_details = {}
        self.dispatch_phases = {}
        self.cancel_lock = asyncio.Lock()
        self.cancelling_all = False
        self.cancelling_users = set()
        self.cancel_epoch = 0
        self.user_cancel_epochs = defaultdict(int)
        self.delayed_retry_jobs = {}
        self.bot_trace_counter = 0
        self.last_crawl_second = 0
        self.batch_jobs = {} # batch_id -> aggregate multi-link context
        self.state_lock = asyncio.Lock()
        self.github_poll_error = None
        self.shutdown_requested = False

    async def setup_hook(self):
        self.session = aiohttp.ClientSession(timeout=HTTP_TIMEOUT)
        await init_db()
        await init_excluded_db()
        await remove_expired_global_exclusions()
        await self.load_state()
        logging.info("Restoring bot trace counter from history")
        await self.restore_bot_trace_counter()
        logging.info("Syncing Discord commands")
        await self.tree.sync()
        if LOG_CHANNEL_ID:
            upload_logs.start()
        poll_github_runs.start()
        cleanup_expired_exclusions.start()
        self.update_bot_status.start()
        logging.info("Commands synced, DB initialized, Session active, Log upload task started, Github polling started, exclusion cleanup started")

    def next_bot_trace_id(self):
        # The dispatcher checkpoints this counter before sending the request.
        self.bot_trace_counter += 1
        return f"{BOT_REQUEST_TRACE_ID}-{self.bot_trace_counter:02d}"

    def next_crawl_timestamp(self):
        now = int(datetime.now(timezone.utc).timestamp())
        self.last_crawl_second = max(now, self.last_crawl_second + 1)
        return datetime.fromtimestamp(self.last_crawl_second, timezone.utc).strftime("%Y%m%d%H%M%S")

    def job_generation(self, user_id):
        return self.cancel_epoch, self.user_cancel_epochs[user_id]

    def queue_is_paused(self, user_id):
        return self.cancelling_all or user_id in self.cancelling_users

    async def restore_bot_trace_counter(self):
        # History also prevents reuse if a state checkpoint is missing/older.
        async with aiosqlite.connect(DB_NAME) as db:
            async with db.execute(
                "SELECT MAX(CAST(SUBSTR(trace_id, ?) AS INTEGER)) FROM history WHERE trace_id GLOB ?",
                (len(BOT_REQUEST_TRACE_ID) + 2, f"{BOT_REQUEST_TRACE_ID}-[0-9]*")
            ) as cursor:
                row = await cursor.fetchone()
        self.bot_trace_counter = max(self.bot_trace_counter, (row[0] if row else None) or 0)

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

            query = 'uploader:"ArabNewsArchive@markstonehub.org"'
            
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
            
            activity = discord.Activity(type=discord.ActivityType.watching, name=f"Arab News Archive · {count} items · {size_str}")
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
            "bot_trace_counter": self.bot_trace_counter,
            "last_crawl_second": self.last_crawl_second,
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
                "bot_retry_count": context.get("bot_retry_count", 0),
                "spn_series": context.get("spn_series"),
                "ignore_existing_item": context.get("ignore_existing_item", False),
                "cancel_requested": context.get("cancel_requested", False),
                "cancel_acknowledged": context.get("cancel_acknowledged", False),
                "github_run_id": context.get("github_run_id"),
                "start_time": context["start_time"].isoformat() if isinstance(context["start_time"], datetime) else context["start_time"],
                "status_msg_data": {
                    "channel_id": context["status_msg"].channel.id,
                    "message_id": context["status_msg"].id
                } if context["status_msg"] else None
            }

        # A process can stop during preflight/dispatch. Save those reservations
        # as queued work too, instead of restoring a count with no matching job.
        jobs_to_save = {uid: list(jobs) for uid, jobs in self.queued_jobs.items()}
        for job in reversed(list(self.starting_jobs.values())):
            jobs_to_save.setdefault(job[5], []).insert(0, job)

        # Serialize queued_jobs
        for user_id, jobs in jobs_to_save.items():
            serialized_jobs = []
            for job in jobs:
                # job: (target_url, url_type, is_silent, original_message,
                #       guild_id, user_id, free_space, batch_id, is_bot_request,
                #       reuse_status_message, ignore_existing_item, bot_retry_count, spn_series)
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
                    "reuse_status_message": bool(job[9]) if len(job) > 9 else False,
                    "ignore_existing_item": bool(job[10]) if len(job) > 10 else False,
                    "bot_retry_count": job[11] if len(job) > 11 else 0,
                    "spn_series": job[12] if len(job) > 12 else None,
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

    def restore_message_reference(self, data):
        """Rebuild a usable message reference without fetching Discord history."""
        if not data:
            return None
        try:
            channel_id, message_id = int(data["channel_id"]), int(data["message_id"])
            if channel_id <= 0 or message_id <= 0:
                raise ValueError("Discord IDs must be positive")
            return self.get_partial_messageable(channel_id).get_partial_message(message_id)
        except (KeyError, TypeError, ValueError) as error:
            logging.warning("Could not restore a saved Discord message reference: %s", error)
            return None

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
            self.bot_trace_counter = max(self.bot_trace_counter, int(state.get("bot_trace_counter", 0)))
            self.last_crawl_second = max(self.last_crawl_second, int(state.get("last_crawl_second", 0)))
            logging.info(
                "Restoring %s batches, %s pending traces, and %s queued jobs using saved Discord message IDs",
                len(state.get("batch_jobs", {})), len(state.get("pending_traces", {})),
                sum(len(jobs) for jobs in state.get("queued_jobs", {}).values())
            )

            # Rebuild counters from actual tracked requests after restoring them.
            # Old snapshots counted tasks waiting on the shared bot lock even
            # though those tasks could not be resumed after a restart.
            self.active_jobs = defaultdict(int)

            # Restore batch_jobs
            self.batch_jobs = {}
            for batch_id, bdata in state.get("batch_jobs", {}).items():
                status_msg = self.restore_message_reference(bdata.get("status_msg_data"))
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
                status_msg = self.restore_message_reference(data.get("status_msg_data"))

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
                    "is_bot_request": data.get("is_bot_request", is_bot_trace_id(trace_id)),
                    "bot_retry_count": data.get("bot_retry_count", 0),
                    "spn_series": data.get("spn_series"),
                    "ignore_existing_item": data.get("ignore_existing_item", False),
                    "cancel_requested": data.get("cancel_requested", False),
                    "cancel_acknowledged": data.get("cancel_acknowledged", False),
                    "github_run_id": data.get("github_run_id"),
                    "start_time": datetime.fromisoformat(data["start_time"]) if data.get("start_time") else datetime.now(timezone.utc)
                }

            # Restore queued_jobs
            for user_id_str, jobs_data in state.get("queued_jobs", {}).items():
                user_id = int(user_id_str)
                restored_jobs = []
                for job_data in jobs_data:
                    msg = self.restore_message_reference(job_data.get("message_data"))
                    
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
                        job_data.get("reuse_status_message", False),
                        job_data.get("ignore_existing_item", False),
                        job_data.get("bot_retry_count", 0),
                        job_data.get("spn_series"),
                    ))
                self.queued_jobs[user_id] = restored_jobs

            for context in self.pending_traces.values():
                self.active_jobs[context["user_id"]] += 1
            for trace_id in self.pending_traces:
                if is_bot_trace_id(trace_id) and trace_id != BOT_REQUEST_TRACE_ID:
                    self.bot_trace_counter = max(self.bot_trace_counter, int(trace_id.rsplit("-", 1)[1]))
            saved_counts = {int(k): v for k, v in state.get("active_jobs", {}).items() if v}
            actual_counts = {uid: count for uid, count in self.active_jobs.items() if count}
            if saved_counts != actual_counts:
                logging.warning("Repaired stale active job counts: saved=%s restored=%s", saved_counts, actual_counts)
            logging.info(f"State loaded: {len(self.pending_traces)} pending traces, {sum(map(len, self.queued_jobs.values()))} queued jobs")
            # Keep the last checkpoint until the next atomic save succeeds.

        except Exception as e:
            logging.error(f"Failed to load state: {e}")

    async def close(self):
        self.shutdown_requested = True
        for timer in self.queue_cooldowns.values():
            timer.cancel()
        self.queue_cooldowns.clear()
        poll_github_runs.cancel()
        cleanup_expired_exclusions.cancel()
        upload_logs.cancel()
        self.update_bot_status.cancel()
        tasks_to_stop = list(self.dispatch_tasks)
        for task in tasks_to_stop:
            task.cancel()
        if tasks_to_stop:
            await asyncio.gather(*tasks_to_stop, return_exceptions=True)
        if self.session:
            await self.session.close()
        await super().close()

    async def fetch_artifact_logs(self, run_id, trace_id, *, include_archive=True, include_crawl=False):
        artifacts_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{run_id}/artifacts"
        expected_names = set()
        if include_archive:
            expected_names.add(f"arab-news-archive-logs-{trace_id}.txt")
        if include_crawl:
            expected_names.add(f"arab-news-archive-crawl-logs-{trace_id}.txt")
        downloaded = {}
        try:
            for _ in range(3):
                async with self.session.get(artifacts_url, headers=GITHUB_HEADERS) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        for artifact in data.get("artifacts", []):
                            expected_name = artifact["name"]
                            if expected_name not in expected_names or expected_name in downloaded:
                                continue
                            async with self.session.get(artifact["archive_download_url"], headers=GITHUB_HEADERS) as d_resp:
                                if d_resp.status != 200:
                                    continue
                                log_data = await d_resp.read()
                                if zipfile.is_zipfile(io.BytesIO(log_data)):
                                    with zipfile.ZipFile(io.BytesIO(log_data)) as archive:
                                        for name in archive.namelist():
                                            if name.rsplit('/', 1)[-1] == expected_name:
                                                downloaded[expected_name] = archive.read(name)
                                                break
                                else:
                                    downloaded[expected_name] = log_data
                        if downloaded.keys() == expected_names:
                            return b'\n'.join(downloaded.values())
                await asyncio.sleep(2)
        except Exception as e:
            logging.error(f"Failed to fetch artifact for run {run_id}: {e}")
        # Read job logs when the standalone log artifact is unavailable.
        try:
            logs_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{run_id}/logs"
            async with self.session.get(logs_url, headers=GITHUB_HEADERS) as response:
                if response.status == 200:
                    raw = await response.read()
                    if zipfile.is_zipfile(io.BytesIO(raw)):
                        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
                            raw = b'\n'.join(archive.read(name) for name in archive.namelist() if name.endswith('.txt'))
                    return b'\n'.join([raw, *downloaded.values()])
        except Exception as exc:
            logging.warning("Could not fetch workflow log fallback for run %s: %s", run_id, exc)
        return b'\n'.join(downloaded.values()) or None

    async def read_completion_log(self, context, trace_id):
        run_id = context.get("github_run_id")
        if not run_id:
            return ""
        series = context.get("spn_series")
        save_page_now, crawl_website = website_archive_steps(series)
        log_bytes = await self.fetch_artifact_logs(
            run_id, trace_id, include_archive=not series or save_page_now, include_crawl=crawl_website,
        )
        if not log_bytes:
            return ""
        log_text = log_bytes.decode("utf-8", errors="replace")
        log_text = re.sub(r'[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\.[a-zA-Z0-9-.]+', '***', log_text)
        return '\n'.join(line.split('\r')[-1] for line in log_text.split('\n'))

    async def handle_completion(self, context, exit_code, trace_id, log_text, result, *, followup=None):
        if context.get("cancel_requested"):
            return
        user_id = context["user_id"]
        original_url = context["target_url"]
        url_type = context["url_type"]
        status_msg = context["status_msg"]
        is_silent = context["is_silent"]
        batch_id = context.get("batch_id")

        actual_run_id = context.get("github_run_id")
        series = context.get("spn_series")
        save_page_now, crawl_website = website_archive_steps(series)
        saved, existing, skipped = result["saved"], result["existing"], result["skipped"]
        wayback_url = result.get("wayback_url") if save_page_now else None
        crawl_id = result.get("warc_identifier") if crawl_website else None
        crawl_url = f"https://archive.org/details/{crawl_id}" if crawl_id else None
        saved_to_account = result.get("my_web_archive") is True
        if wayback_url:
            number = series["attempt"]
            capture = {"url": wayback_url, "my_web_archive": saved_to_account, "archive_number": number}
            previous = next((entry for entry in series["captures"]
                             if entry.get("archive_number") == number or entry["url"] == wayback_url), None)
            if previous is None:
                series["captures"].append(capture)
            elif saved_to_account and not previous["my_web_archive"]:
                previous.update(capture)
        if crawl_url and crawl_url not in series["crawls"]:
            series["crawls"].append(crawl_url)

        log_channel = self.get_channel(LOG_CHANNEL_ID) if log_text and LOG_CHANNEL_ID else None
        if log_channel:
            status = "completed" if exit_code == 0 else "failed"
            try:
                await log_channel.send(
                    content=f"Log for trace `{trace_id}`\n(Status: {status}):",
                    file=discord.File(fp=io.BytesIO(log_text.encode("utf-8")), filename=f"arab_news_archive_log_{trace_id}.txt"),
                )
            except Exception as e:
                logging.error(f"Failed to upload artifact to log channel: {e}")

        if context.get("cancel_requested"):
            return
        archive_succeeded = bool(wayback_url or crawl_url) if series else exit_code == 0
        is_already_archived = archive_succeeded and not saved and skipped > 0
        history_status = "Already archived" if is_already_archived else ("Archived" if archive_succeeded else "Failed")
        bot_retry_wait = followup["wait"] if followup and followup["context"].get("bot_retry_count") else None
        if bot_retry_wait:
            history_status = "Retrying later"
        if actual_run_id:
            async with aiosqlite.connect(DB_NAME) as db:
                await db.execute("UPDATE history SET run_id = ?, status = ? WHERE run_id = ?", (actual_run_id, history_status, context["history_run_id"]))
                await db.commit()
        else:
            await update_history_status(context["history_run_id"], history_status)

        if series:
            await self.report_spn_capture(
                context, trace_id, wayback_url, saved_to_account, crawl_url=crawl_url, followup=followup,
            )
            return

        item_ids = list(dict.fromkeys(saved + existing))
        archive_urls = [f"https://archive.org/details/{identifier}" for identifier in item_ids]
        if bot_retry_wait:
            if context.get("cancel_requested"):
                return
            batch = self.batch_jobs.get(batch_id)
            if batch is not None:
                batch["archive_urls"].extend(archive_urls)
            if not is_silent and status_msg:
                try:
                    await status_msg.edit(
                        content=f"⚠️ Archive failed and will be retried in {bot_retry_wait}\n\n||Trace ID: `{trace_id}`||"
                    )
                except Exception:
                    logging.warning("Could not show retry status for trace %s", trace_id)
            return

        log_lower = log_text.casefold()
        no_space = "no space left on device" in log_lower
        if (not archive_succeeded and no_space and not context.get("free_space", False)
                and not context.get("is_bot_request", False)):
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
                True, # reuse the existing status message
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
                        content=f"⏳ Storage limit reached for {url_type}, retrying with large file support\n\n||Trace ID: `{trace_id}`||"
                    )
                except Exception:
                    pass
            
            return

        if archive_succeeded:
            archive_key = archive_identifier(original_url)
            try:
                await make_global_exclusion_permanent(archive_key)
            except Exception:
                logging.exception("Failed to keep the successful exclusion for %s", archive_key)

        if batch_id:
            await self.update_batch_progress(batch_id, archive_succeeded, archive_urls)
            return

        if not is_silent and status_msg:
            icon = "❌"
            status_text = f"Archive failed (Exit Code: {exit_code})"
            display_url = "Unavailable"
            if is_already_archived:
                icon = "➖"
                status_text = f"{url_type} is already archived"
            elif archive_succeeded:
                icon = "✅"
                status_text = "Archive succeeded"
            elif no_space:
                status_text = "This download is too large"
            elif "all configured download cookie accounts were rejected or rate-limited" in log_lower:
                status_text = "The configured cookie accounts were rejected or rate-limited"
            elif "no usable download cookie secrets are configured" in log_lower:
                status_text = "No usable download cookie secrets are configured"
            elif "requested format is not available" in log_lower:
                status_text = "Unable to download the requested media format"
            elif "no downloadable media found" in log_lower or "unsupported url" in log_lower:
                status_text = "No downloadable media found for this link"
            elif "internet archive upload failed (http 429)" in log_lower or "please reduce your request rate" in log_lower:
                status_text = "The Internet Archive is rate-limiting uploads"
            elif "internet archive upload failed" in log_lower:
                status_text = "Upload to the Internet Archive failed"

            if not archive_succeeded and saved:
                status_text += f", {len(saved)} item(s) archived before the failure"

            edit_kwargs = {"embed": None}
            if len(archive_urls) == 1:
                display_url = archive_urls[0]
            elif len(archive_urls) > 1:
                display_url = f"Multiple items archived ({len(archive_urls)} URLs)"
                edit_kwargs["attachments"] = [
                    discord.File(io.BytesIO("\n".join(archive_urls).encode("utf-8")), filename=f"arab_news_urls_{trace_id}.txt")
                ]
            edit_kwargs["content"] = format_archive_complete(icon, status_text, display_url, trace_id)
            try:
                await status_msg.edit(**edit_kwargs)
            except Exception as e:
                logging.error(f"Failed to edit status message: {e}")

    async def report_spn_capture(
        self, context, trace_id, wayback_url=None, saved_to_account=False, *, crawl_url=None, followup=None,
    ):
        if context.get("cancel_requested"):
            return
        series = context["spn_series"]
        wayback_urls = [capture["url"] for capture in series["captures"]]
        crawl_urls = series.get("crawls", [])
        urls = wayback_urls + crawl_urls
        if not followup:
            if urls:
                try:
                    await make_global_exclusion_permanent(
                        archive_identifier(context["target_url"], save_page_now=True),
                        category=f"spn-series-{series['id']}",
                    )
                except Exception:
                    logging.exception("Could not keep the finished Wayback series in the exclusion list")
            if context.get("batch_id"):
                await self.update_batch_progress(context["batch_id"], bool(urls), urls)
                return

        status_msg = context.get("status_msg")
        if context["is_silent"] or not status_msg:
            return

        if followup:
            save_page_now, crawl_website = website_archive_steps(series)
            status_lines = []
            if save_page_now:
                outcome = "✅ Saved" if wayback_url else "⚠️ Failed"
                status_lines.append(f"{outcome} Wayback capture {series['attempt']}/{SPN_CAPTURE_COUNT}")
                if wayback_url and not saved_to_account:
                    status_lines.append("My Web Archive save unconfirmed")
            if crawl_website:
                outcome = "✅ Uploaded" if crawl_url else "⚠️ Failed"
                status_lines.append(f"{outcome} WARC crawl {series.get('crawl_attempt', 1)}/{SPN_CAPTURE_COUNT}")
            next_context = followup["context"]
            next_step = describe_website_archive(next_context["spn_series"])
            wait = followup["wait"]
            retry_number = next_context["bot_retry_count"]
            if retry_number:
                status_lines.append(f"⏳ Retry {retry_number}/{len(BOT_RETRY_SCHEDULE)} in about {wait} · {next_step}")
            else:
                status_lines.append(f"⏳ Next archive in about {wait} · {next_step}")
            text = "\n".join(status_lines)
            display_urls = [url for url in (wayback_url, crawl_url) if url]
        else:
            crawl_complete = "crawls" not in series or len(crawl_urls) == SPN_CAPTURE_COUNT
            icon = "✅" if len(wayback_urls) == SPN_CAPTURE_COUNT and crawl_complete else "⚠️"
            text = f"{icon} Website archive finished\nWayback captures saved {len(wayback_urls)}/{SPN_CAPTURE_COUNT}"
            if "crawls" in series:
                text += f"\nWARC crawls uploaded {len(crawl_urls)}/{SPN_CAPTURE_COUNT}"
            unconfirmed = sum(not capture["my_web_archive"] for capture in series["captures"])
            if unconfirmed:
                text += f"\nMy Web Archive saves unconfirmed for {unconfirmed} capture(s)"
            display_urls = urls

        edit_kwargs = {"embed": None}
        if display_urls and sum(len(url) + 3 for url in display_urls) < 1600:
            text += "\n" + "\n".join(f"<{url}>" for url in display_urls)
        elif display_urls:
            edit_kwargs["attachments"] = [
                discord.File(io.BytesIO("\n".join(display_urls).encode("utf-8")), filename=f"website_archives_{trace_id}.txt")
            ]
        edit_kwargs["content"] = text + f"\n\n||Trace ID: `{trace_id}`||"
        try:
            await status_msg.edit(**edit_kwargs)
        except Exception:
            logging.warning("Could not show Wayback capture result for trace %s", trace_id)

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
                            filename=f"arab_news_archive_links_{batch_id}.txt"
                        )

                    final_batch_msg = (
                        "✅ Archive Batch Complete\n"
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

def prepare_bot_retry(context):
    count = context.get("bot_retry_count", 0)
    if (not context.get("is_bot_request") or count >= len(BOT_RETRY_SCHEDULE)
            or context.get("cancel_requested")
            or client.queue_is_paused(context["user_id"])):
        return None
    delay_seconds, wait = BOT_RETRY_SCHEDULE[count]
    return {
        "context": {**context, "bot_retry_count": count + 1},
        "delay_seconds": delay_seconds,
        "wait": wait,
    }


def website_archive_steps(series):
    if not series:
        return False, False
    retry_steps = series.get("retry_steps")
    if retry_steps:
        return retry_steps["save_page_now"], retry_steps["crawl_website"]
    if series.get("crawl_attempt"):
        return False, True
    return True, "crawls" in series and series["attempt"] == 1


def describe_website_archive(series, retry_number=0):
    save_page_now, crawl_website = website_archive_steps(series)
    labels = []
    if save_page_now:
        labels.append(f"Wayback capture {series['attempt']}/{SPN_CAPTURE_COUNT}")
    if crawl_website:
        labels.append(f"WARC crawl {series.get('crawl_attempt', 1)}/{SPN_CAPTURE_COUNT}")
    description = " and ".join(labels)
    if retry_number:
        description += f" · Retry {retry_number}/{len(BOT_RETRY_SCHEDULE)}"
    return description


def prepare_website_followup(context):
    series = context["spn_series"]
    if context.get("cancel_requested") or client.queue_is_paused(context["user_id"]):
        return None
    next_series = dict(series)
    next_series.pop("retry_steps", None)
    next_series.pop("crawl_timestamp", None)
    # The stored archive numbers only advance after this archive and its retries finish.
    if series.get("crawl_attempt"):
        if series["crawl_attempt"] >= SPN_CAPTURE_COUNT:
            return None
        next_series["crawl_attempt"] += 1
    elif series["attempt"] < SPN_CAPTURE_COUNT:
        next_series["attempt"] += 1
    elif "crawls" in series:
        next_series["crawl_attempt"] = 2
    else:
        return None
    return {
        "context": {**context, "spn_series": next_series, "bot_retry_count": 0},
        "delay_seconds": SPN_CAPTURE_INTERVAL_SECONDS,
        "wait": "1 hour",
    }


def prepare_website_continuation(context, result=None):
    series = context["spn_series"]
    save_page_now, crawl_website = website_archive_steps(series)
    result = result or {}
    failed_steps = {
        "save_page_now": save_page_now and not (result.get("wayback_url") and result.get("my_web_archive")),
        "crawl_website": crawl_website and not result.get("warc_identifier"),
    }
    if any(failed_steps.values()):
        retry = prepare_bot_retry(context)
        if retry:
            retry["context"]["spn_series"] = {**series, "retry_steps": failed_steps}
            return retry
    return prepare_website_followup(context)


def schedule_delayed_retry(context, delay_seconds):
    """Register immediately so /cancelalljobs also catches timers not yet started."""
    user_id = context["user_id"]
    retry_id = uuid.uuid4().hex
    generation = client.job_generation(user_id)
    record = {"context": context, "task": None}
    if not context.get("cancel_requested"):
        client.delayed_retry_jobs[retry_id] = record

    async def wait_and_resume():
        record["task"] = asyncio.current_task()
        try:
            if retry_id not in client.delayed_retry_jobs or context.get("cancel_requested"):
                return
            await asyncio.sleep(delay_seconds)
            if (retry_id not in client.delayed_retry_jobs or context.get("cancel_requested")
                    or generation != client.job_generation(user_id)):
                return
            await enqueue_delayed_retry(context)
        finally:
            client.delayed_retry_jobs.pop(retry_id, None)
    return wait_and_resume()


def schedule_timeout_retry(context):
    return schedule_delayed_retry({**context, "ignore_existing_item": True}, JOB_RETRY_DELAY_SECONDS)


async def enqueue_delayed_retry(context):
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
        True, # reuse the existing status message
        context.get("ignore_existing_item", False),
        context.get("bot_retry_count", 0),
        context.get("spn_series"),
    )

    client.queued_jobs[user_id].append(queued_job)
    await client.save_state()
    await process_all_queues()

# --- GitHub Polling Task ---

def workflow_run_matches(trace_id, context, run):
    bound_run_id = context.get("github_run_id")
    if bound_run_id:
        return run.get("id") == bound_run_id
    run_name = run.get("display_title") or run.get("name", "")
    match = re.search(r'\[trace-([a-zA-Z0-9-]+)\]', run_name)
    if not match or match.group(1) != trace_id:
        return False
    if context.get("is_bot_request"):
        # Ignore older runs with a matching trace ID.
        try:
            created_at = datetime.fromisoformat(run["created_at"].replace("Z", "+00:00"))
            if created_at.timestamp() + 5 < context["start_time"].timestamp():
                return False
        except (KeyError, TypeError, ValueError, AttributeError):
            return False
    return True


def archive_request_expired(context):
    started_at = context.get("start_time")
    if not isinstance(started_at, datetime):
        return False
    _, crawl_website = website_archive_steps(context.get("spn_series"))
    timeout = CRAWL_JOB_TIMEOUT_SECONDS if crawl_website else JOB_TIMEOUT_SECONDS
    return datetime.now(timezone.utc).timestamp() - started_at.timestamp() > timeout


def release_archive_request(trace_id, context):
    if client.pending_traces.get(trace_id) is not context:
        return
    del client.pending_traces[trace_id]
    release_queue_slot(context["user_id"])


def release_queue_slot(user_id):
    client.active_jobs[user_id] = max(0, client.active_jobs[user_id] - 1)
    timer = client.queue_cooldowns.pop(user_id, None)
    if timer is not None:
        timer.cancel()
    if client.shutdown_requested:
        return

    def resume_queue():
        client.queue_cooldowns.pop(user_id, None)
        if not client.shutdown_requested:
            asyncio.create_task(check_and_process_queue(user_id))

    loop = asyncio.get_running_loop()
    client.queue_cooldowns[user_id] = loop.call_later(QUEUE_COOLDOWN_SECONDS, resume_queue)


async def finish_archive_request(trace_id, context, run):
    conclusion = run.get("conclusion")
    exit_code = 0 if conclusion == "success" else 1
    try:
        log_text = await asyncio.wait_for(client.read_completion_log(context, trace_id), timeout=180)
    except Exception:
        logging.exception("Could not read archive results for trace %s", trace_id)
        log_text = ""
    result = parse_archive_result(log_text)
    followup = None
    if conclusion != "cancelled":
        if context.get("spn_series"):
            followup = prepare_website_continuation(context, result)
        elif exit_code:
            followup = prepare_bot_retry(context)
    try:
        await asyncio.wait_for(
            client.handle_completion(context, exit_code, trace_id, log_text, result, followup=followup),
            timeout=120,
        )
    except Exception:
        logging.exception("Completion handling failed for trace %s, releasing its slot", trace_id)
    finally:
        # DB, artifact, or Discord reporting errors cannot pin a finished job.
        if client.pending_traces.get(trace_id) is context:
            release_archive_request(trace_id, context)
            if followup and not context.get("cancel_requested"):
                asyncio.create_task(schedule_delayed_retry(followup["context"], followup["delay_seconds"]))
        await client.save_state()
        await process_all_queues()


async def expire_archive_request(trace_id, context):
    if context.get("cancel_requested"):
        return
    run_id = context.get("github_run_id")
    if run_id:
        cancel_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{run_id}/cancel"
        try:
            async with client.session.post(cancel_url, headers=GITHUB_HEADERS) as resp:
                if resp.status not in (202, 409):
                    logging.warning("Could not cancel timed out run %s: HTTP %s", run_id, resp.status)
        except Exception:
            logging.exception("Error cancelling timed out run %s", run_id)

    if context.get("cancel_requested") or client.pending_traces.get(trace_id) is not context:
        return
    if context.get("spn_series"):
        # The other job in the initial pair may have published its result already.
        logging.warning("Timed out website archive %s", trace_id)
        await finish_archive_request(trace_id, context, {"conclusion": "timed_out"})
        return
    # Apply the deadline even to queued, waiting, missing, and unobservable runs.
    is_bot_request = context.get("is_bot_request", False)
    retry = prepare_bot_retry(context)
    retry_wait = retry["wait"] if retry else (None if is_bot_request else "2 hours")
    release_archive_request(trace_id, context)
    if retry:
        asyncio.create_task(schedule_delayed_retry(retry["context"], retry["delay_seconds"]))
    elif not is_bot_request:
        asyncio.create_task(schedule_timeout_retry(context))
    await client.save_state()
    await process_all_queues()
    logging.warning("Timed out trace %s (last GitHub status: %s)%s",
                    trace_id, context.get("github_status", "not found"),
                    f", retry in {retry_wait}" if retry_wait else "")
    try:
        await update_history_status(context["history_run_id"], "Retrying later" if retry_wait else "Failed")
    except Exception:
        logging.exception("Could not update timed out history for trace %s", trace_id)
    if not retry_wait and context.get("batch_id"):
        await client.update_batch_progress(context["batch_id"], is_success=False)
    if not context["is_silent"] and context.get("status_msg"):
        message = "⚠️ This archive job has taken longer than 30 minutes"
        if retry_wait:
            message += f" and will be retried in about {retry_wait}"
        try:
            await asyncio.wait_for(context["status_msg"].edit(
                content=f"{message}\n\n||Trace ID: `{trace_id}`||"
            ), timeout=30)
        except Exception:
            logging.warning("Could not show timeout status for trace %s", trace_id)


@tasks.loop(seconds=15)
async def poll_github_runs():
    if not client.pending_traces:
        await process_all_queues()
        return

    runs_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/workflows/{WORKFLOW_FILE}/runs"
    runs = []
    try:
        # Search older pages for requests that have not yet been bound to a run.
        # Already-bound requests also have a direct run-ID lookup below.
        for page in range(1, 11):
            async with client.session.get(runs_url, headers=GITHUB_HEADERS,
                                          params={"per_page": 100, "page": page}) as resp:
                if resp.status != 200:
                    raise RuntimeError(f"Workflow listing returned GitHub HTTP {resp.status}")
                data = await resp.json()
            page_runs = data.get("workflow_runs", [])
            runs.extend(page_runs)
            unresolved = any(
                not context.get("github_run_id")
                and not any(workflow_run_matches(trace_id, context, run) for run in runs)
                for trace_id, context in list(client.pending_traces.items())
            )
            if not unresolved or len(page_runs) < 100:
                break
        client.github_poll_error = None
    except Exception as exc:
        client.github_poll_error = str(exc) or type(exc).__name__
        logging.warning("Error listing GitHub runs: %s", client.github_poll_error)

    for trace_id, context in list(client.pending_traces.items()):
        try:
            if client.pending_traces.get(trace_id) is not context:
                continue
            run = next((run for run in runs if workflow_run_matches(trace_id, context, run)), None)
            if run is None and context.get("github_run_id"):
                run_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{context['github_run_id']}"
                try:
                    async with client.session.get(run_url, headers=GITHUB_HEADERS) as resp:
                        if resp.status == 200:
                            run = await resp.json()
                        else:
                            client.github_poll_error = f"Run lookup returned GitHub HTTP {resp.status}"
                            logging.warning("Cannot read run for trace %s: HTTP %s", trace_id, resp.status)
                except Exception as exc:
                    client.github_poll_error = str(exc) or type(exc).__name__
                    logging.warning("Cannot read run for trace %s: %s", trace_id, exc)

            if client.pending_traces.get(trace_id) is not context:
                continue
            if context.get("cancel_requested"):
                if run:
                    context["github_run_id"] = run.get("id")
                    context["github_status"] = run.get("status")
                if run and run.get("status") == "completed":
                    await finish_cancelled_request(trace_id, context, run)
                elif run:
                    await request_workflow_cancellation(context)
                elif archive_request_expired(context):
                    logging.warning("No workflow found for cancelled trace %s, releasing local tracking", trace_id)
                    await finish_cancelled_request(trace_id, context)
                continue
            if run is not None:
                context["github_run_id"] = run.get("id")
                context["github_status"] = run.get("status")
                if run.get("status") == "completed":
                    await finish_archive_request(trace_id, context, run)
                    continue

            # The local clock decides the deadline even when GitHub is unavailable.
            if archive_request_expired(context):
                await expire_archive_request(trace_id, context)
            elif run and run.get("status") == "in_progress" and not context.get("is_processing"):
                context["is_processing"] = True
                if not context["is_silent"] and context.get("status_msg"):
                    description = f"This {context['url_type'].lower()} is being preserved"
                    if context.get("spn_series"):
                        website = describe_website_archive(context["spn_series"], context.get("bot_retry_count", 0))
                        description = f"In progress · {website}"
                    try:
                        await asyncio.wait_for(context["status_msg"].edit(
                            content=f"⏳ {description}\n\n||Trace ID: `{trace_id}`||"
                        ), timeout=30)
                    except Exception:
                        pass
        except Exception:
            logging.exception("Error processing GitHub trace %s", trace_id)

    await client.save_state()
    await process_all_queues()

@poll_github_runs.before_loop
async def before_poll_github_runs():
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
    filename = f"arab-news-{now.year:04d}-{now.month:02d}-{now.day:02d} {now.hour:02d}-{now.minute:02d}-{now.second:02d} logs.txt"
    
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
        await channel.send(content="#hourly", file=discord.File(filename))
        
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
        await db.execute("BEGIN IMMEDIATE")
        await db.execute("""
            CREATE TABLE IF NOT EXISTS exclusions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                guild_id INTEGER,
                type TEXT NOT NULL,
                value TEXT NOT NULL,
                added_by TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                reason TEXT,
                expires_at INTEGER
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
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                reason TEXT,
                expires_at INTEGER
            )
        """)

        for table in ("exclusions", "global_user_exclusions"):
            async with db.execute(f"PRAGMA table_info({table})") as cursor:
                columns = {row[1] for row in await cursor.fetchall()}
            if "reason" not in columns:
                await db.execute(f"ALTER TABLE {table} ADD COLUMN reason TEXT")
            if "expires_at" not in columns:
                await db.execute(f"ALTER TABLE {table} ADD COLUMN expires_at INTEGER")

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

        # Requests using automated trace IDs are known bot or
        # webhook jobs and can be excluded without an API lookup
        await db.execute(
            """
            INSERT OR REPLACE INTO leaderboard_accounts
                (user_id, account_type, checked_at)
            SELECT DISTINCT user_id, 'bot', CURRENT_TIMESTAMP
            FROM history
            WHERE (trace_id = ? OR trace_id GLOB ?)
              AND user_id IS NOT NULL
            """,
            (BOT_REQUEST_TRACE_ID, f"{BOT_REQUEST_TRACE_ID}-[0-9]*")
        )
        
        await db.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_exclusions ON exclusions(guild_id, type, value);")
        await db.execute("CREATE INDEX IF NOT EXISTS ix_history_user ON history(user_id, id DESC);")
        await db.execute("CREATE INDEX IF NOT EXISTS ix_history_trace ON history(trace_id, id DESC);")
        await db.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_history_run ON history(run_id);")
        await db.execute("CREATE INDEX IF NOT EXISTS ix_lifetime_jobs_user ON lifetime_jobs(user_id);")
        
        await db.commit()

async def add_exclusion(guild_id, e_type, value, added_by, *, reason=None, expires_at=None):
    async with aiosqlite.connect(DB_NAME) as db:
        now = datetime.now(timezone.utc)
        cursor = await db.execute(
            """
            INSERT INTO exclusions (guild_id, type, value, added_by, timestamp, reason, expires_at)
            VALUES (?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(guild_id, type, value) DO UPDATE SET
                added_by = excluded.added_by,
                timestamp = excluded.timestamp,
                reason = excluded.reason,
                expires_at = excluded.expires_at
            WHERE exclusions.expires_at <= ?
            """,
            (guild_id, e_type, str(value), str(added_by), now.isoformat(), reason, expires_at, int(now.timestamp())),
        )
        await db.commit()
        return cursor.rowcount > 0

async def remove_exclusion(guild_id, e_type, value):
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute("DELETE FROM exclusions WHERE guild_id = ? AND type = ? AND value = ?", (guild_id, e_type, str(value)))
        await db.commit()
        return cursor.rowcount > 0

async def get_user_or_channel_exclusion(user_id, channel_id, guild_id):
    async with aiosqlite.connect(DB_NAME) as db:
        query = """
            SELECT type, reason, expires_at FROM exclusions
            WHERE guild_id = ?
            AND (expires_at IS NULL OR expires_at > ?)
            AND (
                (type='user' AND value=?)
                OR (type='channel' AND value=?)
            )
            ORDER BY CASE type WHEN 'user' THEN 0 ELSE 1 END
            LIMIT 1
        """
        now = int(datetime.now(timezone.utc).timestamp())
        async with db.execute(query, (guild_id, now, str(user_id), str(channel_id))) as cursor:
            return await cursor.fetchone()

async def is_url_type_excluded(guild_id, url_type):
    async with aiosqlite.connect(DB_NAME) as db:
        query = "SELECT 1 FROM exclusions WHERE guild_id = ? AND type='url_type' AND value = ? LIMIT 1"
        async with db.execute(query, (guild_id, str(url_type))) as cursor:
            return await cursor.fetchone() is not None

async def add_global_user_exclusion(user_id, added_by, *, reason=None, expires_at=None):
    async with aiosqlite.connect(DB_NAME) as db:
        now = datetime.now(timezone.utc)
        cursor = await db.execute(
            """
            INSERT INTO global_user_exclusions (user_id, added_by, timestamp, reason, expires_at)
            VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(user_id) DO UPDATE SET
                added_by = excluded.added_by,
                timestamp = excluded.timestamp,
                reason = excluded.reason,
                expires_at = excluded.expires_at
            WHERE global_user_exclusions.expires_at <= ?
            """,
            (user_id, str(added_by), now.isoformat(), reason, expires_at, int(now.timestamp())),
        )
        await db.commit()
        return cursor.rowcount > 0

async def remove_global_user_exclusion(user_id):
    async with aiosqlite.connect(DB_NAME) as db:
        cursor = await db.execute(
            "DELETE FROM global_user_exclusions WHERE user_id = ?",
            (user_id,)
        )
        await db.commit()
        return cursor.rowcount > 0

async def get_global_user_exclusion(user_id):
    async with aiosqlite.connect(DB_NAME) as db:
        now = int(datetime.now(timezone.utc).timestamp())
        async with db.execute(
            "SELECT reason, expires_at FROM global_user_exclusions WHERE user_id = ? AND (expires_at IS NULL OR expires_at > ?)",
            (user_id, now)
        ) as cursor:
            return await cursor.fetchone()

async def set_allow_bot_messages(guild_id, added_by):
    """Enable processing of bot messages with links in a server"""
    async with aiosqlite.connect(DB_NAME) as db:
        utc_now = datetime.now(timezone.utc).isoformat()
        cursor = await db.execute(
            """
            INSERT INTO exclusions (guild_id, type, value, added_by, timestamp)
            SELECT ?, 'allow_bot_messages', 'enabled', ?, ?
            WHERE NOT EXISTS (
                SELECT 1 FROM exclusions WHERE guild_id = ? AND type = 'allow_bot_messages'
            )
            """,
            (guild_id, str(added_by), utc_now, guild_id),
        )
        await db.commit()
        return cursor.rowcount > 0

async def unset_allow_bot_messages(guild_id):
    """Disable processing of bot messages with links in a server"""
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

        if is_bot_trace_id(trace_id):
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

LINK_IN_TEXT = re.compile(
    r'\[(?:\\[^\r\n]|[^\[\]\\\r\n]|\[[^\[\]\r\n]*\])*\]\([ \t]*(?=<?https?://)'
    r'|(?P<plain>https?://[^\s<>"\x60|]+)',
    re.IGNORECASE,
)
URL_TYPE_CHOICES = [
    app_commands.Choice(name="Web or other link", value="Link"),
    app_commands.Choice(name="Direct video file", value="Video"),
    app_commands.Choice(name="Direct audio file", value="Audio"),
    app_commands.Choice(name="Direct image file", value="Image"),
    app_commands.Choice(name="Other direct file", value="File"),
]


def parse_archive_url(value):
    url = value.strip()
    if url.startswith("["):
        prefix = LINK_IN_TEXT.match(url)
        destination = masked_link_destination(url, prefix.end()) if prefix else None
        if not destination or destination[1] != len(url):
            return None
        url = destination[0]
    if url.startswith("<") and url.endswith(">"):
        url = url[1:-1]
    if any(char.isspace() or ord(char) < 32 or char in '<>"\\' for char in url):
        return None
    try:
        parsed = urlsplit(url)
        port = parsed.port
    except ValueError:
        return None
    if parsed.scheme in ("http", "https") and parsed.hostname and parsed.username is None and port != 0:
        return url
    return None


def normalize_spn_hostname(host):
    try:
        return host.encode("idna").decode("ascii").lower().rstrip(".")
    except UnicodeError:
        return ""


def parse_spn_domain(value):
    url = parse_archive_url(value)
    host = urlsplit(url).hostname if url else value.strip()
    domain = normalize_spn_hostname(host)
    labels = domain.split(".")
    if len(labels) < 2 or len(domain) > 253 or not all(
        re.fullmatch(r"[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?", label) for label in labels
    ):
        return None
    return domain.removeprefix("www.") if len(labels) > 2 else domain


def matches_spn_rule(url, rules):
    if url in rules:
        return True
    hostname = normalize_spn_hostname(urlsplit(url).hostname or "")
    while hostname:
        if hostname in rules:
            return True
        hostname = hostname.partition(".")[2]
    return False


def archive_identifier(url, *, save_page_now=False):
    prefix = "arab-news-spn-" if save_page_now else "arab-news-"
    return prefix + sha256(url.strip().encode("utf-8")).hexdigest()


def parse_archive_result(log_text):
    result_pattern = re.compile(r"^(?:\d{4}-\d{2}-\d{2}T\S+\s+)?Archive result: (\{.*\})$")
    identifier_pattern = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,99}")
    parsed = {"saved": [], "existing": [], "skipped": 0}
    media_found = False
    for line in reversed(log_text.splitlines()):
        match = result_pattern.fullmatch(line.strip())
        if not match:
            continue
        try:
            result = json.loads(match[1])
        except json.JSONDecodeError:
            continue
        if not isinstance(result, dict):
            continue
        if "warc_identifier" in result:
            identifier = result["warc_identifier"]
            if isinstance(identifier, str) and identifier_pattern.fullmatch(identifier):
                parsed.setdefault("warc_identifier", identifier)
            continue
        if "wayback_url" in result:
            wayback_url = result["wayback_url"]
            if ("wayback_url" not in parsed and isinstance(wayback_url, str)
                    and re.fullmatch(r'https://web\.archive\.org/web/[0-9]{14}/https?://[^\s<>"\x60|]+', wayback_url, re.I)):
                parsed.update(wayback_url=wayback_url, my_web_archive=result.get("my_web_archive") is True)
            continue
        if media_found:
            continue
        saved = result.get("saved", [])
        existing = result.get("existing", [])
        skipped = result.get("skipped", 0)
        if not (isinstance(saved, list) and isinstance(existing, list) and isinstance(skipped, int)):
            continue
        if skipped < 0 or not all(isinstance(key, str) and identifier_pattern.fullmatch(key) for key in saved + existing):
            continue
        parsed.update(saved=saved, existing=existing, skipped=skipped)
        media_found = True
    return parsed


def determine_url_type(url):
    mime = mimetypes.guess_type(urlsplit(url).path)[0]
    if not mime or mime in {"text/html", "application/xhtml+xml"}:
        return "Link"
    return {"video": "Video", "audio": "Audio", "image": "Image"}.get(mime.split("/", 1)[0], "File")


def masked_link_destination(text, start):
    if text[start] == "<":
        match = re.match(r"<([^\s<>]+)>[ \t]*\)", text[start:])
        return (match[1], start + match.end()) if match else None

    # A closing parenthesis ends the link only outside the URL's own parentheses.
    depth = 0
    end = start
    while end < len(text):
        char = text[end]
        if char == "\\" and text[end + 1:end + 2] in ("(", ")"):
            end += 2
            continue
        if (char == ")" and depth == 0) or char.isspace() or char in '<>"\x60|\\':
            break
        depth += (char == "(") - (char == ")")
        end += 1

    closing = re.match(r"[ \t]*\)", text[end:])
    if depth or not closing:
        return None
    return re.sub(r"\\([()])", r"\1", text[start:end]), end + closing.end()


def extract_tasks_from_text(text):
    url = parse_archive_url(text)
    if url:
        return [(url, determine_url_type(url), False)]

    tasks = []
    seen = set()
    position = 0
    while match := LINK_IN_TEXT.search(text, position):
        position = match.end()
        raw_url = match["plain"]
        if raw_url is None:
            destination = masked_link_destination(text, position)
            if destination is None:
                continue
            raw_url, position = destination
        elif not (match.start() and text[match.start() - 1] == "<"):
            raw_url = raw_url.rstrip(".,!،؛؟")
            while raw_url.endswith(")") and raw_url.count(")") > raw_url.count("("):
                raw_url = raw_url[:-1]
        url = parse_archive_url(raw_url)
        if url and url not in seen:
            seen.add(url)
            tasks.append((url, determine_url_type(url), False))
    return tasks


def extract_component_text(components):
    for component in components:
        content = getattr(component, "content", None)
        if isinstance(content, str):
            yield content
        yield from extract_component_text(getattr(component, "children", ()))


def extract_message_archive_tasks(content, embeds, components=()):
    text_parts = [content]
    for embed in embeds:
        # Automatic link previews already have their source URL in the message body.
        if embed.type not in (None, "rich"):
            continue
        text_parts.extend((
            embed.url or embed.title,
            embed.description,
            embed.author.url or embed.author.name,
            embed.footer.text,
        ))
        for field in embed.fields:
            text_parts.extend((field.name, field.value))
    text_parts.extend(extract_component_text(components))
    return list(dict.fromkeys(
        task for text in text_parts if text for task in extract_tasks_from_text(text)
    ))


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
        await db.execute("CREATE TABLE IF NOT EXISTS spn_urls (url TEXT PRIMARY KEY)")
        await db.commit()


async def get_spn_rules():
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        async with db.execute("SELECT url FROM spn_urls") as cursor:
            return {row[0] for row in await cursor.fetchall()}


async def set_spn_rule(rule, enabled):
    statement = "INSERT OR IGNORE INTO spn_urls (url) VALUES (?)" if enabled else "DELETE FROM spn_urls WHERE url = ?"
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute(statement, (rule,))
        await db.commit()
        return cursor.rowcount > 0


async def claim_spn_series(url, series_id):
    # Allow a persisted series to continue while preventing concurrent series for the same URL.
    archive_key = archive_identifier(url, save_page_now=True)
    await remove_expired_global_exclusions(archive_key)
    expiry_modifier = f"+{STANDARD_EXCLUSION_RETENTION_DAYS} days"
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("""
            INSERT INTO excluded AS current_exclusion (video_id, category, expires_at)
            VALUES (?, ?, datetime('now', ?))
            ON CONFLICT(video_id) DO UPDATE SET expires_at = excluded.expires_at
            WHERE current_exclusion.category = excluded.category AND current_exclusion.expires_at IS NOT NULL
        """, (archive_key, f"spn-series-{series_id}", expiry_modifier))
        await db.commit()
        return cursor.rowcount > 0

async def is_url_excluded_globally(archive_key):
    if not archive_key:
        return False

    await remove_expired_global_exclusions(archive_key)

    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("SELECT 1 FROM excluded WHERE video_id = ?", (archive_key,))
        return await cursor.fetchone() is not None

async def add_to_global_excluded_file(archive_key, category):
    if not archive_key or not category: return
    expiry_modifier = f"+{STANDARD_EXCLUSION_RETENTION_DAYS} days"
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        await db.execute("""
            INSERT INTO excluded (video_id, category, timestamp, expires_at)
            VALUES (?, ?, CURRENT_TIMESTAMP, datetime('now', ?))
            ON CONFLICT(video_id) DO UPDATE SET
                category = excluded.category,
                timestamp = CURRENT_TIMESTAMP,
                expires_at = datetime('now', ?)
        """, (archive_key, category, expiry_modifier, expiry_modifier))
        await db.commit()

async def make_global_exclusion_permanent(archive_key, *, category=None):
    if not archive_key:
        return False

    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("""
            UPDATE excluded
            SET expires_at = NULL
            WHERE video_id = ? AND (? IS NULL OR category = ?)
        """, (archive_key, category, category))
        await db.commit()
        return cursor.rowcount > 0

async def remove_expired_global_exclusions(archive_key=None):
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        if archive_key is None:
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
            """, (archive_key,))

        await db.commit()
        return cursor.rowcount

async def remove_from_global_excluded_file(archive_key):
    if not archive_key: return False
    async with aiosqlite.connect(EXCLUDED_DB_NAME) as db:
        cursor = await db.execute("DELETE FROM excluded WHERE video_id = ?", (archive_key,))
        await db.commit()
        return cursor.rowcount > 0

# --- GitHub API & Archiving Logic ---

async def trigger_workflow(url, trace_id, free_space=False, ignore_existing_item=False,
                           request_user_id=None, request_generation=None, *,
                           save_page_now=False, crawl_website=False, ia_identifier=None, crawl_timestamp=None):
    if request_generation is not None and request_generation != client.job_generation(request_user_id):
        return False, "Request cancelled"
    dispatch_url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/workflows/{WORKFLOW_FILE}/dispatches"
    payload = {
        "ref": "main",
        "inputs": {
            "url": url,
            "trace_id": trace_id,
            "free_space": str(free_space).lower(),
            "ignore_existing_item": str(ignore_existing_item).lower(),
        },
    }
    if save_page_now:
        payload["inputs"]["save_page_now"] = "true"
    if crawl_website:
        payload["inputs"]["crawl_website"] = "true"
        if ia_identifier:
            payload["inputs"]["ia_identifier"] = ia_identifier
        if crawl_timestamp:
            payload["inputs"]["crawl_timestamp"] = crawl_timestamp
    async with client.session.post(dispatch_url, json=payload, headers=GITHUB_HEADERS) as resp:
        if resp.status not in (200, 201, 204):
            text = await resp.text()
            return False, f"Failed to dispatch workflow: {resp.status} {text}"
    return True, None


async def dispatch_archive_tasks(tasks_to_process, user, source, guild_id, free_space, *, from_text_command=False):
    generation = client.job_generation(user.id)
    is_interaction = isinstance(source, discord.Interaction)
    is_dm = guild_id is None
    is_bot_request = bool(getattr(user, "bot", False))
    active_limit = MAX_BOT_CONCURRENT_JOBS if is_bot_request else MAX_CONCURRENT_JOBS

    async def send_response(text, ephemeral=False, suppress_embeds=False, **message_options):
        if source.response.is_done():
            return await source.followup.send(
                text, ephemeral=ephemeral, wait=True, suppress_embeds=suppress_embeds, **message_options,
            )
        await source.response.send_message(
            text, ephemeral=ephemeral, suppress_embeds=suppress_embeds, **message_options,
        )
        return await source.original_response()

    denial = None
    global_ban = await get_global_user_exclusion(user.id)
    if global_ban is not None:
        denial = format_ban_message("You are globally banned from using this bot", *global_ban)
    elif not is_dm:
        exclusion = await get_user_or_channel_exclusion(user.id, source.channel.id, guild_id)
        if exclusion is not None:
            exclusion_type, reason, expires_at = exclusion
            if exclusion_type == "user":
                denial = format_ban_message("You are banned from archiving in this server", reason, expires_at)
            else:
                denial = "Archiving is disabled in this channel"

    if denial:
        allowed_mentions = discord.AllowedMentions.none()
        if is_interaction:
            await send_response(denial, ephemeral=True, allowed_mentions=allowed_mentions)
        elif from_text_command and not is_bot_request:
            if is_dm:
                await source.reply(denial, mention_author=False, allowed_mentions=allowed_mentions)
            else:
                try:
                    await user.send(denial, allowed_mentions=allowed_mentions)
                except discord.Forbidden:
                    await source.reply("Use `/archive` to view your restriction privately", mention_author=False)
        return

    # Acknowledge slash commands before network I/O, no archive request is sent
    if is_interaction and not source.response.is_done():
        await source.response.defer()
    valid_tasks = []
    spn_rules = await get_spn_rules()
    for target_url, url_type, is_silent in tasks_to_process:
        if not is_dm and await is_url_type_excluded(guild_id, url_type):
            continue
        save_page_now = matches_spn_rule(target_url, spn_rules)
        if await is_url_excluded_globally(archive_identifier(target_url, save_page_now=save_page_now)):
            continue
        valid_tasks.append((target_url, url_type, is_silent, save_page_now))

    tasks_to_process = valid_tasks
    if not tasks_to_process:
        if is_interaction:
            await send_response("The provided URL(s) are excluded from archiving", ephemeral=True)
        return

    if user.id != OWNER_ID and not is_bot_request:
        current_jobs = client.active_jobs[user.id]
        current_queue = len(client.queued_jobs[user.id])
        available_slots = max(0, MAX_QUEUED_JOBS - current_queue)
        if user.id not in client.queue_cooldowns:
            available_slots += max(0, MAX_CONCURRENT_JOBS - current_jobs)
        
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
        for _, url_type, _, _ in tasks_to_process:
            type_counts[url_type] += 1

        def pluralize(kind, count):
            return kind if count == 1 else f"{kind}s"

        counts_text = ", ".join(f"{count} {pluralize(kind, count)}" for kind, count in sorted(type_counts.items()))
        batch_id = str(uuid.uuid4())[:8]
        batch_text = f"⏳ Links are being preserved ({counts_text})\n\n||Batch ID: `{batch_id}`||"
        
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

    for target_url, url_type, is_silent, save_page_now in tasks_to_process:
        if generation != client.job_generation(user.id):
            if batch_id:
                client.batch_jobs.pop(batch_id, None)
            return
        effective_silent = is_silent or batch_id is not None
        current_jobs = client.active_jobs[user.id]
        wait_reason = None
        if current_jobs >= active_limit:
            wait_reason = f"You have {current_jobs}/{active_limit} active archive requests running, please wait for one of them to finish"
        elif user.id in client.queue_cooldowns:
            wait_reason = "Waiting for the five-second archive cooldown"
        elif client.queued_jobs[user.id]:
            wait_reason = "Waiting for your earlier queued requests"

        message_for_execution = None
        
        if batch_id:
            message_for_execution = None
        else:
            if is_interaction:
                if wait_reason:
                    queue_pos = len(client.queued_jobs[user.id]) + 1
                    text = (
                        f"Your request for this {url_type.lower()} has been added to the queue (Position: {queue_pos})\n\n"
                        f"||{wait_reason}||"
                    )
                else:
                    text = f"Sending request to preserve this {url_type.lower()}\n\n[||Target||](<{target_url}>)"
                
                message_for_execution = await send_response(text)
            else:
                if wait_reason and not effective_silent:
                    queue_pos = len(client.queued_jobs[user.id]) + 1
                    await source.reply(
                        f"Your request for this {url_type.lower()} has been added to the queue (Position: {queue_pos})\n\n"
                        f"||{wait_reason}||",
                        delete_after=10
                    )
                message_for_execution = source
        
        # Every accepted request has a durable queue entry before it starts.
        if generation != client.job_generation(user.id):
            if batch_id:
                client.batch_jobs.pop(batch_id, None)
            return
        job = (
            target_url, url_type, effective_silent, message_for_execution,
            guild_id, user.id, free_space, batch_id, is_bot_request
        )
        if save_page_now:
            job += (False, False, 0, {"id": uuid.uuid4().hex, "attempt": 1, "captures": [], "crawls": []})
        client.queued_jobs[user.id].append(job)
        await client.save_state()
        await process_all_queues()

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
    reuse_status_message=False,
    ignore_existing_item=False,
    bot_retry_count=0,
    spn_series=None,
    trace_id=None
):
    """
    Handles the actual execution: triggering workflow, updating UI, logging to DB, and starting monitor
    """
    generation = client.job_generation(user_id)
    trace_id = trace_id or (client.next_bot_trace_id() if is_bot_request else str(uuid.uuid4())[:8])
    # Initial User Feedback (Only if not silent)
    status_msg = None
    if not batch_id and not is_silent and original_message:
        try:
            if reuse_status_message or getattr(getattr(original_message, "author", None), "id", None) == client.user.id:
                status_msg = original_message
                await status_msg.edit(content=f"Sending request to preserve this {url_type.lower()}\n\n[||Target||](<{target_url}>)")
            else:
                status_msg = await original_message.reply(f"Sending request to preserve this {url_type.lower()}\n\n[||Target||](<{target_url}>)")
        except asyncio.CancelledError:
            raise
        except Exception:
            pass

    context = {
        "user_id": user_id,
        "target_url": target_url,
        "url_type": url_type,
        "is_silent": is_silent,
        "status_msg": status_msg,
        "guild_id": guild_id,
        "free_space": free_space,
        "start_time": datetime.now(timezone.utc),
        "batch_id": batch_id,
        "is_bot_request": is_bot_request,
        "ignore_existing_item": ignore_existing_item,
        "bot_retry_count": bot_retry_count,
        "spn_series": spn_series,
    }
    success = False
    try:
        save_page_now, crawl_website = website_archive_steps(spn_series)
        crawl_timestamp = None
        ia_identifier = None
        if crawl_website:
            crawl_timestamp = spn_series.get("crawl_timestamp")
            if not crawl_timestamp:
                if bot_retry_count and "crawl_timestamp" not in spn_series:
                    # Older retries may already have written part of this item.
                    crawl_number = spn_series.get("crawl_attempt", 1)
                    ia_identifier = f"arab-news-archive-crawl-{spn_series['id']}-{crawl_number}"
                else:
                    crawl_timestamp = client.next_crawl_timestamp()
                    spn_series["crawl_timestamp"] = crawl_timestamp
                    await client.save_state()
        if spn_series and not await claim_spn_series(target_url, spn_series["id"]):
            if not is_silent and status_msg:
                try:
                    await status_msg.edit(content="➖ A Wayback series for this URL is already active or archived")
                except Exception:
                    pass
            if batch_id:
                await client.update_batch_progress(batch_id, is_success=False)
            return
        client.dispatch_phases[trace_id] = "dispatching"
        success, error = await trigger_workflow(
            target_url, trace_id,
            free_space=free_space or bot_retry_count > 0, ignore_existing_item=ignore_existing_item or bot_retry_count > 0,
            request_user_id=user_id, request_generation=generation, save_page_now=save_page_now, crawl_website=crawl_website,
            ia_identifier=ia_identifier, crawl_timestamp=crawl_timestamp,
        )
        
        if success:
            # Use a string UUID for the run_id to avoid integer overflow
            # The history table schema expects run_id to be INTEGER, but SQLite is dynamic
            # However, to be safe and cleaner, let's use a smaller random int
            history_run_id = int(uuid.uuid4().int % (2**63 - 1))
            
            # Track the accepted dispatch before any fallible DB/UI work, so
            # an error cannot leave a running workflow holding an invisible slot.
            context["history_run_id"] = history_run_id
            client.pending_traces[trace_id] = context
            if generation != client.job_generation(user_id):
                context["cancel_requested"] = True
            client.starting_jobs.pop(trace_id, None)
            await client.save_state()

            if context.get("cancel_requested") or client.pending_traces.get(trace_id) is not context:
                return

            if not spn_series:
                await add_to_global_excluded_file(archive_identifier(target_url), url_type)
            await log_history(guild_id, user_id, target_url, "queued", history_run_id, trace_id)
            
            if not batch_id and not is_silent and status_msg:
                description = f"This {url_type.lower()} is being preserved"
                if spn_series:
                    description = f"Starting · {describe_website_archive(spn_series, bot_retry_count)}"
                try:
                    await status_msg.edit(content=f"⏳ {description}\n\n||Trace ID: `{trace_id}`||")
                except:
                    pass
            
            # poll_github_runs owns this request until completion or timeout.
            return
        failure_message = f"Error starting workflow: {error}"
    except Exception as e:
        logging.error(f"Critical error in processing {target_url}: {e}")
        failure_message = f"Bot internal error: {e}"

    if success or generation != client.job_generation(user_id):
        return
    if spn_series:
        followup = prepare_website_continuation(context)
        await client.report_spn_capture(context, trace_id, followup=followup)
        return followup
    retry = prepare_bot_retry(context)
    if retry:
        failure_message += f"\n\n⚠️ The request will be retried in {retry['wait']}"
    if not is_silent and status_msg:
        try:
            await status_msg.edit(content=failure_message)
        except Exception:
            pass
    if batch_id and not retry:
        await client.update_batch_progress(batch_id, is_success=False)
    return retry


async def run_reserved_archive_job(trace_id, job):
    """Release a reservation exactly once unless a workflow now owns it."""
    retry = None
    try:
        await client.save_state()
        retry = await execute_archive_request(*job, trace_id=trace_id)
    except asyncio.CancelledError:
        if client.starting_jobs.get(trace_id) is job and not client.queue_is_paused(job[5]):
            client.queued_jobs[job[5]].insert(0, job)
        raise
    except Exception:
        logging.exception("Archive dispatch task failed for %s", job[0])
        if len(job) > 7 and job[7] and client.starting_jobs.get(trace_id) is job:
            await client.update_batch_progress(job[7], is_success=False)
    finally:
        client.dispatch_phases.pop(trace_id, None)
        # A workflow may already have completed while its dispatch task was
        # still reporting to Discord. Only release a reservation we still own.
        if client.starting_jobs.get(trace_id) is job:
            del client.starting_jobs[trace_id]
            release_queue_slot(job[5])
            if retry and not client.queue_is_paused(job[5]):
                asyncio.create_task(schedule_delayed_retry(retry["context"], retry["delay_seconds"]))
        await client.save_state()
        await process_all_queues()

async def check_and_process_queue(user_id):
    """Reserve capacity and give each bot request its own numbered trace."""
    started = 0
    while (not client.shutdown_requested and not client.queue_is_paused(user_id)
           and user_id not in client.queue_cooldowns
           and client.queued_jobs[user_id]):
        next_job = client.queued_jobs[user_id][0]
        is_bot_request = len(next_job) > 8 and next_job[8]
        active_limit = MAX_BOT_CONCURRENT_JOBS if is_bot_request else MAX_CONCURRENT_JOBS
        if client.active_jobs[user_id] >= active_limit:
            break
        next_job = client.queued_jobs[user_id].pop(0)
        trace_id = client.next_bot_trace_id() if is_bot_request else str(uuid.uuid4())[:8]
        client.starting_jobs[trace_id] = next_job
        client.active_jobs[user_id] += 1
        task = asyncio.create_task(run_reserved_archive_job(trace_id, next_job))
        client.dispatch_tasks.add(task)
        client.dispatch_task_details[task] = (trace_id, next_job)
        def finished(done):
            client.dispatch_tasks.discard(done)
            client.dispatch_task_details.pop(done, None)
        task.add_done_callback(finished)
        started += 1
    return started


async def process_all_queues():
    for user_id in list(client.queued_jobs):
        await check_and_process_queue(user_id)


async def request_workflow_cancellation(context):
    run_id = context.get("github_run_id")
    if not run_id:
        return False
    if context.get("cancel_acknowledged"):
        return True
    url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/actions/runs/{run_id}/cancel"
    try:
        async with client.session.post(url, headers=GITHUB_HEADERS) as response:
            if response.status == 202:
                context["cancel_acknowledged"] = True
                return True
            logging.warning("Cancellation for run %s returned HTTP %s, polling will check again", run_id, response.status)
    except Exception:
        logging.exception("Could not request cancellation for run %s", run_id)
    return False


async def finish_cancelled_request(trace_id, context, run=None):
    release_archive_request(trace_id, context)
    status = "Archived" if run and run.get("conclusion") == "success" else "Cancelled"
    run_id = context.get("github_run_id")
    try:
        async with aiosqlite.connect(DB_NAME) as db:
            await db.execute(
                "UPDATE history SET status = ?, run_id = COALESCE(?, run_id) "
                "WHERE run_id IN (?, ?) AND status NOT IN ('Archived', 'Already archived')",
                (status, run_id, context.get("history_run_id"), run_id)
            )
            await db.commit()
    except Exception:
        logging.exception("Could not record cancelled trace %s", trace_id)
    if not context.get("is_silent") and context.get("status_msg"):
        try:
            await asyncio.wait_for(context["status_msg"].edit(
                content=(f"Archive {'finished before cancellation' if status == 'Archived' else 'request cancelled by the bot owner'}"
                         f"\n\n||Trace ID: `{trace_id}`||")
            ), timeout=10)
        except Exception:
            logging.warning("Could not update cancellation message for trace %s", trace_id)
    await client.save_state()


async def cancel_archive_jobs(target_user_id=None):
    """Discard the selected backlog and keep live runs tracked until they stop."""
    workflow_cancel = getattr(client, "_workflow_cancel_retries", None)
    if getattr(client, "_workflow_hooks_installed", False) and workflow_cancel is None:
        raise RuntimeError("Update the hosting workflow too, so saved delayed retries can be cancelled")
    async with client.cancel_lock:
        matches = lambda uid: target_user_id is None or uid == target_user_id
        if target_user_id is None:
            client.cancelling_all = True
            client.cancel_epoch += 1
        else:
            client.cancelling_users.add(target_user_id)
            client.user_cancel_epochs[target_user_id] += 1
        result = {"queued_removed":0, "retries_removed":0, "inflight_selected":0,
                  "github_accepted":0, "github_waiting":0}
        batch_ids = set()
        try:
            for uid in list(client.queued_jobs):
                if matches(uid):
                    old_jobs = client.queued_jobs[uid]
                    client.queued_jobs[uid] = []
                    result["queued_removed"] += len(old_jobs)
                    batch_ids.update(job[7] for job in old_jobs if len(job) > 7 and job[7])
            selected_traces = set()
            for trace_id, context in list(client.pending_traces.items()):
                if matches(context["user_id"]):
                    context["cancel_requested"] = True
                    selected_traces.add(trace_id)
                    if context.get("batch_id"):
                        batch_ids.add(context["batch_id"])
            reservations = {trace:job for trace, job in client.starting_jobs.items() if matches(job[5])}
            selected_traces.update(reservations)
            batch_ids.update(job[7] for job in reservations.values() if len(job) > 7 and job[7])

            timers_to_stop = []
            for retry_id, record in list(client.delayed_retry_jobs.items()):
                if matches(record["context"]["user_id"]):
                    del client.delayed_retry_jobs[retry_id]
                    result["retries_removed"] += 1
                    context = record["context"]
                    context["cancel_requested"] = True
                    if context.get("batch_id"):
                        batch_ids.add(context["batch_id"])
                    if record.get("task") is not None:
                        record["task"].cancel()
                        timers_to_stop.append(record["task"])
            if workflow_cancel is not None:
                cleared = await workflow_cancel(target_user_id)
                result["retries_removed"] += cleared["removed"]
                batch_ids.update(cleared["batch_ids"])
            if timers_to_stop:
                await asyncio.gather(*timers_to_stop, return_exceptions=True)

            dispatches = [(task, trace, job) for task, (trace, job) in list(client.dispatch_task_details.items())
                          if trace in reservations]
            for task, trace, job in dispatches:
                if client.dispatch_phases.get(trace) != "dispatching":
                    task.cancel()
            # Let an HTTP dispatch already in progress finish. Its generation
            # check marks an accepted run for cancellation instead of losing it.
            if dispatches:
                await asyncio.gather(*(task for task, _, _ in dispatches), return_exceptions=True)
            for trace, job in reservations.items():
                if client.starting_jobs.get(trace) is job:
                    del client.starting_jobs[trace]
                    release_queue_slot(job[5])
            for batch_id in batch_ids:
                client.batch_jobs.pop(batch_id, None)
            contexts = [context for context in client.pending_traces.values()
                        if matches(context["user_id"]) and context.get("cancel_requested")]
            semaphore = asyncio.Semaphore(4)
            async def cancel_one(context):
                async with semaphore:
                    return await request_workflow_cancellation(context)
            acknowledgements = await asyncio.gather(*(cancel_one(context) for context in contexts))
            result["inflight_selected"] = len(selected_traces)
            result["github_accepted"] = sum(acknowledgements)
            result["github_waiting"] = len(contexts) - result["github_accepted"]
            await client.save_state()
            logging.info("Owner cancelled archive jobs for %s: %s", target_user_id or "all users", result)
            return result
        finally:
            if target_user_id is None:
                client.cancelling_all = False
            else:
                client.cancelling_users.discard(target_user_id)
            await process_all_queues()

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
        title="Arab News Archive Help", 
        description="This bot preserves media and selected web pages in the Internet Archive", 
        color=discord.Color.red()
    )
    embed.add_field(
        name="How It Works",
        value="Paste a public HTTP or HTTPS link in an archive-enabled channel, You can also submit one manually with `/archive` or `!arabarchive <url>`",
        inline=False
    )
    embed.add_field(
        name="Large Downloads",
        value="For large stuff, set `/archive`'s `free_space` option to `True`, or use `!arabarchive <url> --large` (short form: `-l`), Large mode frees storage in the job but the job might take longer to start (approximately 2-3~ minutes)",
        inline=False
    )
    embed.add_field(
        name="User Commands",
        value="`/archive` - Manually archive a link\n`/history` - View your archive history\n`/deletehistory` - Clear your archive history\n`/howmanyjobs [user]` - View a user's lifetime archive job count\n`/leaderboard` - View the archive leaderboard\n`/ping` - Check the bot's latency",
        inline=False
    )
    embed.add_field(
        name="Admin Commands",
        value="`/excludeurl` / `/unexcludeurl` - Manage archivable URL types in your server\n`/excludechannel` / `/unexcludechannel` - Manage excluded Discord channels\n`/excludeuser` / `/unexcludeuser` - Manage excluded users in your server\n`/enableallmessages` / `/disableallmessages` - Toggle automatic scanning of messages for links",
        inline=False
    )
    if interaction.user.id == OWNER_ID:
        embed.add_field(
            name="Owner Commands",
            value="`/spnurl` - Add, remove, or list exact URLs that use Save Page Now\n`/restart` - Restart the bot\n`/shutdown` - Save state and stop the hosting workflow without starting another session",
            inline=False
        )
    await interaction.response.send_message(embed=embed, ephemeral=False)

@client.tree.command(name="excludeurl", description="Exclude a specific URL type from being archived in this server")
@app_commands.describe(url_type="The type of URL to exclude")
@app_commands.choices(url_type=URL_TYPE_CHOICES)
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
@app_commands.choices(url_type=URL_TYPE_CHOICES)
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

@client.tree.command(name="removeurl", description="Remove a link from the global exclusion database (BOT OWNER ONLY)")
@app_commands.describe(url="The link or stored archive key to remove")
async def remove_url(interaction: discord.Interaction, url: str):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    cleaned_url = parse_archive_url(url)
    if cleaned_url:
        media_removed = await remove_from_global_excluded_file(archive_identifier(cleaned_url))
        wayback_removed = await remove_from_global_excluded_file(archive_identifier(cleaned_url, save_page_now=True))
        success = media_removed or wayback_removed
    else:
        success = await remove_from_global_excluded_file(url.strip())
    if success:
        await interaction.response.send_message("Removed from the global exclusion database", ephemeral=True)
    else:
        await interaction.response.send_message("Could not find that link in the global exclusion database", ephemeral=True)

@client.tree.command(name="spnurl", description="Manage domains for Wayback captures and WARC crawls (BOT OWNER ONLY)")
@app_commands.describe(action="Change or view the Save Page Now list", url="Domain such as aljazeera.com, or a website URL")
@app_commands.choices(action=[
    app_commands.Choice(name="Add", value="add"),
    app_commands.Choice(name="Remove", value="remove"),
    app_commands.Choice(name="List", value="list"),
])
async def spn_url_command(interaction: discord.Interaction, action: app_commands.Choice[str], url: str = None):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return

    if action.value == "list":
        rules = sorted(await get_spn_rules())
        text = "\n".join(f"<{entry}>" if "://" in entry else f"`{entry}`" for entry in rules)
        if len(text) > 1900:
            attachment = discord.File(io.BytesIO("\n".join(rules).encode("utf-8")), filename="spn_urls.txt")
            await interaction.response.send_message("Save Page Now entries", file=attachment, ephemeral=True)
        else:
            await interaction.response.send_message(text or "The Save Page Now list is empty", ephemeral=True)
        return

    enabled = action.value == "add"
    value = url or ""
    # Full URLs identify legacy entries on removal. Domain rules are removed by name.
    exact_url = parse_archive_url(value) if not enabled else None
    rule = exact_url or parse_spn_domain(value)
    if not rule:
        await interaction.response.send_message("Enter a domain such as `aljazeera.com`", ephemeral=True)
        return
    changed = await set_spn_rule(rule, enabled)
    if enabled:
        message = (f"Added `{rule}` and its subdomains for Save Page Now and WARC crawls"
                   if changed else f"`{rule}` is already on the Save Page Now list")
    elif exact_url:
        message = (f"Removed <{exact_url}> from the Save Page Now list" if changed else
                   "No matching URL entry, use the domain shown in the list to remove a domain rule")
    else:
        message = (f"Removed `{rule}` from the Save Page Now list"
                   if changed else f"`{rule}` is absent from the Save Page Now list")
    await interaction.response.send_message(message, ephemeral=True)

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

def parse_ban_options(reason, duration):
    reason = (reason or "").strip() or None
    if reason and len(reason) > 500:
        raise ValueError("Use a reason of 500 characters or fewer")
    if duration is None:
        return reason, None

    match = re.fullmatch(r"([0-9]{1,9})\s*([smhdw])", duration.strip().lower())
    if not match or int(match[1]) == 0:
        raise ValueError("Enter a positive duration such as `30m`, `2h`, or `7d`")
    seconds_per_unit = {"s": 1, "m": 60, "h": 3600, "d": 86400, "w": 604800}
    seconds = int(match[1]) * seconds_per_unit[match[2]]
    try:
        expiry = datetime.now(timezone.utc) + timedelta(seconds=seconds)
    except OverflowError as error:
        raise ValueError("Enter a shorter duration") from error
    return reason, int(expiry.timestamp())


def format_ban_message(message, reason, expires_at):
    if expires_at is None:
        message += " permanently"
    else:
        message += f" until <t:{expires_at}:F> (<t:{expires_at}:R>)"
    if reason:
        message += f"\nReason “{discord.utils.escape_markdown(reason)}”"
    return message


@client.tree.command(name="excludeuser", description="Add user to exclusion")
@app_commands.describe(
    reason="Optional reason for the ban",
    duration="Optional duration like 30m, 2h, or 7d. Omit for a permanent ban",
)
@app_commands.checks.has_permissions(ban_members=True)
async def exclude_user(interaction: discord.Interaction, user: discord.User, reason: str = None, duration: str = None):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return

    try:
        reason, expires_at = parse_ban_options(reason, duration)
    except ValueError as error:
        await interaction.response.send_message(str(error), ephemeral=True)
        return

    success = await add_exclusion(
        interaction.guild.id, "user", user.id, interaction.user.name, reason=reason, expires_at=expires_at,
    )
    if success:
        await interaction.response.send_message(
            format_ban_message(f"User ID `{user.id}` excluded from this server", reason, expires_at),
            ephemeral=True,
            allowed_mentions=discord.AllowedMentions.none(),
        )
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
@app_commands.describe(
    user_id="The raw Discord user ID or a copied user mention",
    reason="Optional reason for the ban",
    duration="Optional duration like 30m, 2h, or 7d. Omit for a permanent ban",
)
async def global_exclude(interaction: discord.Interaction, user_id: str, reason: str = None, duration: str = None):
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

    try:
        reason, expires_at = parse_ban_options(reason, duration)
    except ValueError as error:
        await interaction.response.send_message(str(error), ephemeral=True)
        return

    if await add_global_user_exclusion(target_user_id, interaction.user.name, reason=reason, expires_at=expires_at):
        await interaction.response.send_message(
            format_ban_message(f"User ID `{target_user_id}` globally excluded", reason, expires_at),
            ephemeral=True,
            allowed_mentions=discord.AllowedMentions.none(),
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

def resolve_bot_message_server(interaction, server_id):
    if server_id is None:
        if interaction.guild:
            return interaction.guild.id
        raise ValueError("Enter a server ID when using this command in DMs")

    server_id = server_id.strip()
    if not re.fullmatch(r"[0-9]{17,20}", server_id) or not 0 < int(server_id) < 2**63:
        raise ValueError("Enter a valid Discord server ID")
    return int(server_id)


@client.tree.command(name="allowbotmessages", description="Allow bot messages to trigger archives in a server (BOT OWNER ONLY)")
@app_commands.describe(server_id="Optional Discord server ID. Uses the current server when omitted")
async def allow_bot_messages(interaction: discord.Interaction, server_id: str = None):

    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("Only the bot owner can use this command", ephemeral=True)
        return

    try:
        guild_id = resolve_bot_message_server(interaction, server_id)
    except ValueError as error:
        await interaction.response.send_message(str(error), ephemeral=True)
        return

    success = await set_allow_bot_messages(guild_id, interaction.user.name)
    
    if success:
        await interaction.response.send_message(
            f"Bot messages can now trigger archive requests in server `{guild_id}`",
            ephemeral=True
        )
    else:
        await interaction.response.send_message(f"Bot messages are already allowed in server `{guild_id}`", ephemeral=True)

@client.tree.command(name="disallowbotmessages", description="Disable archiving from bot messages in a server (BOT OWNER ONLY)")
@app_commands.describe(server_id="Optional Discord server ID. Uses the current server when omitted")
async def disallow_bot_messages(interaction: discord.Interaction, server_id: str = None):

    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("Only the bot owner can use this command", ephemeral=True)
        return

    try:
        guild_id = resolve_bot_message_server(interaction, server_id)
    except ValueError as error:
        await interaction.response.send_message(str(error), ephemeral=True)
        return

    success = await unset_allow_bot_messages(guild_id)
    
    if success:
        await interaction.response.send_message(f"Disabled archiving from bot messages in server `{guild_id}`", ephemeral=True)
    else:
        await interaction.response.send_message(f"Archiving from bot messages is already disabled in server `{guild_id}`", ephemeral=True)

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

@client.tree.command(name="enableallmessages", description="Turn on reading all messages for links")
@app_commands.checks.has_permissions(manage_messages=True)
async def enableallmessages(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return
        
    await enable_all_messages(interaction.guild.id)
    await interaction.response.send_message("Reading all messages has been turned on", ephemeral=True)

@client.tree.command(name="disableallmessages", description="Turn off reading all messages for links")
@app_commands.checks.has_permissions(manage_messages=True)
async def disableallmessages(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("This command can only be used in a server", ephemeral=True)
        return
        
    await disable_all_messages(interaction.guild.id, interaction.user.name)
    await interaction.response.send_message("Reading all messages has been turned off", ephemeral=True)

@client.tree.command(name="archive", description="Manually archive a public link")
@app_commands.describe(url="A public HTTP or HTTPS link", free_space="Free additional storage for large downloads")
async def archive_cmd(interaction: discord.Interaction, url: str, free_space: bool = False):
    guild_id = interaction.guild.id if interaction.guild else None

    target_url = parse_archive_url(url)
    if not target_url:
        await interaction.response.send_message("Enter a valid HTTP or HTTPS link", ephemeral=True)
        return
    tasks_to_process = [(target_url, determine_url_type(target_url), False)]
    await dispatch_archive_tasks(tasks_to_process, interaction.user, interaction, guild_id, free_space)

@client.tree.command(name="ping", description="Test the bot's latency")
async def ping(interaction: discord.Interaction):
    await interaction.response.send_message(f"Pong! `{round(client.latency*1000)}ms`", ephemeral=False)

@client.tree.command(name="jobs", description="Show active jobs, queued requests, and queue blockers (BOT OWNER ONLY)")
async def jobs(interaction: discord.Interaction):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return
    
    active_users = {uid: count for uid, count in client.active_jobs.items() if count > 0}
    queued_users = {uid: len(queue) for uid, queue in client.queued_jobs.items() if queue}
    embed = discord.Embed(title="Arab News Archive Queue", color=discord.Color.blue())
    lines = [f"<@{uid}>: {active_users.get(uid, 0)} active, {queued_users.get(uid, 0)} queued"
             for uid in sorted(set(active_users) | set(queued_users))]
    embed.description = ("\n".join(lines)[:3900] if lines else "No active or queued jobs right now")
    bot_traces = [(trace_id, context) for trace_id, context in client.pending_traces.items()
                  if context.get("is_bot_request") or is_bot_trace_id(trace_id)]
    if bot_traces:
        bot_lines = [f"`{trace_id}`: {context.get('github_status', 'awaiting run match')}"
                     for trace_id, context in bot_traces[:10]]
        if len(bot_traces) > 10:
            bot_lines.append(f"And {len(bot_traces) - 10} more")
        embed.add_field(name="Active bot requests", value="\n".join(bot_lines)[:1024], inline=False)
    if client.github_poll_error:
        embed.add_field(name="GitHub polling error", value=client.github_poll_error[:1024], inline=False)
    embed.set_footer(text=f"{sum(active_users.values())} active, {sum(queued_users.values())} queued, {len(client.starting_jobs)} starting")
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
    free_space = context.get("free_space", False) or context.get("bot_retry_count", 0) > 0
    embed.add_field(name="Free Space", value=str(free_space), inline=True)
    
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

@client.tree.command(name="cancelalljobs", description="Cancel queued, retrying, and active archive jobs (BOT OWNER ONLY)")
@app_commands.describe(user_id="Optional Discord user/bot ID or mention, leave blank to cancel everyone's jobs")
async def cancelalljobs(interaction: discord.Interaction, user_id: str = None):
    if interaction.user.id != OWNER_ID:
        await interaction.response.send_message("You are not authorized to use this command", ephemeral=True)
        return
    target_user_id = None
    if user_id is not None:
        target_user_id = parse_discord_user_id(user_id)
        if target_user_id is None:
            await interaction.response.send_message("Enter a 17-20 digit user/bot ID or paste a user mention", ephemeral=True)
            return
    await interaction.response.defer(ephemeral=True)
    try:
        result = await cancel_archive_jobs(target_user_id)
    except Exception as error:
        logging.exception("Could not cancel archive jobs")
        await interaction.followup.send(f"Could not finish cancelling jobs: {error}", ephemeral=True)
        return
    scope = f"user/bot `{target_user_id}`" if target_user_id is not None else "all users and bots"
    text = (f"Cancellation requested for {scope}\n"
            f"Queued requests removed: {result['queued_removed']}\n"
            f"Scheduled retries removed: {result['retries_removed']}\n"
            f"Active/starting requests selected: {result['inflight_selected']}\n"
            f"GitHub cancellation requests accepted: {result['github_accepted']}")
    if result["github_waiting"]:
        text += f"\nAwaiting run discovery or a successful GitHub cancellation request: {result['github_waiting']}"
    text += "\nNew requests remain enabled, completed archives and history are kept"
    await interaction.followup.send(text, ephemeral=True)


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
    command = re.match(r"\s*!arabarchive(?:\s|$)", content, re.IGNORECASE)
    has_archive_cmd = command is not None
    if not is_dm and not has_archive_cmd and not await is_all_messages_enabled(guild_id):
        return
    if command:
        content = content[command.end():]

    free_space = bool(re.search(r'(?:^|\s)(?:--large|-l)(?:\s|$)', content))

    # Handle bot messages
    if message.author.bot:
        # In DMs, ignore all bot messages
        if is_dm:
            return
        # In servers, only process if bot messages are allowed
        if not await is_bot_messages_allowed(guild_id):
            return

    tasks_to_process = extract_message_archive_tasks(content, message.embeds, message.components)
    if not tasks_to_process:
        return

    await dispatch_archive_tasks(
        tasks_to_process, message.author, message, guild_id, free_space, from_text_command=has_archive_cmd,
    )

if __name__ == "__main__":
    client.run(DISCORD_TOKEN)
