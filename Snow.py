import os
import sys
import time
import threading
import socket
import json
import queue
import re
from http.server import HTTPServer, SimpleHTTPRequestHandler
from collections import deque
from playsound import playsound # pip install playsound==1.2.2
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import WebDriverException, StaleElementReferenceException, UnexpectedAlertPresentException, NoAlertPresentException
import getpass
# ===================================================================
# --- ✍️ CONFIGURATION ---
# ===================================================================
USER = input("ServiceNow Username: ")
PASSWORD = getpass.getpass("ServiceNow Password: ")
# --- ServiceNow URLs ---
BASE_URL = "https://servicecafe.service-now.com"
LOGIN_URL = f"{BASE_URL}/nav_to.do?uri=%2F$pa_dashboard.do"
URL_NEW_STATE_LIST = "https://servicecafe.service-now.com/incident_list.do?sysparm_query=state%3D1%5Eassignment_group.name%3DCognizant%20Network%20Ops"
# --- New Queue URLs (Placeholders - Update as needed) ---
# Incidents New
URL_INC_N_L2L3 = ""
URL_INC_N_FW = ""
URL_INC_N_AKAMAI = ""
URL_INC_N_SASE = ""
# RITMs New
URL_RITM_N_OPS = ""
URL_RITM_N_L2L3 = ""
URL_RITM_N_FW = ""
URL_RITM_N_AKAMAI = ""
URL_RITM_N_IAP = "https://servicecafe.service-now.com/sc_req_item_list.do?sysparm_query=state%3D1%5Eassignment_group%3D676f1d2bdb05e8902d13892d1396194f%5Eassignment_group%3Da12cdabadb4460509de0ebd84896191f%5EORassignment_group%3Deb62204c1b81e450b8e4bbbc0a4bcbf1%5EORassignment_group%3Dbccf27e9db142c1065313318f49619f2%5EORassignment_group%3D676f1d2bdb05e8902d13892d1396194f%5EORassignment_group%3D9d73f8fcdb3b5f000f1bf2f9af9619d0%5EORassignment_group%3Dc4f2297a4f001a00dd83afdd0210c7b4%5EORassignment_group%3Ddef9e4d7db2a641065313318f49619fd%5EORassignment_group%3D83612fa74f636240b2343f828110c7b2%5EORassignment_group%3D6f0d44674707e550bfb84f32736d43ba%5Esys_created_on%3Ejavascript:gs.dateGenerate(%272020-11-30%27%2C%2723:59:59%27)%5EstateNOT%20IN24%2C14"
# Incidents WIP
URL_INC_W_FW = ""
URL_INC_W_AKAMAI = ""
URL_INC_W_SASE = ""
# RITMs WIP
URL_RITM_W_FW = ""
URL_RITM_W_AKAMAI = ""
URL_RITM_W_IAP = ""
# --- File Paths (Placeholders - Set in Main) ---
IS_WINDOWS = os.name == "nt"
if IS_WINDOWS:
    import msvcrt
BASE_DATA_DIR = (
    r"C:\Users\Mahesh\Downloads"
    if IS_WINDOWS
    else "/workspaces/Snow_Autoupdate/data"
)
os.makedirs(BASE_DATA_DIR, exist_ok=True)
SOUND_PATH = os.path.join(BASE_DATA_DIR, "miui.mp3")
QUEUE_SOUND_PATH = os.path.join(BASE_DATA_DIR, "kidding-obito.mp3")
REOPEN_FILE_PATH = os.path.join(BASE_DATA_DIR, "Reopen.txt")
# Default paths (will be overwritten by user choice)
LOG_FILE_PATH = os.path.join(BASE_DATA_DIR, "Log.txt")
LIVE_FILE_PATH = os.path.join(BASE_DATA_DIR, "Live.txt")
# --- Predefined Shift Users List ---
SHIFT_USERS_LIST = [
    "Varsha Patil",
    "Padmanabhan Ramamoorthy",
    "Savitri S",
    "Jagadesh Kumar",
    "Nageswara Usirikayala",
    "Jonnala Reddy Karthik",
    "Haritha Chinnavula",
    "Mounika Kandula",
    "Guru Prasad",
    "Pushparaj P2"
]
# --- Settings ---
POLL_INTERVAL = 3 # ⚡ Changed to 3 seconds
MAX_UNASSIGN_SKIP_COUNT = 2 # Number of skips before auto-assigning unassigned tickets
MAX_ASSIGN_SKIP_COUNT = 4 # Number of skips before auto-acknowledging assigned tickets to WIP
LIVE_CLEAR_INTERVAL = 180 # 🧹 Clear Live.txt every 180 seconds (3 mins)
# ⚡ NEW: Auto-Restart Settings to prevent lag
AUTO_RESTART_CYCLES = 300
AUTO_RESTART_MINUTES = 30
# Visual Formatting Settings
LINE_LENGTH = 92 # Width of the divider lines
LOG_BUFFER_SIZE = 999999 # ⚡ INCREASED: Effectively infinite for session to show logs from start
WEB_SERVER_PORT = 8000 # Port for mobile log viewer
# Global input queue for mobile commands
mobile_input_queue = queue.Queue()
# ⚡ FIX: Initialize with default user immediately so mobile app isn't empty on load
pending_ticket_data = {'ticket_data': None, 'shift_users': ["Mahesh Kumar"]}
# Global counters for cycles
new_count = 0
reopen_count = 0 # For reopen > 2
ack_count = 0
skipped_count = 0
restart_count = 0 # ⚡ NEW: Track number of restarts
cycle_counter = 0
# Global queue counts (default 0, update when scraping if URLs provided)
queue_counts = {
    'inc_n_l2l3': 0, 'inc_n_fw': 0, 'inc_n_akamai': 0, 'inc_n_sase': 0,
    'ritm_n_ops': 0, 'ritm_n_l2l3': 0, 'ritm_n_fw': 0, 'ritm_n_akamai': 0, 'ritm_n_iap': 0,
    'inc_w_fw': 0, 'inc_w_akamai': 0, 'inc_w_sase': 0,
    'ritm_w_fw': 0, 'ritm_w_akamai': 0, 'ritm_w_iap': 0
}
# ⚡ NEW: Global History of Updated Tickets
updated_tickets_history = []
# Global stop flags
stop_script = False
cancel_current_ticket = False
restart_requested = False
scrap_toggle_requested = False
# Global sound enabled for queue updates
sound_enabled = True
# Global scrap enabled for notes scraping
scrap_enabled = False
# ⚡ ALARM GLOBALS
alarm_enabled = False
alarm_interval_minutes = 10 # Default 10 minutes
alarm_last_played = 0
# State name to value mapping
state_name_to_val = {
    'Work in Progress': '4',
    'Pending Tasks': '22',
    'Pending Vendor': '21',
    'Pending User': '18',
    'Pending Change': '19'
}
# ===================================================================
# --- LIVE LOG MANAGER (APPEND MODE) ---
# ===================================================================
class LiveLogManager:
    """
    1. Mobile Buffer: RAM (Fastest) for the Web Server.
    2. Log.txt: Append Mode (Historical History - Never deleted).
    3. Live.txt: Append Mode (Clears every 3 mins).
    """
    def __init__(self, log_file, live_file, buffer_size=100):
        self.log_file = log_file
        self.live_file = live_file
       
        # Buffers & Timers
        self.buffer = deque()
        self.lock = threading.Lock()
        self.last_clear_time = time.time() # Timer for clearing Live.txt
    def update_paths(self, new_log_path, new_live_path):
        """Updates paths dynamically based on user input"""
        self.log_file = new_log_path
        self.live_file = new_live_path
    def add(self, message):
        current_time = time.time()
        time_str = time.strftime("[%Y-%m-%d %H:%M:%S]")
        full_line = f"{time_str} {message}"
       
        with self.lock:
            # --- 1. Update Mobile Web Buffer ---
            self.buffer.append(full_line)
       
        # --- 2. Write to HISTORICAL Log (Always Append) ---
        try:
            log_dir = os.path.dirname(self.log_file)
            if not os.path.exists(log_dir): os.makedirs(log_dir)
            with open(self.log_file, "a", encoding="utf-8") as f:
                f.write(full_line + "\n")
        except: pass
        # --- 3. Handle LIVE Log (Clear if 3 mins passed) ---
        try:
            log_dir = os.path.dirname(self.live_file)
            if not os.path.exists(log_dir): os.makedirs(log_dir)
           
            # Check if 3 minutes have passed
            if current_time - self.last_clear_time >= LIVE_CLEAR_INTERVAL:
                with open(self.live_file, "w", encoding="utf-8") as f:
                    f.write(f"[{time_str}] 🧹 REFRESH: Live Log Cleared (3 Min Cycle)\n")
                self.last_clear_time = current_time # Reset timer
           
            # Write the new line
            with open(self.live_file, "a", encoding="utf-8") as f:
                f.write(full_line + "\n")
        except: pass
    def get_all(self):
        """Get all logs for mobile viewer."""
        with self.lock:
            return "\n".join(self.buffer)
# Global log manager (Initialized with defaults, updated in Main)
log_manager = LiveLogManager(LOG_FILE_PATH, LIVE_FILE_PATH, LOG_BUFFER_SIZE)
def log(message):
    """Prints to console (clean, no timestamp) and saves to file with timestamp."""
    print(message)
    log_manager.add(message)
# ===================================================================
# --- WEB SERVER FOR MOBILE WITH CLI CONTROL ---
# ===================================================================
class MobileLogHandler(SimpleHTTPRequestHandler):
    """HTTP handler to serve logs to mobile devices with interactive CLI."""
    # ⚡ UPDATED: Helper to handle writes safely without crashing on disconnect
    def safe_write(self, data):
        try:
            self.wfile.write(data)
        except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
            pass # Client disconnected
    def do_GET(self):
        if self.path == '/' or self.path == '':
            self.send_response(200)
            self.send_header('Content-type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
            self.end_headers()
           
            html = '''
            <!DOCTYPE html>
            <html>
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <title>Live Script Monitor</title>
                <style>
                        * { margin: 0; padding: 0; box-sizing: border-box; }
                        body {
                            font-family: 'Courier New', monospace;
                            background: #0a0e27;
                            color: #00ff88;
                            padding: 10px;
                            height: 95vh; /* Full mobile height */
                            overflow: hidden;
                            display: flex;
                            flex-direction: column;
                            box-sizing: border-box;
                        }
                        .header {
                            text-align: center;
                            margin-bottom: 8px;
                            font-weight: bold;
                            font-size: 16px;
                            color: #ff6b6b;
                            border-bottom: 2px solid #00ff88;
                            padding-bottom: 5px;
                            flex-shrink: 0;
                        }
                       
                        .controls {
                            display: flex;
                            gap: 4px; /* Reduced space between buttons */
                            margin-bottom: 8px;
                            justify-content: center;
                            align-items: center; /* Vertically center */
                            flex-shrink: 0;
                            white-space: nowrap; /* Prevent wrapping */
                            flex-wrap: wrap; /* Allow wrap if needed */
                        }
                       
                        .refresh-btn, .toggle-btn, .stop-btn, .sound-toggle-btn, .restart-btn, .scrap-toggle-btn {
                            padding: 4px 8px; /* Reduced padding */
                            border: none;
                            border-radius: 4px;
                            cursor: pointer;
                            font-weight: bold;
                            font-family: monospace;
                            font-size: 10px; /* Reduced font-size */
                        }
                        .refresh-btn {
                            background: #00ff88;
                            color: #0a0e27;
                        }
                        .refresh-btn:hover { background: #00dd77; }
                       
                        .toggle-btn {
                            background: #ff6b6b;
                            color: #0a0e27;
                        }
                        .toggle-btn:hover { background: #ff4444; }
                        .stop-btn {
                            background: #ff4444;
                            color: #0a0e27;
                        }
                        .stop-btn:hover { background: #ff2222; }
                        .sound-toggle-btn {
                            background: #00ff88;
                            color: #0a0e27;
                        }
                        .sound-toggle-btn.off {
                            background: #ff6b6b;
                        }
                        /* ⚡ NEW RESTART BUTTON STYLE */
                        .restart-btn {
                            background: #ffaa00;
                            color: #0a0e27;
                        }
                        .restart-btn:hover { background: #ffcc00; }
                        .scrap-toggle-btn {
                            background: #aa00ff;
                            color: #0a0e27;
                        }
                        .scrap-toggle-btn:hover { background: #cc00ff; }
                        .scrap-toggle-btn.off {
                            background: #ff6b6b;
                        }
                        /* ⚡ ALARM BUTTON STYLES */
                        .alarm-wrapper {
                            display: flex;
                            align-items: center;
                            background: #ff6b6b; /* Default Off Color */
                            border-radius: 4px;
                            padding: 0;
                            position: relative;
                        }
                        .alarm-wrapper.on {
                            background: #00ff88;
                        }
                        .alarm-btn {
                            background: transparent;
                            border: none;
                            color: #0a0e27;
                            font-weight: bold;
                            font-family: monospace;
                            font-size: 10px;
                            padding: 4px 6px;
                            cursor: pointer;
                            border-right: 1px solid rgba(0,0,0,0.3);
                        }
                        .alarm-dropdown-btn {
                            background: transparent;
                            border: none;
                            color: #0a0e27;
                            font-weight: bold;
                            font-size: 10px;
                            padding: 4px 6px;
                            cursor: pointer;
                        }
                        .alarm-dropdown-content {
                            display: none;
                            position: absolute;
                            top: 100%;
                            left: 0;
                            background-color: #f9f9f9;
                            min-width: 120px;
                            box-shadow: 0px 8px 16px 0px rgba(0,0,0,0.2);
                            z-index: 1000;
                            border-radius: 4px;
                            overflow: hidden;
                        }
                        .alarm-dropdown-content button {
                            color: black;
                            padding: 8px 12px;
                            text-decoration: none;
                            display: block;
                            width: 100%;
                            text-align: left;
                            border: none;
                            background: white;
                            font-family: monospace;
                            font-size: 11px;
                            cursor: pointer;
                            border-bottom: 1px solid #ddd;
                        }
                        .alarm-dropdown-content button:hover {background-color: #f1f1f1}
                        .alarm-dropdown-content.show {display: block;}
                        .status {
                            font-size: 11px;
                            color: #00ccff;
                            margin-bottom: 5px;
                            text-align: center;
                            flex-shrink: 0;
                        }
                       
                        .stats-section {
                            margin-bottom: 8px;
                            padding: 8px;
                            background: #0d1117;
                            border: 1px solid #00ff88;
                            border-radius: 5px;
                            font-size: 10px;
                            flex-shrink: 0;
                            text-align: center; /* ⚡ Center all text */
                        }
                        .stats-row {
                            display: flex;
                            justify-content: center; /* ⚡ Center the row content */
                            align-items: center;
                            gap: 5px;
                        }
                        .stat-col {
                            flex: 1;
                            display: flex;
                            flex-direction: column; /* ⚡ Stack vertically for better center look */
                            justify-content: center;
                            align-items: center;
                            gap: 2px;
                            min-width: 50px;
                        }
                        .stats-label {
                            font-weight: bold;
                            color: #ff6b6b;
                            white-space: nowrap;
                            font-size: 10px;
                        }
                       
                        .container {
                            display: flex;
                            flex: 1;
                            overflow: hidden;
                            min-height: 0;
                            position: relative; /* REQUIRED for absolute positioning of child */
                        }
                        .logs-container {
                            width: 100%;
                            overflow-y: auto;
                            border: 2px solid #00ff88;
                            background: #0d1117;
                            padding: 10px;
                            border-radius: 5px;
                            font-size: 11px;
                            line-height: 1.5;
                            min-height: 0;
                        }
                       
                        /* 🔴 ANIMATED RED BOX (SLIDING DRAWER) - ACTIONS PANEL (RIGHT) */
                        .cli-panel {
                            position: absolute; /* CHANGED from fixed to absolute */
                            top: 0; /* Align to top of container */
                            bottom: 0; /* Align to bottom of container */
                            right: 0;
                            height: 100%; /* Fill height of container */
                            width: 85%;
                            max-width: 350px;
                            background: #0d1117;
                            border-left: 2px solid #ff6b6b;
                            border-top: 2px solid #ff6b6b;
                            border-bottom: 2px solid #ff6b6b;
                            border-top-left-radius: 10px;
                            border-bottom-left-radius: 10px;
                            padding: 15px;
                            display: flex;
                            flex-direction: column;
                            box-shadow: -5px 0 20px rgba(0,0,0,0.8);
                            /* Animation Properties */
                            transform: translateX(110%); /* Hidden to the right */
                            transition: transform 0.3s cubic-bezier(0.25, 0.8, 0.25, 1);
                            z-index: 999;
                        }
                       
                        /* Class to slide it in */
                        .cli-panel.open {
                            transform: translateX(0); /* Slide left into view */
                        }
                       
                        /* 🔵 ANIMATED BLUE BOX (SLIDING DRAWER) - UPDATES PANEL (LEFT) */
                        .updates-panel {
                            position: absolute;
                            top: 0;
                            bottom: 0;
                            left: 0;
                            height: 100%;
                            width: 85%;
                            max-width: 350px;
                            background: #0d1117;
                            border-right: 2px solid #4488ff;
                            border-top: 2px solid #4488ff;
                            border-bottom: 2px solid #4488ff;
                            border-top-right-radius: 10px;
                            border-bottom-right-radius: 10px;
                            padding: 15px;
                            display: flex;
                            flex-direction: column;
                            box-shadow: 5px 0 20px rgba(0,0,0,0.8);
                           
                            /* Animation Properties */
                            transform: translateX(-110%); /* Hidden to the left */
                            transition: transform 0.3s cubic-bezier(0.25, 0.8, 0.25, 1);
                            z-index: 998;
                        }
                       
                        /* Class to slide it in */
                        .updates-panel.open {
                            transform: translateX(0); /* Slide right into view */
                        }
                       
                        .cli-header, .updates-header {
                            color: #ff6b6b;
                            font-weight: bold;
                            margin-bottom: 10px;
                            border-bottom: 1px solid #ff6b6b;
                            padding-bottom: 5px;
                            display: flex;
                            justify-content: space-between;
                            align-items: center;
                        }
                        .updates-header {
                            color: #4488ff;
                            border-bottom-color: #4488ff;
                        }
                       
                        .close-panel-btn {
                            background: none;
                            border: none;
                            color: inherit;
                            font-size: 16px;
                            cursor: pointer;
                            padding: 0 5px;
                            font-weight: bold;
                        }
                       
                        .cli-content {
                            flex: 1;
                            overflow-y: auto;
                            margin-bottom: 8px;
                            min-height: 80px;
                        }
                        .cli-input {
                            display: flex;
                            flex-direction: column;
                            gap: 8px;
                            flex-shrink: 0;
                        }
                        .input-group {
                            display: flex;
                            gap: 5px;
                        }
                        .input-group input, .input-group select {
                            flex: 1;
                            padding: 8px;
                            background: #1a1f3a;
                            color: #00ff88;
                            border: 1px solid #00ff88;
                            border-radius: 3px;
                            font-family: monospace;
                            font-size: 12px;
                        }
                        .input-group button {
                            padding: 8px 12px;
                            background: #00ff88;
                            color: #0a0e27;
                            border: none;
                            border-radius: 3px;
                            cursor: pointer;
                            font-weight: bold;
                            font-size: 12px;
                            flex: 1;
                        }
                        .input-group button:hover {
                            background: #00dd77;
                        }
                        #workNotesInput {
                            width: 100% !important;
                            height: 60px !important;
                            padding: 8px !important;
                            background: #1a1f3a !important;
                            color: #00ff88 !important;
                            border: 1px solid #00ff88 !important;
                            border-radius: 3px !important;
                            font-family: monospace !important;
                            font-size: 11px !important;
                            resize: none !important;
                            overflow-y: auto !important;
                        }
                        .log-line {
                            margin: 3px 0;
                            white-space: pre-wrap;
                            word-break: break-word;
                        }
                        .error { color: #ff4444; }
                        .success { color: #44ff44; }
                        .warning { color: #ffaa00; }
                        .info { color: #4488ff; }
                        .action { color: #ff88ff; }
                        .cli-msg { color: #ffaa00; margin-bottom: 4px; font-size: 12px; }
                       
                        .logs-container::-webkit-scrollbar { width: 6px; }
                        .logs-container::-webkit-scrollbar-track { background: #0d1117; }
                        .logs-container::-webkit-scrollbar-thumb { background: #00ff88; border-radius: 3px; }
                       
                        .auto-scroll-toggle {
                            display: flex;
                            align-items: center;
                            gap: 5px;
                            font-size: 12px;
                        }
                        .toggle-checkbox { cursor: pointer; width: 16px; height: 16px; }
                       
                        .queue-tables {
                            /* flex: 1; Removed flex:1 here to allow history to grow */
                            overflow-y: auto;
                            display: flex;
                            flex-direction: column;
                            gap: 8px;
                            max-height: 40%; /* Limit queue height */
                            flex-shrink: 0; /* Prevent shrinking */
                        }
                        .queue-table {
                            background: #1a1f3a;
                            border: 1px solid #4488ff;
                            border-radius: 3px;
                            padding: 4px;
                            font-size: 9px;
                        }
                        .queue-header, .queue-row {
                            display: flex;
                            align-items: center;
                        }
                        .type-header {
                            flex: 1.5;
                            text-align: left;
                            font-weight: bold;
                            color: #4488ff;
                        }
                        .header-cell {
                            flex: 1;
                            text-align: center;
                            font-weight: bold;
                            color: #4488ff;
                        }
                        .empty-cell {
                            flex: 1.5;
                        }
                        .queue-count {
                            flex: 1;
                            text-align: center;
                            font-weight: bold;
                            color: #00ff88;
                            font-size: 12px;
                        }
                        /* ⚡ HISTORY CARD STYLES */
                        .history-card {
                            background: #161b33;
                            border-left: 3px solid #ff88ff;
                            margin-bottom: 8px;
                            padding: 8px;
                            border-radius: 4px;
                            box-shadow: 0 2px 4px rgba(0,0,0,0.3);
                        }
                        .h-ticket {
                            color: #00ff88;
                            font-weight: bold;
                            font-size: 12px;
                            margin-bottom: 2px;
                        }
                        .h-desc {
                            color: #ddd;
                            font-size: 11px;
                            white-space: normal; /* Allow text wrapping */
                            word-wrap: break-word;
                            line-height: 1.3;
                            margin-bottom: 4px;
                            display: block;
                        }
                        .h-state {
                            color: #4488ff;
                            font-size: 11px;
                            font-weight: bold;
                            margin-bottom: 2px;
                        }
                        .h-update {
                            color: #ffaa00;
                            font-size: 10px;
                            font-style: italic;
                        }
                        /* ⚡ SCROLLABLE CONTAINER FIX */
                        #historyContainer {
                            flex: 1;
                            overflow-y: auto;
                            min-height: 0; /* Crucial for nested flex scrolling */
                            border-top: 1px solid #333;
                            margin-top: 5px;
                        }
                </style>
            </head>
            <body>
                    <div class="header">🔴 LIVE SCRIPT MONITOR 🔴</div>
                    <div class="controls">
           
                        <label class="auto-scroll-toggle">
                            <input type="checkbox" id="autoScroll" class="toggle-checkbox" checked>
                            Auto
                        </label>
                        <button class="refresh-btn" onclick="manualRefresh()">🔄 Refresh</button>
                        <button class="toggle-btn" onclick="toggleUpdates()">📊 Updates</button>
                        <button class="toggle-btn" onclick="toggleCLI()">📱 Actions</button>
                        <button class="sound-toggle-btn" id="soundToggle" onclick="toggleSound()">🔊 Sound: On</button>
                        <button class="stop-btn" onclick="stopScript()">🛑 Stop</button>
                        <button class="restart-btn" onclick="restartSession()">♻️ Restart</button>
                        <button class="scrap-toggle-btn" id="scrapToggle" onclick="toggleScrap()">📄 Scrap: Off</button>
                       
                        <div class="alarm-wrapper" id="alarmWrapper">
                            <button class="alarm-btn" id="alarmBtn" onclick="toggleAlarm()">⏰ ALARM</button>
                            <button class="alarm-dropdown-btn" onclick="toggleAlarmMenu()">▶</button>
                            <div id="alarmDropdown" class="alarm-dropdown-content">
                                <button onclick="setAlarmInterval(5)">5 Minutes</button>
                                <button onclick="setAlarmInterval(10)">10 Minutes</button>
                                <button onclick="setAlarmInterval(15)">15 Minutes</button>
                                <button onclick="setCustomAlarm()">Custom Minutes</button>
                            </div>
                        </div>
                    </div>
                   
                    <div class="status">Status: <span id="status">Connecting...</span> | Cycles: <span id="cycleCount">0</span> | Alarm: <span id="alarmStatus">OFF</span> (<span id="alarmInterval">10</span>m)</div>
                   
                    <div class="stats-section" id="statsSection">
                        <div class="stats-row">
                            <div class="stat-col">
                                <span class="stats-label">New</span><span id="newCount">0</span>
                            </div>
                            <div class="stat-col">
                                <span class="stats-label">Reopen</span><span id="reopenCount">0</span>
                            </div>
                            <div class="stat-col">
                                <span class="stats-label">Ack</span><span id="ackCount">0</span>
                            </div>
                            <div class="stat-col">
                                <span class="stats-label">Skipped</span><span id="skippedCount">0</span>
                            </div>
                            <div class="stat-col">
                                <span class="stats-label">Restarts</span><span id="restartCount">0</span>
                            </div>
                        </div>
                    </div>
                   
                    <div class="container">
                        <div class="logs-container" id="logs">Loading logs...</div>
                   
                        <div class="updates-panel" id="updatesPanel">
                            <div class="updates-header">
                                <span>📊 QUEUE UPDATES</span>
                                <button class="close-panel-btn" onclick="toggleUpdates()">❌</button>
                            </div>
                            <div class="queue-tables" id="queueTables">
                            </div>
                            <div class="updates-header" style="margin-top: 15px; border-bottom-color: #ff88ff; color: #ff88ff;">
                                <span>📜 RECENT ACTIONS</span>
                            </div>
                            <div id="historyContainer">
                                <div style="text-align:center; color:#555; padding:10px;">No updates yet</div>
                            </div>
                        </div>
                   
                        <div class="cli-panel" id="cliPanel">
                            <div class="cli-header">
                                <span>📱 TICKET ACTION</span>
                                <button class="close-panel-btn" onclick="toggleCLI()">❌</button>
                            </div>
                            <div class="cli-content" id="cliContent">
                                <div class="cli-msg">⏳ Waiting for ticket...</div>
                            </div>
                            <div class="cli-input">
                                <div class="input-group" id="assigneeContainer">
                                    <select id="assigneeSelect">
                                        <option value="">Select Assignee...</option>
                                    </select>
                                </div>
                                <div class="input-group">
                                    <select id="stateSelect">
                                        <option value="">Select State...</option>
                                        <option value="1">Work in Progress (4)</option>
                                        <option value="2">Pending Tasks (22)</option>
                                        <option value="3">Pending Vendor (21)</option>
                                        <option value="4">Pending User (18)</option>
                                        <option value="5">Pending Change (19)</option>
                                    </select>
                                </div>
                                <textarea id="workNotesInput" placeholder="📝 Work Notes..."></textarea>
                                <div class="input-group">
                                    <button onclick="submitInput()">✅ Submit</button>
                                    <button onclick="skipInput()" style="background: #ff6b6b;">⏭️ Skip</button>
                                    <button onclick="cancelTicket()" style="background: #ff4444; flex: 1;">🚫 Cancel</button>
                                </div>
                            </div>
                        </div>
                    </div>
                   
                    <div style="text-align: center; padding: 6px; background: #0a0e27; border-top: 1px solid #00ff88; font-size: 9px; color: #00ff88; flex-shrink: 0;">
                        👨‍💻 Mahesh Gorla @ ServiceNow | v2.3
                    </div>
                   
                    <script>
                        let lastContent = "";
                        let autoScrollEnabled = true;
                        let soundEnabled = true;
                        let scrapEnabled = false;
                       
                        function colorize(text) {
                            if (text.includes('❌') || text.includes('Error') || text.includes('Failed')) {
                                return `<span class="error">${escapeHtml(text)}</span>`;
                            }
                            if (text.includes('✅') || text.includes('Successful')) {
                                return `<span class="success">${escapeHtml(text)}</span>`;
                            }
                            if (text.includes('⚠️') || text.includes('Warning')) {
                                return `<span class="warning">${escapeHtml(text)}</span>`;
                            }
                            if (text.includes('🚨') || text.includes('ACTION REQUIRED') || text.includes('AUTO-ACTION')) {
                                return `<span class="action">${escapeHtml(text)}</span>`;
                            }
                            return `<span class="info">${escapeHtml(text)}</span>`;
                        }
                       
                        function escapeHtml(text) {
                            const div = document.createElement('div');
                            div.textContent = text;
                            return div.innerHTML;
                        }
                       
                        function manualRefresh() {
                            fetchLogs(true);
                            fetchCLIStatus();
                            fetchStats();
                        }
                       
                        function toggleCLI() {
                            const panel = document.getElementById('cliPanel');
                            const other = document.getElementById('updatesPanel');
                            // Ensure CLI is on top
                            if (other.classList.contains('open')) {
                                other.style.zIndex = '998';
                            }
                            panel.style.zIndex = '999';
                            panel.classList.toggle('open');
                        }
                       
                        function toggleUpdates() {
                            const panel = document.getElementById('updatesPanel');
                            const other = document.getElementById('cliPanel');
                            // Ensure Updates is on top
                            if (other.classList.contains('open')) {
                                other.style.zIndex = '998';
                            }
                            panel.style.zIndex = '999';
                            panel.classList.toggle('open');
                        }
                       
                        function toggleSound() {
                            soundEnabled = !soundEnabled;
                            fetch('/api/toggle-sound', {
                                method: 'POST',
                                headers: {'Content-Type': 'application/json'},
                                body: JSON.stringify({enabled: soundEnabled})
                            });
                            updateSoundButton();
                        }
                       
                        function updateSoundButton() {
                            const btn = document.getElementById('soundToggle');
                            btn.textContent = `🔊 Sound: ${soundEnabled ? 'On' : 'Off'}`;
                            if (soundEnabled) {
                                btn.classList.remove('off');
                            } else {
                                btn.classList.add('off');
                            }
                        }
                       
                        function toggleScrap() {
                            scrapEnabled = !scrapEnabled;
                            fetch('/api/toggle-scrap', {
                                method: 'POST',
                                headers: {'Content-Type': 'application/json'},
                                body: JSON.stringify({enabled: scrapEnabled})
                            });
                            updateScrapButton();
                        }
                       
                        function updateScrapButton() {
                            const btn = document.getElementById('scrapToggle');
                            btn.textContent = `📄 Scrap: ${scrapEnabled ? 'On' : 'Off'}`;
                            if (scrapEnabled) {
                                btn.classList.remove('off');
                            } else {
                                btn.classList.add('off');
                            }
                        }
                        // ⚡ ALARM FUNCTIONS
                        function toggleAlarmMenu() {
                            document.getElementById("alarmDropdown").classList.toggle("show");
                        }
                        // Close the dropdown if the user clicks outside of it
                        window.onclick = function(event) {
                            if (!event.target.matches('.alarm-dropdown-btn')) {
                                var dropdowns = document.getElementsByClassName("alarm-dropdown-content");
                                var i;
                                for (i = 0; i < dropdowns.length; i++) {
                                    var openDropdown = dropdowns[i];
                                    if (openDropdown.classList.contains('show')) {
                                        openDropdown.classList.remove('show');
                                    }
                                }
                            }
                        }
                        function toggleAlarm() {
                            // Toggle state locally first for UI feedback, but fetch updates state
                            fetch('/api/toggle-alarm', {method: 'POST'})
                                .then(r => r.json())
                                .then(data => {
                                    updateAlarmUI(data.enabled, data.interval);
                                });
                        }
                        function setAlarmInterval(mins) {
                            fetch('/api/set-alarm-interval', {
                                method: 'POST',
                                headers: {'Content-Type': 'application/json'},
                                body: JSON.stringify({minutes: mins})
                            }).then(r => r.json()).then(data => {
                                updateAlarmUI(data.enabled, data.interval);
                                // Ensure alarm is turned on when interval selected
                                if(!data.enabled) toggleAlarm();
                            });
                        }
                        function setCustomAlarm() {
                            let mins = prompt("Enter custom alarm interval (minutes):", "20");
                            if (mins != null && parseInt(mins) > 0) {
                                setAlarmInterval(parseInt(mins));
                            }
                        }
                        function updateAlarmUI(enabled, interval) {
                            const wrapper = document.getElementById('alarmWrapper');
                            const statusSpan = document.getElementById('alarmStatus');
                            const intervalSpan = document.getElementById('alarmInterval');
                           
                            intervalSpan.innerText = interval;
                           
                            if (enabled) {
                                wrapper.classList.add('on');
                                statusSpan.innerText = "ON";
                                statusSpan.style.color = "#00ff88";
                            } else {
                                wrapper.classList.remove('on');
                                statusSpan.innerText = "OFF";
                                statusSpan.style.color = "#ff6b6b";
                            }
                        }
                       
                        function stopScript() {
                            if (confirm('Stop the entire script?')) {
                                fetch('/api/stop-script', {method: 'POST'}).then(() => {
                                    alert('Stop signal sent. Script will stop soon.');
                                });
                            }
                        }
                        // ⚡ NEW RESTART FUNCTION
                        function restartSession() {
                            if (confirm('Restart the Browser Session? (This will close and reopen Chrome)')) {
                                fetch('/api/restart-session', {method: 'POST'}).then(() => {
                                    alert('Restart signal sent. Browser will reset momentarily.');
                                });
                            }
                        }
                       
                        function cancelTicket() {
                            if (confirm('Cancel current ticket processing?')) {
                                fetch('/api/cancel-ticket', {method: 'POST'}).then(() => {
                                    alert('Current ticket cancelled.');
                                    fetchCLIStatus();
                                });
                            }
                        }
                       
                        function fetchLogs(forceUpdate = false) {
                            fetch('/api/logs?t=' + Date.now())
                                .then(r => r.json())
                                .then(data => {
                                    document.getElementById('status').innerText = '✅ Connected';
                                    document.getElementById('status').style.color = '#00ff88';
                                   
                                    const container = document.getElementById('logs');
                                    const newContent = data.logs;
                                   
                                    if (newContent !== lastContent || forceUpdate) {
                                        const lines = newContent.split('\\n').filter(l => l.trim());
                                       
                                        container.innerHTML = lines.map((line) => {
                                            return `<div class="log-line">${colorize(line)}</div>`;
                                        }).join('');
                                        lastContent = newContent;
                                       
                                        if (autoScrollEnabled) {
                                            setTimeout(() => {
                                                container.scrollTop = container.scrollHeight;
                                            }, 50);
                                        }
                                    }
                                })
                                .catch(err => {
                                    document.getElementById('status').innerText = '❌ Disconnected';
                                    document.getElementById('status').style.color = '#ff4444';
                                });
                        }
                       
                        function fetchCLIStatus() {
                            fetch('/api/cli-status?t=' + Date.now())
                                .then(r => r.json())
                                .then(data => {
                                    const cliPanel = document.getElementById('cliPanel');
                                    const cliContent = document.getElementById('cliContent');
                                    const assigneeContainer = document.getElementById('assigneeContainer'); // ⚡ Get container
                                    const assigneeSelect = document.getElementById('assigneeSelect');
                                   
                                    // ⚡ ALWAYS POPULATE USERS IF DATA EXISTS AND LIST IS EMPTY
                                    if (data.shift_users.length > 0 && assigneeSelect.options.length <= 1) {
                                         assigneeSelect.innerHTML = '<option value="">Select Assignee...</option>';
                                         data.shift_users.forEach((user, idx) => {
                                             assigneeSelect.innerHTML += `<option value="${idx+1}">${user}</option>`;
                                         });
                                    }
                                    if (data.waiting_for_input) {
                                        // ⚡ TOGGLE VISIBILITY BASED ON TICKET TYPE
                                        if (data.ticket_type === 'ASSIGNED') {
                                            assigneeContainer.style.display = 'none';
                                        } else {
                                            assigneeContainer.style.display = 'flex';
                                        }
                                       
                                        // 🟢 POPULATE CONTENT (ALWAYS, regardless of open state)
                                        cliContent.innerHTML = `<div class="cli-msg">🎫 <b>${data.ticket}</b></div>
                                            <div class="cli-msg">📋 ${data.desc}</div>
                                            <div class="cli-msg">📌 ${data.ticket_type}</div>`;
                                            // ⚡ REMOVED: Auto-open logic - Panels stay in user-chosen state
                                    } else {
                                        // Reset fields and content when no ticket (but DO NOT auto-close panel)
                                        document.getElementById('assigneeSelect').value = '';
                                        document.getElementById('stateSelect').value = '';
                                        document.getElementById('workNotesInput').value = '';
                                        cliContent.innerHTML = '<div class="cli-msg">⏳ Waiting for ticket...</div>';
                                        assigneeContainer.style.display = 'flex';
                                        // ⚡ REMOVED: cliPanel.classList.remove('open'); - Panel now stays in user-chosen state
                                    }
                                })
                                .catch(err => {
                                    console.error('CLI status error:', err);
                                });
                        }
                       
                        function fetchStats() {
                            fetch('/api/stats?t=' + Date.now())
                                .then(r => r.json())
                                .then(data => {
                                    // Update cycle count
                                    document.getElementById('cycleCount').innerText = data.cycle_count;
                                   
                                    // Update stats counts
                                    document.getElementById('newCount').innerText = data.new_count;
                                    document.getElementById('reopenCount').innerText = data.reopen_count;
                                    document.getElementById('ackCount').innerText = data.ack_count;
                                    document.getElementById('skippedCount').innerText = data.skipped_count;
                                    document.getElementById('restartCount').innerText = data.restart_count; // ⚡ UPDATE RESTART COUNT
                                   
                                    // Update sound enabled
                                    soundEnabled = data.sound_enabled;
                                    updateSoundButton();
                                   
                                    // Update scrap enabled
                                    scrapEnabled = data.scrap_enabled;
                                    updateScrapButton();
                                    // Update Alarm UI state from backend
                                    updateAlarmUI(data.alarm_enabled, data.alarm_interval);
                                   
                                    // Update queue tables
                                    const queueTables = document.getElementById('queueTables');
                                    queueTables.innerHTML = '';
                                   
                                    // INC (N)
                                    let incNTable = '<div class="queue-table"><div class="queue-header"><span class="type-header">INC (N)</span><span class="header-cell">L2/L3</span><span class="header-cell">FW</span><span class="header-cell">AK</span><span class="header-cell">SS</span></div><div class="queue-row"><span class="empty-cell"></span><span class="queue-count">' + data.queue_counts.inc_n_l2l3 + '</span><span class="queue-count">' + data.queue_counts.inc_n_fw + '</span><span class="queue-count">' + data.queue_counts.inc_n_akamai + '</span><span class="queue-count">' + data.queue_counts.inc_n_sase + '</span></div></div>';
                                    queueTables.innerHTML += incNTable;
                                   
                                    // INC (W)
                                    let incWTable = '<div class="queue-table"><div class="queue-header"><span class="type-header">INC (W)</span><span class="header-cell">FW</span><span class="header-cell">AK</span><span class="header-cell">SS</span></div><div class="queue-row"><span class="empty-cell"></span><span class="queue-count">' + data.queue_counts.inc_w_fw + '</span><span class="queue-count">' + data.queue_counts.inc_w_akamai + '</span><span class="queue-count">' + data.queue_counts.inc_w_sase + '</span></div></div>';
                                    queueTables.innerHTML += incWTable;
                                   
                                    // RITM (N)
                                    let ritmNTable = '<div class="queue-table"><div class="queue-header"><span class="type-header">RITM (N)</span><span class="header-cell">OPS</span><span class="header-cell">L2/L3</span><span class="header-cell">FW</span><span class="header-cell">AK</span><span class="header-cell">IAP</span></div><div class="queue-row"><span class="empty-cell"></span><span class="queue-count">' + data.queue_counts.ritm_n_ops + '</span><span class="queue-count">' + data.queue_counts.ritm_n_l2l3 + '</span><span class="queue-count">' + data.queue_counts.ritm_n_fw + '</span><span class="queue-count">' + data.queue_counts.ritm_n_akamai + '</span><span class="queue-count">' + data.queue_counts.ritm_n_iap + '</span></div></div>';
                                    queueTables.innerHTML += ritmNTable;
                                   
                                    // RITM (W)
                                    let ritmWTable = '<div class="queue-table"><div class="queue-header"><span class="type-header">RITM (W)</span><span class="header-cell">FW</span><span class="header-cell">AK</span><span class="header-cell">IAP</span></div><div class="queue-row"><span class="empty-cell"></span><span class="queue-count">' + data.queue_counts.ritm_w_fw + '</span><span class="queue-count">' + data.queue_counts.ritm_w_akamai + '</span><span class="queue-count">' + data.queue_counts.ritm_w_iap + '</span></div></div>';
                                    queueTables.innerHTML += ritmWTable;
                                    // ⚡ POPULATE HISTORY (NEW ROW-WISE CARD LAYOUT)
                                    const historyContainer = document.getElementById('historyContainer');
                                    if (data.history && data.history.length > 0) {
                                        historyContainer.innerHTML = data.history.map(item => `
                                            <div class="history-card">
                                                <div class="h-ticket">${item.ticket} <span style="float:right; font-size:10px; color:#888;">${item.time}</span></div>
                                                <div class="h-desc">${item.desc}</div>
                                                <div class="h-state">State: ${item.state}</div>
                                                <div class="h-update">Update: ${item.update_info}</div>
                                            </div>
                                        `).join('');
                                    } else {
                                        historyContainer.innerHTML = '<div style="text-align:center; color:#555; padding:10px;">No updates yet</div>';
                                    }
                                })
                                .catch(err => {
                                    console.error('Stats error:', err);
                                });
                        }
                       
                        function submitInput() {
                            const assignee = document.getElementById('assigneeSelect').value;
                            const state = document.getElementById('stateSelect').value;
                            const workNotes = document.getElementById('workNotesInput').value.trim();
                           
                            // ⚡ CHECK: If wrapper is hidden (ASSIGNED), assignee can be empty
                            const isAssignedHidden = document.getElementById('assigneeContainer').style.display === 'none';
                            if ((!assignee && !isAssignedHidden) || !state) {
                                alert('Please select all required fields');
                                return;
                            }
                           
                            fetch('/api/cli-input', {
                                method: 'POST',
                                headers: {'Content-Type': 'application/json'},
                                body: JSON.stringify({assignee: assignee, state: state, work_notes: workNotes})
                            }).then(r => r.json()).then(data => {
                                // ⚡ REMOVED: Auto-close on submit - let user close manually if desired
                                setTimeout(fetchCLIStatus, 1000);
                            });
                        }
                       
                        function skipInput() {
                            fetch('/api/cli-input', {
                                method: 'POST',
                                headers: {'Content-Type': 'application/json'},
                                body: JSON.stringify({action: 'skip'})
                            }).then(r => r.json()).then(data => {
                                // ⚡ REMOVED: Auto-close on skip - let user close manually if desired
                                setTimeout(fetchCLIStatus, 1000);
                            });
                        }
                       
                        document.getElementById('autoScroll').addEventListener('change', (e) => {
                            autoScrollEnabled = e.target.checked;
                            if (autoScrollEnabled) {
                                document.getElementById('logs').scrollTop = document.getElementById('logs').scrollHeight;
                            }
                        });
                       
                        fetchLogs();
                        fetchCLIStatus();
                        fetchStats();
                        setInterval(fetchLogs, 1000);
                        setInterval(fetchCLIStatus, 2000);
                        setInterval(fetchStats, 5000);
                    </script>
            </body>
            </html>
            '''
            self.safe_write(html.encode('utf-8'))
           
        elif self.path.startswith('/api/logs'):
            self.send_response(200)
            self.send_header('Content-type', 'application/json; charset=utf-8')
            self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
            self.end_headers()
           
            logs_content = log_manager.get_all()
            response = json.dumps({"logs": logs_content})
            self.safe_write(response.encode('utf-8'))
           
        elif self.path.startswith('/api/cli-status'):
            self.send_response(200)
            self.send_header('Content-type', 'application/json; charset=utf-8')
            self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
            self.end_headers()
           
            try:
                waiting = pending_ticket_data.get('ticket_data') is not None and pending_ticket_data.get('ticket_data')
                data = {
                    'waiting_for_input': waiting,
                    'ticket': pending_ticket_data.get('ticket_data', {}).get('ticket', '') if waiting else '',
                    'desc': pending_ticket_data.get('ticket_data', {}).get('desc', '') if waiting else '',
                    'ticket_type': pending_ticket_data.get('ticket_data', {}).get('ticket_type', '') if waiting else '',
                    'shift_users': pending_ticket_data.get('shift_users', [])
                }
            except:
                data = {
                    'waiting_for_input': False,
                    'ticket': '',
                    'desc': '',
                    'ticket_type': '',
                    'shift_users': []
                }
           
            response = json.dumps(data)
            self.safe_write(response.encode('utf-8'))
           
        elif self.path.startswith('/api/stats'):
            self.send_response(200)
            self.send_header('Content-type', 'application/json; charset=utf-8')
            self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
            self.end_headers()
           
            data = {
                'cycle_count': cycle_counter,
                'new_count': new_count,
                'reopen_count': reopen_count,
                'ack_count': ack_count,
                'skipped_count': skipped_count,
                'restart_count': restart_count, # ⚡ SEND RESTART COUNT
                'sound_enabled': sound_enabled,
                'scrap_enabled': scrap_enabled,
                'queue_counts': queue_counts,
                'history': updated_tickets_history, # ⚡ Send history
                'alarm_enabled': alarm_enabled, # ⚡ ALARM STATE
                'alarm_interval': alarm_interval_minutes # ⚡ ALARM INTERVAL
            }
            response = json.dumps(data)
            self.safe_write(response.encode('utf-8'))
        else:
            self.send_response(404)
            self.end_headers()
    def do_POST(self):
        # ⚡ CRITICAL FIX: Declare all globals at the TOP of the function
        global stop_script, restart_requested, cancel_current_ticket
        global sound_enabled, scrap_enabled, scrap_toggle_requested
        global alarm_enabled, alarm_last_played, alarm_interval_minutes
        if self.path.startswith('/api/cli-input'):
            content_length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(content_length)
           
            try:
                data = json.loads(body.decode('utf-8'))
                mobile_input_queue.put(data)
               
                self.send_response(200)
                self.send_header('Content-type', 'application/json; charset=utf-8')
                self.end_headers()
                self.safe_write(json.dumps({"success": True}).encode('utf-8'))
            except:
                self.send_response(400)
                self.end_headers()
        elif self.path.startswith('/api/stop-script'):
            stop_script = True
            self.send_response(200)
            self.send_header('Content-type', 'application/json; charset=utf-8')
            self.end_headers()
            self.safe_write(json.dumps({"success": True}).encode('utf-8'))
           
        # ⚡ NEW: RESTART SESSION ENDPOINT
        elif self.path.startswith('/api/restart-session'):
            restart_requested = True
            self.send_response(200)
            self.send_header('Content-type', 'application/json; charset=utf-8')
            self.end_headers()
            self.safe_write(json.dumps({"success": True}).encode('utf-8'))
           
        elif self.path.startswith('/api/cancel-ticket'):
            cancel_current_ticket = True
            pending_ticket_data['ticket_data'] = None
            self.send_response(200)
            self.send_header('Content-type', 'application/json; charset=utf-8')
            self.end_headers()
            self.safe_write(json.dumps({"success": True}).encode('utf-8'))
           
        elif self.path.startswith('/api/toggle-sound'):
            content_length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(content_length)
           
            try:
                data = json.loads(body.decode('utf-8'))
                sound_enabled = data.get('enabled', True)
               
                self.send_response(200)
                self.send_header('Content-type', 'application/json; charset=utf-8')
                self.end_headers()
                self.safe_write(json.dumps({"success": True}).encode('utf-8'))
            except:
                self.send_response(400)
                self.end_headers()
               
        elif self.path.startswith('/api/toggle-scrap'):
            content_length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(content_length)
           
            try:
                data = json.loads(body.decode('utf-8'))
                scrap_enabled = data.get('enabled', False)
                scrap_toggle_requested = True
               
                self.send_response(200)
                self.send_header('Content-type', 'application/json; charset=utf-8')
                self.end_headers()
                self.safe_write(json.dumps({"success": True}).encode('utf-8'))
            except:
                self.send_response(400)
                self.end_headers()
        # ⚡ NEW ALARM ENDPOINTS
        elif self.path.startswith('/api/toggle-alarm'):
            alarm_enabled = not alarm_enabled
            if alarm_enabled:
                alarm_last_played = time.time() # Reset timer on enable
                log("⏰ ALARM ENABLED")
            else:
                log("⏰ ALARM DISABLED")
           
            self.send_response(200)
            self.send_header('Content-type', 'application/json; charset=utf-8')
            self.end_headers()
            self.safe_write(json.dumps({"enabled": alarm_enabled, "interval": alarm_interval_minutes}).encode('utf-8'))
        elif self.path.startswith('/api/set-alarm-interval'):
            content_length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(content_length)
            try:
                data = json.loads(body.decode('utf-8'))
                alarm_interval_minutes = int(data.get('minutes', 10))
                alarm_enabled = True # Auto enable on set
                alarm_last_played = time.time() # Reset timer
                log(f"⏰ ALARM INTERVAL SET: {alarm_interval_minutes} minutes")
               
                self.send_response(200)
                self.send_header('Content-type', 'application/json; charset=utf-8')
                self.end_headers()
                self.safe_write(json.dumps({"enabled": alarm_enabled, "interval": alarm_interval_minutes}).encode('utf-8'))
            except:
                self.send_response(400)
                self.end_headers()
        else:
            self.send_response(404)
            self.end_headers()
    def log_message(self, format, *args):
        pass # Suppress server logs
def get_local_ip():
    """Get your laptop's local IP address"""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except:
        return "localhost"
def start_web_server():
    """Start web server for mobile log viewing in background thread."""
    def run_server():
        server = HTTPServer(('0.0.0.0', WEB_SERVER_PORT), MobileLogHandler)
        ip = get_local_ip()
       
        # Also log to file for mobile viewer
        log_manager.add("")
        log_manager.add("=" * LINE_LENGTH)
        log_manager.add("📱 WEB SERVER STARTED - MOBILE LOG VIEWER + CLI CONTROL")
        log_manager.add("=" * LINE_LENGTH)
        log_manager.add(f" 👉 Local Network: http://{ip}:{WEB_SERVER_PORT}")
        log_manager.add(f" 💡 Ensure mobile & laptop are on SAME WiFi")
        log_manager.add(f" 🎮 Use Mobile CLI to control tickets remotely!")
        log_manager.add("=" * LINE_LENGTH)
        log_manager.add("")
       
        server.serve_forever()
   
    thread = threading.Thread(target=run_server, daemon=True)
    thread.start()
# ⚡ ALARM BACKGROUND CHECKER
def alarm_checker():
    """Runs in background to play alarm periodicallly"""
    global alarm_last_played
    while True:
        if alarm_enabled and not stop_script:
            elapsed = time.time() - alarm_last_played
            interval_sec = alarm_interval_minutes * 60
           
            if elapsed >= interval_sec:
                log(f"⏰ ALARM TRIGGERED ({alarm_interval_minutes}m interval)")
                play_notification() # Plays miui.mp3
                alarm_last_played = time.time()
       
        time.sleep(5) # Check every 5 seconds
# ===================================================================
# --- HELPERS ---
# ===================================================================
def print_centered_header(text, char="-"):
    """Prints a centered header starting at the beginning of the line."""
    border = char * LINE_LENGTH
    padding = (LINE_LENGTH - len(text)) // 2
    centered_text = (" " * padding) + text
    log(border)
    log(centered_text)
    log(border)
def display_cycle_stats():
    """Display cycle stats in console and log."""
    log("\n" + "-" * LINE_LENGTH)
    log(f" 📊 CYCLE STATS: New: {new_count} | Reopen : {reopen_count} | Ack: {ack_count} | Skipped: {skipped_count}")
    log("-" * LINE_LENGTH + "\n")
def display_queue_stats():
    """Display queue stats in console and log."""
    log("\n" + "-" * LINE_LENGTH)
    log("🗂️ QUEUE COUNTS:")
    log("INC (N) L2/L3 FW AK SS")
    log(f"Count {queue_counts['inc_n_l2l3']:>5} {queue_counts['inc_n_fw']:>4} {queue_counts['inc_n_akamai']:>4} {queue_counts['inc_n_sase']:>3}")
    log("INC (W) FW AK SS")
    log(f"Count {queue_counts['inc_w_fw']:>5} {queue_counts['inc_w_akamai']:>4} {queue_counts['inc_w_sase']:>3}")
    log("RITM (N) OPS L2/L3 FW AK IAP")
    log(f"Count {queue_counts['ritm_n_ops']:>5} {queue_counts['ritm_n_l2l3']:>5} {queue_counts['ritm_n_fw']:>4} {queue_counts['ritm_n_akamai']:>4} {queue_counts['ritm_n_iap']:>3}")
    log("RITM (W) FW AK IAP")
    log(f"Count {queue_counts['ritm_w_fw']:>5} {queue_counts['ritm_w_akamai']:>4} {queue_counts['ritm_w_iap']:>3}")
    log("-" * LINE_LENGTH + "\n")
def load_l2_from_file():
    """Loads previous L2 memory from file."""
    memory = {}
    if os.path.exists(REOPEN_FILE_PATH):
        try:
            with open(REOPEN_FILE_PATH, "r", encoding="utf-8") as f:
                for line in f:
                    parts = line.strip().split('|')
                    if len(parts) >= 3:
                        ticket = parts[0].strip()
                        name = parts[1].strip()
                        desc = parts[2].strip()
                        val = state_name_to_val.get(name, '4')
                        memory[ticket] = {'value': val, 'name': name}
        except: pass
    return memory
def save_l2_item_to_file(ticket, state_name, short_desc):
    """Appends a new processed ticket to the file: ticket|state_name|short_desc"""
    try:
        log_dir = os.path.dirname(REOPEN_FILE_PATH)
        if not os.path.exists(log_dir): os.makedirs(log_dir)
        clean_desc = short_desc.replace("|", "-").replace("\n", " ")
        with open(REOPEN_FILE_PATH, "a", encoding="utf-8") as f:
            f.write(f"{ticket}|{state_name}|{clean_desc}\n")
    except Exception as e:
        log(f" ⚠️ Error saving to file: {e}")
def add_history(ticket, desc, state, assignee):
    """⚡ Helper to add item to global history list safely with granular data"""
    try:
        # Determine "What was updated"
        update_info = "State Updated"
        if assignee:
            update_info = f"Assigned to {assignee}"
       
        updated_tickets_history.insert(0, {
            "ticket": ticket,
            "desc": desc,
            "state": state,
            "update_info": update_info,
            "time": time.strftime("%H:%M") # ⚡ ADDED TIME STAMP
        })
        # Keep list size manageable
        if len(updated_tickets_history) > 50:
            updated_tickets_history.pop()
    except: pass
def play_notification():
    """Plays sound for exactly 3 seconds."""
    clean_path = os.path.abspath(SOUND_PATH.strip())
    def _play():
        old_stderr = sys.stderr
        try:
            with open(os.devnull, 'w') as f:
                sys.stderr = f
                if os.path.exists(clean_path):
                    playsound(clean_path)
                else:
                    print("\a")
        except Exception as e:
            log(f" ⚠️ Sound playback error: {e}")
        finally:
            sys.stderr = old_stderr
    t = threading.Thread(target=_play)
    t.daemon = True
    t.start()
    time.sleep(3)
def play_queue_sound():
    """Plays queue update sound asynchronously."""
    clean_path = os.path.abspath(QUEUE_SOUND_PATH.strip())
    def _play():
        old_stderr = sys.stderr
        try:
            with open(os.devnull, 'w') as f:
                sys.stderr = f
                if os.path.exists(clean_path):
                    playsound(clean_path)
                else:
                    print("\a")
        except Exception as e:
            log(f" ⚠️ Queue sound playback error: {e}")
        finally:
            sys.stderr = old_stderr
    t = threading.Thread(target=_play, daemon=True)
    t.start()
    log("🔊 Queue update sound played - counts increased")
def get_shift_users():
    """Asks user for shift members at startup using predefined list."""
    users = ["Mahesh Kumar"] # Default "me"
    print_centered_header("👥 SHIFT CONFIGURATION 👥", char="-")
    print("\n 📋 Predefined Shift Users:")
    for idx, name in enumerate(SHIFT_USERS_LIST, 1):
        print(f" [{idx}] {name}")
    print(f"\n 👤 Default: Mahesh Kumar (Me)")
    try:
        selection_str = input(" 👉 Current shift with me [default]: Enter numbers (comma sep, e.g., 1,2): ").strip()
        if selection_str:
            selections = [int(s.strip()) for s in selection_str.split(',') if s.strip().isdigit()]
            for sel in selections:
                if 1 <= sel <= len(SHIFT_USERS_LIST):
                    users.append(SHIFT_USERS_LIST[sel-1])
       
        # ⚡ KEY FIX: Update the shared data immediately as users are added
        pending_ticket_data['shift_users'] = users
    except: pass
    log(f" ✅ Active Shift Users: {users}\n")
    return users
def get_input_with_timeout(prompt, timeout=60, shift_users=None):
    """
    Windows: supports keyboard + mobile
    Linux (Codespaces): mobile-only
    """
    start_time = time.time()
    # Always keep shift users synced for mobile UI
    if pending_ticket_data.get('ticket_data'):
        pending_ticket_data['shift_users'] = shift_users or []
    if not IS_WINDOWS:
        # 🔵 Codespaces/Linux: NO keyboard input
        while True:
            try:
                return mobile_input_queue.get(timeout=timeout)
            except queue.Empty:
                log(" ⌛ Timeout! Skipping ticket.")
                return "S"
    # 🟢 Windows logic (original behavior)
    input_chars = []
    while msvcrt.kbhit():
        msvcrt.getch()
    print("")
    while True:
        elapsed = time.time() - start_time
        remaining = int(timeout - elapsed)
        try:
            mobile_input = mobile_input_queue.get_nowait()
            return mobile_input
        except queue.Empty:
            pass
        sys.stdout.write(f"\r Clock: [{remaining:02d}s] {prompt} {''.join(input_chars)} ")
        sys.stdout.flush()
        if remaining <= 0:
            log(" ⌛ Timeout! Skipping ticket.")
            return "S"
        if msvcrt.kbhit():
            char = msvcrt.getwch()
            if char in ('\r', '\n'):
                print("")
                return "".join(input_chars)
            elif char == '\b':
                if input_chars:
                    input_chars.pop()
            else:
                input_chars.append(char)
        time.sleep(0.05)
# ===================================================================
# --- BROWSER INITIALIZATION (HEADLESS) ---
# ===================================================================
def initialize_driver():
    log("🚀 Launching Chrome (Headless Mode)")
    opts = Options()
    opts.add_argument("--headless=new")
    opts.add_argument("--window-size=1920,1080")
    opts.add_argument("--disable-gpu")
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument("--silent")
    opts.add_argument("--log-level=3")
    opts.add_experimental_option("excludeSwitches", ["enable-automation", "enable-logging"])
    old_stderr = sys.stderr
    try:
        with open(os.devnull, 'w') as f:
            sys.stderr = f
            driver = webdriver.Chrome(options=opts)
    finally:
        sys.stderr = old_stderr
    wait = WebDriverWait(driver, 20)
    log("🔐 Logging in (Background)")
    driver.get(LOGIN_URL)
    try:
        try:
            wait.until(EC.element_to_be_clickable((By.ID, "btnSetPopup"))).click()
            time.sleep(2)
        except:
            pass
        time.sleep(2)
        wait.until(EC.element_to_be_clickable((By.ID, "corporateOpener"))).click()
        time.sleep(2)
        wait.until(EC.element_to_be_clickable((By.ID, "UsernameInputTxtCorporate"))).send_keys(USER)
        time.sleep(1)
        driver.find_element(By.ID, "PasswordInputCorporate").send_keys(PASSWORD)
        time.sleep(1)
        driver.find_element(By.ID, "btnLoginCorporate").click()
        time.sleep(2)
        wait.until(EC.url_contains("$pa_dashboard.do"))
        log("✅ Logged in successfully.")
    except Exception as e:
        log(f"❌ Login Failed. Error: {e}")
        try: driver.quit()
        except: pass
        exit()
    return driver, wait
# ===================================================================
# --- SCRAPER FOR COUNTS ---
# ===================================================================
def scrape_queue_count(driver, wait, url, queue_key):
    """Scrape the count of tickets from the given ServiceNow list URL."""
    if not url or url.strip() == "":
        return 0
    try:
        driver.get(url)
        # Wait for the table body
        try:
            wait.until(EC.presence_of_element_located((By.CLASS_NAME, "list2_body")))
        except:
            # If list2_body never appears, it might be an empty page or error
            return 0
        rows = driver.find_elements(By.CSS_SELECTOR, ".list2_body tr")
       
        # ⚡ FIX: Check if the only row is "No records to display"
        if len(rows) == 1:
            text = rows[0].text.lower()
            if "no records to display" in text:
                log(f"📊 Queue '{queue_key}' scraped: 0 tickets (Empty)")
                return 0
       
        count = len(rows)
        log(f"📊 Queue '{queue_key}' scraped: {count} tickets")
        return count
    except Exception as e:
        log(f" ⚠️ Error scraping queue '{queue_key}': {e}")
        return 0
# ===================================================================
# --- SCRAPE LAST STATE FROM NOTES (UPDATED LOGIC) ---
# ===================================================================
# Defined valid states to prevent grabbing garbage text
VALID_STATES = [
    "new", "work in progress", "in progress", "active",
    "pending tasks", "pending vendor", "pending user", "pending change",
    "resolved", "closed", "on hold"
]
def scrape_last_state(driver, wait):
    """
    Scrape history, looking back up to 6 'State' changes to find a non-New/Resolved state.
    Returns:
       - A valid state name (e.g., 'Pending Tasks') if found.
       - None if only 'New' or 'Resolved' are found in the last 6 entries.
    """
    print(" 🔍 Scrapping notes for state history (Depth: 6)...")
    try:
        # Click on Notes tab
        try:
            notes_tab_xpath = "//span[contains(text(), 'Notes') and contains(@class, 'tab_caption_text')]"
            notes_tab = wait.until(EC.element_to_be_clickable((By.XPATH, notes_tab_xpath)))
            driver.execute_script("arguments[0].click();", notes_tab)
            time.sleep(2) # Wait for AJAX load
        except Exception as e:
            log(f" ⚠️ Error clicking Notes tab: {e}")
        # Find all Activity Items (history)
        try:
            activity_items = driver.find_elements(By.CSS_SELECTOR, "li.h-card, li.activity-stream-item, div.sn-widget-list-item")
           
            history_found_count = 0
            limit = 10
           
            for item in activity_items:
                text_content = item.text.replace("\n", " | ")
               
                if "Field changes" in text_content or "State" in text_content:
                    match = re.search(r'State\s*(.*?)\s*was\s*(.*)', text_content, re.IGNORECASE)
                    if match:
                        current_state = match.group(1).strip().replace("|", "").strip()
                        old_state = match.group(2).strip()
                       
                        # Clean up old_state
                        if "|" in old_state: old_state = old_state.split("|")[0].strip()
                       
                        # ⚡ FIX: Strict validation against known states to filter out garbage text
                        is_valid_state = False
                        clean_state_lower = old_state.lower()
                       
                        # Check against allowed list
                        for vs in VALID_STATES:
                            if vs in clean_state_lower:
                                is_valid_state = True
                                # Normalize the string (e.g., "ResolvedwasPending Tasks" -> "Pending Tasks")
                                if vs == "pending tasks" and "pending tasks" in clean_state_lower:
                                    old_state = "Pending Tasks"
                                elif vs == "pending vendor" and "pending vendor" in clean_state_lower:
                                    old_state = "Pending Vendor"
                                elif vs == "pending user" and "pending user" in clean_state_lower:
                                    old_state = "Pending User"
                                elif vs == "pending change" and "pending change" in clean_state_lower:
                                    old_state = "Pending Change"
                                elif vs == "work in progress" and "work in progress" in clean_state_lower:
                                    old_state = "Work in Progress"
                                break
                       
                        if not is_valid_state:
                            # It grabbed garbage text (like the IP address in your log)
                            continue
                        history_found_count += 1
                       
                        # ⚡ FILTER LOGIC: Skip New/Resolved, but count them towards the limit
                        if "new" in clean_state_lower or "resolved" in clean_state_lower:
                            log(f" 👉 [History {history_found_count}] Found '{old_state}' (Skipping: New/Resolved)")
                            if history_found_count >= limit:
                                log(" ⚠️ History depth limit reached. Defaulting to WIP.")
                                return None
                            continue # Look further back
                       
                        # If we are here, it's a meaningful state
                        log(f" 🎯 Scraped History: State was '{old_state}'")
                        return old_state
        except Exception as e:
            log(f" ⚠️ Error iterating activity items: {e}")
        return None
    except Exception as e:
        log(f"⚠️ Error scraping last state from notes: {e}")
        return None
# ===================================================================
# --- TAB 1: SCRAPER ---
# ===================================================================
def scrape_l1_incidents_detailed(driver, wait):
    driver.switch_to.window(driver.window_handles[0])
    driver.get(URL_NEW_STATE_LIST)
    scraped_tickets = []
    try:
        try: wait.until(EC.presence_of_element_located((By.CLASS_NAME, "list2_body")))
        except: return []
        headers = driver.find_elements(By.XPATH, "//table//thead//th")
        col_map = {"Number": -1, "Short description": -1, "Reopen count": -1, "Assigned to": -1}
        for i, h in enumerate(headers):
            txt = h.text.strip().lower()
            if "number" in txt: col_map["Number"] = i
            elif "short description" in txt: col_map["Short description"] = i
            elif "reopen count" in txt: col_map["Reopen count"] = i
            elif "assigned to" in txt: col_map["Assigned to"] = i
        if col_map["Number"] == -1: return []
        rows = driver.find_elements(By.CSS_SELECTOR, ".list2_body tr")
        for row in rows:
            try:
                cells = row.find_elements(By.TAG_NAME, "td")
                t_num = cells[col_map["Number"]].text.strip() if len(cells) > col_map["Number"] else ""
                if not t_num.startswith("INC"): continue
                short_desc = "No Description"
                if col_map["Short description"] != -1 and len(cells) > col_map["Short description"]:
                    short_desc = cells[col_map["Short description"]].text.strip()
               
                assigned_to = ""
                if col_map["Assigned to"] != -1 and len(cells) > col_map["Assigned to"]:
                    assigned_to = cells[col_map["Assigned to"]].text.strip()
                reopen_count = 0
                if col_map["Reopen count"] != -1 and len(cells) > col_map["Reopen count"]:
                    try: reopen_count = int(cells[col_map["Reopen count"]].text.strip())
                    except: reopen_count = 0
                scraped_tickets.append({
                    "ticket": t_num, "desc": short_desc,
                    "assigned": assigned_to, "reopen": reopen_count
                })
            except: pass
    except Exception as e:
        if "stale element" not in str(e).lower():
            log(f" ⚠️ Error scraping L1: {e}")
       
    seen = set()
    unique = []
    for item in scraped_tickets:
        if item['ticket'] not in seen:
            unique.append(item)
            seen.add(item['ticket'])
       
    return unique
# ===================================================================
# --- TAB 2: PROCESSOR ---
# ===================================================================
def process_ticket_in_tab2(driver, wait, ticket_data, l2_memory, shift_users, skip_memory):
    global new_count, reopen_count, ack_count, skipped_count, cancel_current_ticket
    ticket = ticket_data['ticket']
    short_desc = ticket_data['desc']
    assigned_to_val = ticket_data['assigned']
    reopen_count_val = ticket_data['reopen'] # Renamed to avoid conflict
    DIVIDER_STR = "-" * LINE_LENGTH
    EQUAL_STR = "=" * LINE_LENGTH
    val_map = {'1': '4', '2': '22', '3': '21', '4': '18', '5': '19'}
    name_map = {'1': 'Work in Progress', '2': 'Pending Tasks', '3': 'Pending Vendor', '4': 'Pending User', '5': 'Pending Change'}
    # --- 1. FAST CHECKS (Only if scrap not enabled) ---
    if ticket in l2_memory and not scrap_enabled:
        mem = l2_memory[ticket]
        log(DIVIDER_STR)
        log(f" 🔄 Fast-Processing: {ticket} - {short_desc}")
        log(f" 🧠 Found in L2 Memory! Opening to auto-update: {mem['name']}")
        # ⚡ FIX: Use the remembered assignee from memory
        open_and_update(driver, wait, ticket, mem['value'], mem['name'], assignee=None)
       
        # ⚡ FIX: Increment counters for Fast Processing as well
        reopen_count += 1
        ack_count += 1
        log(DIVIDER_STR + "\n")
        # ⚡ ADD HISTORY
        add_history(ticket, short_desc, mem['name'], assignee=None)
        return None
    # --- 2. LOGIC CHECK ---
    needs_attention = False
    reason = ""
    ticket_type = ""
    # ⚡ CRITICAL FIX: If Scrap Mode is enabled, force processing regardless of reopen count
    # This ensures we enter the Scrap block even if the L1 list says reopen count is 0
    if scrap_enabled:
        needs_attention = True
        ticket_type = "ASSIGNED" # Force assignment type to hit scrap logic
        reason = "Scrap Mode Active - Force Process"
    elif not assigned_to_val or "(empty)" in assigned_to_val:
        needs_attention = True
        reason = "Assigned To is Empty"
        ticket_type = "UNASSIGNED"
    elif reopen_count_val > 0:
        needs_attention = True
        reason = f"Reopen Count is {reopen_count_val}"
        ticket_type = "ASSIGNED"
    if not needs_attention:
        return None
    # Update counters
    if ticket_type == "UNASSIGNED":
        new_count += 1
    if reopen_count_val > 2:
        reopen_count += 1
    # --- 3. OPEN PAGE (Background) ---
    if len(driver.window_handles) < 2: driver.execute_script("window.open('');")
    driver.switch_to.window(driver.window_handles[1])
    url = f"{BASE_URL}/incident.do?sysparm_query=number={ticket}"
    driver.get(url)
    try:
        try: wait.until(EC.frame_to_be_available_and_switch_to_it((By.ID, "gsft_main")))
        except: pass
        wait.until(EC.presence_of_element_located((By.ID, "sys_readonly.incident.number")))
       
        if short_desc == "No Description" or not short_desc:
            try: short_desc = driver.find_element(By.ID, "incident.short_description").get_attribute("value")
            except: pass
           
        state_el = driver.find_element(By.ID, "incident.state")
        current_state = state_el.get_attribute("value")
        if current_state in ['6', '7', '8']:
            log(" ⏭️ Ticket Closed. Skipping.")
            return None
        # --- ⚡ SCRAP MODE TRIGGER FOR REOPENED TICKETS ---
        if scrap_enabled and ticket_type == "ASSIGNED":
            # ⚡ SPECIFIC LOG FORMAT
            log("SCRAP MODE : ON")
            log("-" * 60)
            log(f" 🔄 Scrapping : {ticket}")
           
            last_state_name = scrape_last_state(driver, wait)
           
            if last_state_name:
                log(f" 🧠 Found previous updated-state: {last_state_name}")
                if last_state_name in ['New', 'Resolved']:
                    target_val = '4'
                    state_name = 'Work in Progress'
                else:
                    target_val = state_name_to_val.get(last_state_name, '4')
                    state_name = last_state_name
               
                log(f" 📝 Setting State: {state_name} ({target_val})")
                log(" Clicking Save...")
                # ⚡ UPDATE SILENTLY (so we control logs here)
                update_logic(driver, state_el, target_val, state_name, assignee=None, silent=True)
               
                log(" ✅ Update Successful.")
                log("-" * 60)
               
                result = {'value': target_val, 'name': state_name, 'assignee': assigned_to_val}
                l2_memory[ticket] = result
                save_l2_item_to_file(ticket, state_name, short_desc)
                ack_count += 1
                pending_ticket_data['ticket_data'] = None
               
                # ⚡ ADD HISTORY
                add_history(ticket, short_desc, state_name, assignee=None)
                return result
            else:
                log(" ⚠️ Scrap failed or limited to New/Resolved. Defaulting to Work in Progress.")
                log("-" * 60)
                target_val = '4'
                state_name = 'Work in Progress'
                log(f" 📝 Setting State: {state_name} ({target_val})")
                log(" Clicking Save...")
                update_logic(driver, state_el, target_val, state_name, assignee=None, silent=True)
                log(" ✅ Update Successful.")
                log("-" * 60)
               
                result = {'value': target_val, 'name': state_name, 'assignee': assigned_to_val}
                l2_memory[ticket] = result
                save_l2_item_to_file(ticket, state_name, short_desc)
                ack_count += 1
                pending_ticket_data['ticket_data'] = None
               
                # ⚡ ADD HISTORY
                add_history(ticket, short_desc, state_name, assignee=None)
                return result
        # --- ALERT USER (Pretty Output) ---
        log("\n" + EQUAL_STR)
        log(f" 🚨 ACTION REQUIRED: {ticket}")
        log(f" 📄 Desc: {short_desc}")
        log(f" ⚠️ Reason: {reason}")
        log(f" 📌 Type: {ticket_type}")
        log(EQUAL_STR)
       
        # Check for cancel
        if cancel_current_ticket:
            log(" 🚫 Current ticket cancelled by user.")
            cancel_current_ticket = False
            pending_ticket_data['ticket_data'] = None
            return None
        # --- AUTO-ASSIGN CHECK (UNASSIGNED TICKETS - SKIP LIMIT) ---
        if ticket_type == "UNASSIGNED" and skip_memory.get(ticket, 0) >= MAX_UNASSIGN_SKIP_COUNT:
            log(f" 🤖 AUTO-ACTION: Unassigned Ticket skipped {skip_memory.get(ticket)} times.")
            log(f" 👤 Assigning to Default: {shift_users[0]}")
            log(f" ⚙️ Setting State to: {name_map['1']}")
           
            target_val = '4'
            state_name = name_map['1']
            selected_assignee = shift_users[0]
           
            update_logic(driver, state_el, target_val, state_name, assignee=selected_assignee)
            ack_count += 1 # Acknowledge
           
            if ticket in skip_memory: del skip_memory[ticket]
            # ⚡ ADD HISTORY
            add_history(ticket, short_desc, state_name, assignee=selected_assignee)
            return {'value': target_val, 'name': state_name, 'assignee': selected_assignee}
        # --- AUTO-ACKNOWLEDGE CHECK (ASSIGNED TICKETS - SKIP LIMIT) ---
        if ticket_type == "ASSIGNED" and assigned_to_val and "(empty)" not in assigned_to_val:
            if skip_memory.get(ticket, 0) >= MAX_ASSIGN_SKIP_COUNT:
                log(f" 🤖 AUTO-ACTION: Assigned Ticket (Reopen) skipped {skip_memory.get(ticket)} times.")
                log(f" 👤 Currently Assigned to: {assigned_to_val}")
                log(f" ⚙️ Setting State to: {name_map['1']} (Acknowledgement)")
               
                target_val = '4'
                state_name = name_map['1']
               
                update_logic(driver, state_el, target_val, state_name, assignee=None)
                ack_count += 1 # Acknowledge
               
                if ticket in skip_memory: del skip_memory[ticket]
                # ⚡ ADD HISTORY
                add_history(ticket, short_desc, state_name, assignee=None)
                return {'value': target_val, 'name': state_name, 'assignee': assigned_to_val}
       
        play_notification()
        # --- 4. SET UP MOBILE CLI ---
        pending_ticket_data['ticket_data'] = {
            'ticket': ticket,
            'desc': short_desc,
            'ticket_type': ticket_type,
            'assigned_to': assigned_to_val
        }
        pending_ticket_data['shift_users'] = shift_users
        # --- 5. INTERACTION LOGIC (CONSOLIDATED) ---
        selected_assignee = None
        target_val = None
        state_name = None
        work_notes_text = ""
        # ⚡ LOGIC SPLIT: Assigned tickets don't need Assignee prompts in console
        if ticket_type == "UNASSIGNED":
            # Print the Prompt
            print("\n 👤 Need Assignee:")
            for idx, user in enumerate(shift_users):
                print(f" [{idx+1}] {user}")
            print(" [S] Skip")
            print(" 📱 Or use Mobile CLI to select")
           
            # Wait for input (Supports Mobile Bulk or Console Step-by-Step)
            # Only ask for assignee here
            user_input = get_input_with_timeout(f"👉 Select Assignee (1-{len(shift_users)}) or [S]kip: ", timeout=60, shift_users=shift_users)
        else:
            # For ASSIGNED tickets, skip the prompt but still check for mobile input silently
            print(f"\n Select State for {ticket}:")
            print(" [1] Work in Progress (4)")
            print(" [2] Pending Tasks (22)")
            print(" [3] Pending Vendor (21)")
            print(" [4] Pending User (18)")
            print(" [5] Pending Change (19)")
            print(" [S] Skip")
            print(" 📱 Or use Mobile CLI to select")
            user_input = get_input_with_timeout("👉 Select State (1-5) or [S]kip: ", timeout=60, shift_users=shift_users)
        # --- PATH A: MOBILE INPUT (One-Shot Dictionary) ---
        if isinstance(user_input, dict):
            if user_input.get('action') == 'skip':
                log(" ⏭️ Skipped (Mobile). Skipping ticket.")
                skipped_count += 1
                pending_ticket_data['ticket_data'] = None
                return None
           
            # Extract Mobile Data
            try:
                # 1. Assignee Logic
                if ticket_type == 'ASSIGNED':
                    # ⚡ LOGIC FIX: If ticket is assigned, don't change assignee unless forced.
                    # Mobile hides the dropdown, so 'assignee' will be empty or 0.
                    selected_assignee = None
                else:
                    u_choice = int(user_input.get('assignee', 0))
                    if 1 <= u_choice <= len(shift_users):
                        selected_assignee = shift_users[u_choice-1]
               
                # 2. State
                s_choice = str(user_input.get('state', ''))
                if s_choice in val_map:
                    target_val = val_map[s_choice]
                    state_name = name_map[s_choice]
               
                # 3. Work Notes
                work_notes_text = user_input.get('work_notes', '')
                # 4. Print Summary as requested
                # ⚡ ADDED: New line before summary
                print("")
                log(f" ✅ Selected for {ticket} (Mobile):")
                if selected_assignee:
                    log(f" 👉 Selected Assignee Name : {selected_assignee}")
                elif ticket_type == "ASSIGNED":
                    log(f" 👉 Selected Assignee Name : (No Change / Existing)")
                log(f" 👉 Selected State : {state_name}")
               
            except Exception as e:
                log(f" ❌ Error parsing mobile input: {e}")
                return None
        # --- PATH B: CONSOLE INPUT (Step-by-Step String) ---
        else:
            # 1. Process Assignee (Only if Unassigned)
            if ticket_type == "UNASSIGNED":
                if user_input.strip().upper() == 'S':
                    log(" ⏭️ Skipped assignment. Skipping ticket.")
                    skipped_count += 1
                    current_count = skip_memory.get(ticket, 0) + 1
                    skip_memory[ticket] = current_count
                    pending_ticket_data['ticket_data'] = None
                    return None
               
                try:
                    u_choice = int(user_input.strip())
                    if 1 <= u_choice <= len(shift_users):
                        selected_assignee = shift_users[u_choice-1]
                        # log(f" ✅ Selected: {selected_assignee}") # Removed intermediate log
                except:
                    pass
           
            # 2. Process State (Console - Separate Prompt)
            # If we already asked for state in the first step (Assigned flow), use that input
            if ticket_type == "ASSIGNED":
                state_input = user_input # Reuse the input from the single prompt
            else:
                print(f" Select State:")
                print(" [1] Work in Progress (4)")
                print(" [2] Pending Tasks (22)")
                print(" [3] Pending Vendor (21)")
                print(" [4] Pending User (18)")
                print(" [5] Pending Change (19)")
                print(" [S] Skip")
                print(" 📱 Or use Mobile CLI to select")
                state_input = get_input_with_timeout("👉 Select State (1-5) or [S]kip: ", timeout=60, shift_users=shift_users)
           
            # Handle if user switched to Mobile during the 2nd prompt
            if isinstance(state_input, dict):
                # Re-run mobile logic extraction if they used app late
                    if state_input.get('action') == 'skip':
                        skipped_count += 1
                        return None
               
                    if ticket_type == 'ASSIGNED':
                        selected_assignee = None
                    else:
                        u_choice_mob = int(state_input.get('assignee', 0))
                        if 1 <= u_choice_mob <= len(shift_users): selected_assignee = shift_users[u_choice_mob-1]
               
                    s_choice_mob = str(state_input.get('state', ''))
                    if s_choice_mob in val_map:
                        target_val = val_map[s_choice_mob]
                        state_name = name_map[s_choice_mob]
           
                    work_notes_text = state_input.get('work_notes', '')
               
                    print("")
                    log(f" ✅ Selected for {ticket} (Mobile):")
                    if selected_assignee:
                        log(f" 👉 Selected Assignee Name : {selected_assignee}")
                    elif ticket_type == "ASSIGNED":
                        log(f" 👉 Selected Assignee Name : (No Change / Existing)")
                    log(f" 👉 Selected State : {state_name}")
               
            elif state_input.strip().upper() == 'S':
                log(" ⏭️ Skipped.")
                skipped_count += 1
                return None
            else:
                choice = state_input.strip().upper()
                if choice in val_map:
                    target_val = val_map[choice]
                    state_name = name_map[choice]
               
                # LOG CONSOLE SELECTION FINAL SUMMARY
                print("")
                log(f" ✅ Selected for {ticket}:")
                if selected_assignee:
                    log(f" 👉 Selected Assignee Name : {selected_assignee}")
                log(f" 👉 Selected State : {state_name}")
        # --- EXECUTE UPDATE ---
        if target_val: # Assignee can be None if it's an ASSIGNED ticket
            if ticket in skip_memory: del skip_memory[ticket]
            add_work_notes(driver, work_notes_text)
            update_logic(driver, state_el, target_val, state_name, assignee=selected_assignee)
            ack_count += 1 # Acknowledge on update
           
            pending_ticket_data['ticket_data'] = None
            # ⚡ ADD HISTORY
            add_history(ticket, short_desc, state_name, assignee=selected_assignee)
            return {'value': target_val, 'name': state_name, 'assignee': selected_assignee}
       
    except Exception as e:
        log(f" ❌ Error processing ticket: {e}")
        pending_ticket_data['ticket_data'] = None
        return None
def open_and_update(driver, wait, ticket, value, name, assignee):
    if len(driver.window_handles) < 2: driver.execute_script("window.open('');")
    driver.switch_to.window(driver.window_handles[1])
    driver.get(f"{BASE_URL}/incident.do?sysparm_query=number={ticket}")
    try:
        try: wait.until(EC.frame_to_be_available_and_switch_to_it((By.ID, "gsft_main")))
        except: pass
        wait.until(EC.presence_of_element_located((By.ID, "sys_readonly.incident.number")))
       
        state_el = driver.find_element(By.ID, "incident.state")
        update_logic(driver, state_el, value, name, assignee)
    except: pass
def update_logic(driver, state_el, value, name, assignee, silent=False):
    """Executes the update. 'silent' parameter suppresses default logs so specific modes can log their own way."""
    try:
        driver.execute_script(f"arguments[0].value = '{value}';", state_el)
        if assignee:
            try:
                assign_input = driver.find_element(By.ID, "sys_display.incident.assigned_to")
                assign_input.clear()
                time.sleep(0.5)
                assign_input.send_keys(assignee)
                time.sleep(1)
                assign_input.send_keys("\t")
            except: pass
       
        if not silent: log(f" 💾 Saving {name}")
        driver.execute_script("gsftSubmit(document.getElementById('sysverb_update_and_stay'));")
        time.sleep(3)
        if not silent: log(" ✅ Update Successful.")
    except Exception as e:
        log(f" ❌ Update Failed: {e}")
def add_work_notes(driver, work_notes):
    """Add work notes to the ticket"""
    if not work_notes or work_notes.strip() == "":
        return True
    try:
        # Click on work notes textarea
        try:
            work_notes_input = driver.find_element(By.ID, "activity-stream-textarea")
        except:
            # ⚡ Fallback for older UI or if ID differs
            work_notes_input = driver.find_element(By.ID, "incident.work_notes")
        work_notes_input.click()
        time.sleep(0.5)
        try: work_notes_input.clear()
        except: pass
        work_notes_input.send_keys(work_notes)
        time.sleep(1)
        log(f" 📝 Work Notes Added: {work_notes[:50]}...")
        return True
    except Exception as e:
        log(f" ⚠️ Could not add work notes: {e}")
        return True
# ===================================================================
# --- MAIN LOOP ---
# ===================================================================
if __name__ == "__main__":
    # STEP 1: Ask to Enable Web Server
    print("")
    # ⚡ FIX: Using the centered header function here as requested
    print_centered_header("📱 WEB SERVER + MOBILE CLI CONTROL - LIVE LOG VIEWER 📱", char="=")
    print(f" 👉 Local Network: http://{get_local_ip()}:{WEB_SERVER_PORT}")
    print(f" 💡 Ensure mobile & laptop are on SAME WiFi")
    print(f" 🎮 Use Mobile CLI to control tickets remotely!")
    print("=" * LINE_LENGTH)
    print("")
    while True:
        #enable_choice = input("📱 WEB SERVER Live Log Monitor + Mobile CLI - Enable? (Y/N): ").strip().upper()
        enable_choice = 'Y'
        if enable_choice in ['Y', 'N']:
            break
        print(" ❌ Invalid input. Please enter Y or N")
   
    if enable_choice == 'Y':
        log("📱 WEB SERVER + MOBILE CLI: Enabled ✅")
        start_web_server()
        time.sleep(3)
    else:
        log("📱 WEB SERVER: Disabled ❌")
    print("")
    # STEP 2: Ask about OneDrive Usage
    print_centered_header("ONEDRIVE USAGE")
    while True:
        #drive_choice = input(" 👉 Company Onedrive Using (Y/N): ").strip().upper()
        drive_choice = 'N'
        if drive_choice in ['Y', 'N']:
            break
        print(" ❌ Invalid input. Please enter Y or N")
    # Set Dynamic Paths based on Choice
    if drive_choice == 'Y':
        final_log_path = r"C:\Users\2399586\OneDrive - Cognizant\Documents\Snow\Log.txt"
        final_live_path = r"C:\Users\2399586\OneDrive - Cognizant\Documents\Snow\Live.txt"
        log(f" 📂 Using OneDrive Paths: {final_log_path}")
    else:
        final_log_path = r"C:\Users\Mahesh\Downloads\Log.txt"
        final_live_path = r"C:\Users\Mahesh\Downloads\Live.txt"
        log(f" 📂 Using Local Downloads Paths: {final_log_path}")
    # Update the global log manager with the selected paths
    log_manager.update_paths(final_log_path, final_live_path)
    print("")
    # STEP 3: Ask for shift configuration
    shift_users = get_shift_users()
    pending_ticket_data['shift_users'] = shift_users # ⚡ KEY FIX: Save users to global memory immediately
    if not USER or not PASSWORD:
        log("❌ Error: Credentials missing in Configuration section.")
        exit()
    driver = None
    l2_memory = load_l2_from_file()
    skip_memory = {}
    # ⚡ START ALARM CHECKER IN BACKGROUND
    threading.Thread(target=alarm_checker, daemon=True).start()
    while not stop_script:
        try:
            # ⚡ CHECK RESTART FLAGS
            if scrap_toggle_requested:
                log(f"SCRAP MODE : {'ON' if scrap_enabled else 'OFF'}")
                scrap_toggle_requested = False
                try: driver.quit()
                except: pass
                driver = None
                time.sleep(2)
           
            if restart_requested:
                log("\n🔄 Manual Restart Requested via Mobile...")
                restart_count += 1 # ⚡ INCREMENT RESTART COUNT
                try: driver.quit()
                except: pass
                driver = None
               
                # ⚡ RESTART MESSAGE: Print URL again here so it's visible after restart
                if enable_choice == 'Y':
                    print(f"\n 🌐 Local Network: http://{get_local_ip()}:{WEB_SERVER_PORT}\n")
               
                # Reset flag so we don't loop endlessly
                restart_requested = False
                time.sleep(2)
       
            if driver is None:
                driver, wait = initialize_driver()
                driver.execute_script("window.open('about:blank', 'tab2');")
                # ⚡ AUTO-RESTART: Initialize trackers
                session_start_time = time.time()
                session_cycles = 0
            while not stop_script:
                # ⚡ CHECK RESTART FLAGS INSIDE INNER LOOP
                if scrap_toggle_requested or restart_requested: break
               
                # ⚡ AUTO-RESTART: Logic Check
                session_cycles += 1
                cycle_counter += 1
               
                if session_cycles >= AUTO_RESTART_CYCLES or (time.time() - session_start_time) > (AUTO_RESTART_MINUTES * 60):
                     log(f"\n🔄 Auto-Restarting Browser (Limit Reached: {session_cycles} cycles / {int(time.time() - session_start_time)}s)")
                     restart_count += 1 # ⚡ INCREMENT RESTART COUNT
                     try: driver.quit()
                     except: pass
                     driver = None
                     break # Break inner loop to re-initialize
               
                # Track previous queue counts
                prev_queue_counts = queue_counts.copy()
               
                # Update queue counts
                queue_counts['inc_n_l2l3'] = scrape_queue_count(driver, wait, URL_INC_N_L2L3, 'inc_n_l2l3')
                queue_counts['inc_n_fw'] = scrape_queue_count(driver, wait, URL_INC_N_FW, 'inc_n_fw')
                queue_counts['inc_n_akamai'] = scrape_queue_count(driver, wait, URL_INC_N_AKAMAI, 'inc_n_akamai')
                queue_counts['inc_n_sase'] = scrape_queue_count(driver, wait, URL_INC_N_SASE, 'inc_n_sase')
               
                queue_counts['ritm_n_ops'] = scrape_queue_count(driver, wait, URL_RITM_N_OPS, 'ritm_n_ops')
                queue_counts['ritm_n_l2l3'] = scrape_queue_count(driver, wait, URL_RITM_N_L2L3, 'ritm_n_l2l3')
                queue_counts['ritm_n_fw'] = scrape_queue_count(driver, wait, URL_RITM_N_FW, 'ritm_n_fw')
                queue_counts['ritm_n_akamai'] = scrape_queue_count(driver, wait, URL_RITM_N_AKAMAI, 'ritm_n_akamai')
                queue_counts['ritm_n_iap'] = scrape_queue_count(driver, wait, URL_RITM_N_IAP, 'ritm_n_iap')
               
                queue_counts['inc_w_fw'] = scrape_queue_count(driver, wait, URL_INC_W_FW, 'inc_w_fw')
                queue_counts['inc_w_akamai'] = scrape_queue_count(driver, wait, URL_INC_W_AKAMAI, 'inc_w_akamai')
                queue_counts['inc_w_sase'] = scrape_queue_count(driver, wait, URL_INC_W_SASE, 'inc_w_sase')
               
                queue_counts['ritm_w_fw'] = scrape_queue_count(driver, wait, URL_RITM_W_FW, 'ritm_w_fw')
                queue_counts['ritm_w_akamai'] = scrape_queue_count(driver, wait, URL_RITM_W_AKAMAI, 'ritm_w_akamai')
                queue_counts['ritm_w_iap'] = scrape_queue_count(driver, wait, URL_RITM_W_IAP, 'ritm_w_iap')
               
                # Check for increases and play sound if enabled
                if any(queue_counts[k] > prev_queue_counts.get(k, 0) for k in queue_counts):
                    if sound_enabled:
                        play_queue_sound()
                display_queue_stats()
                print_centered_header(f"♻️ Cycle {cycle_counter}: New:{new_count} Reopen:{reopen_count} Ack:{ack_count} Skipped:{skipped_count} ♻️", char="-")
               
                l1_data_list = scrape_l1_incidents_detailed(driver, wait)
                time_now = time.strftime("%H:%M:%S")
                if l1_data_list:
                    log(f" 🎯 Active Tickets Found: {len(l1_data_list)} - {time_now}")
                    for ticket_obj in l1_data_list:
                        # ⚡ CHECK RESTART FLAGS INSIDE TICKET LOOP TOO
                        if scrap_toggle_requested or restart_requested: break
                       
                        result = process_ticket_in_tab2(driver, wait, ticket_obj, l2_memory, shift_users, skip_memory)
                        if result:
                            ticket_num = ticket_obj['ticket']
                            l2_memory[ticket_num] = result
                            # ⚡ KEY FIX: Save to L2 memory file (adjusted format)
                            save_l2_item_to_file(ticket_num, result['name'], ticket_obj['desc'])
                else:
                    log(f" (No tickets found) - {time_now}")
               
                display_cycle_stats()
                time.sleep(POLL_INTERVAL)
       
        except WebDriverException as e:
            log(f"\n⚠️ Browser Connection Lost: {e}")
            log("🔄 Restarting session")
           
            # ⚡ RESTART MESSAGE: Print URL again here so it's visible after restart
            if enable_choice == 'Y':
                 print(f"\n 🌐 Local Network: http://{get_local_ip()}:{WEB_SERVER_PORT}\n")
           
            try: driver.quit()
            except: pass
            driver = None
            time.sleep(5)
       
        except KeyboardInterrupt:
            log("\n🛑 Stopped by User.")
            break
        except Exception as e:
            log(f"\n❌ Unexpected Error: {e}")
            time.sleep(5)
       
    if driver: driver.quit()
    log("🛑 Script Stopped.")