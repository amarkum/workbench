# pylint: skip-file
# flake8: noqa
import csv
import gzip
import hashlib
import io
import json
import logging
import os
import tempfile
import uuid
import webbrowser
import zipfile
from datetime import datetime
from urllib.parse import urlparse
import requests

from flask import Flask, request, render_template_string, redirect, url_for, flash, session, send_file, jsonify
import pandas as pd

logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.CRITICAL)

app = Flask(__name__)
app.secret_key = 'workbench_public_key'

# CSV Edit tracking cache (same as workbench.py)
CSV_DATA_CACHE = {}  # Stores full DataFrame for each file
CSV_EDITS_CACHE = {}  # Stores edits by page and cell

# Simple dark theme HTML
HTML_TEMPLATE = r"""
<!doctype html>
<html>
<head>
    <title>WorkBench</title>
    <script src="https://cdn.tailwindcss.com"></script>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&display=swap" rel="stylesheet">
    <style>
        * { font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif !important; box-sizing: border-box; }
        body, html { margin: 0; padding: 0; background-color: #0f172a !important; color: #e2e8f0 !important; }
        .main-container { background-color: #1e293b !important; color: #e2e8f0 !important; border-radius: 0; }
        input, select, textarea { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
        input:focus, select:focus, textarea:focus { outline: none !important; border-color: #475569 !important; box-shadow: none !important; }
        label { color: #cbd5e1 !important; }
        h1, h2, h3 { color: #f1f5f9 !important; }
        .btn { padding: 0.625rem 1.25rem; font-weight: 500; border-radius: 0; transition: all 0.2s ease; border: none; cursor: pointer; display: inline-flex; align-items: center; justify-content: center; gap: 0.5rem; font-size: 0.875rem; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
        .btn:hover { transform: translateY(-1px); box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06); }
        .btn:disabled { opacity: 0.5; cursor: not-allowed; transform: none; box-shadow: none; }
        .btn-primary { background-color: #6366f1; color: white !important; }
        .btn-primary:hover:not(:disabled) { background-color: #4f46e5; }
        .btn-success { background-color: #10b981; color: white !important; }
        .btn-success:hover:not(:disabled) { background-color: #059669; }
        .btn-secondary { background-color: #64748b; color: white !important; }
        .btn-secondary:hover:not(:disabled) { background-color: #475569; }
        .btn-ghost { background-color: transparent; color: #64748b; box-shadow: none; border: 1px solid #e2e8f0; }
        .btn-ghost:hover:not(:disabled) { background-color: #f8fafc; border-color: #cbd5e1; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
        .btn-ghost.selected, .btn-ghost.selected:hover { background-color: #334155 !important; border-color: #64748b !important; }
        .btn-icon { padding: 0 !important; font-size: 1.125rem !important; line-height: 1 !important; height: 46px; width: 46px; display: inline-flex; align-items: center; justify-content: center; }
        .section-card { border-radius: 0; padding: 1.5rem; box-shadow: 0 1px 3px 0 rgba(0, 0, 0, 0.1), 0 1px 2px 0 rgba(0, 0, 0, 0.06); background-color: #1e293b; border: 1px solid #334155; }
        .greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; color: #94a3b8 !important; }
        .witty-message { font-weight: 400 !important; font-size: 0.875rem !important; margin-top: 0.25rem !important; opacity: 0.8; color: #cbd5e1 !important; }
        .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; margin-bottom: 0.125rem !important; }
        .big-day-date { font-size: 0.875rem !important; font-weight: 500 !important; color: #94a3b8 !important; line-height: 1.2 !important; }
        .big-time-display { display: flex; flex-direction: row; justify-content: flex-end; align-items: center; margin-bottom: 0.5rem; }
        .time-section { text-align: right; height: 46px !important; display: flex !important; flex-direction: column !important; justify-content: center !important; align-items: flex-end !important; }
        
        /* Ensure buttons are visible and properly styled */
        .btn { display: inline-flex !important; visibility: visible !important; opacity: 1 !important; }
        .btn-success { background-color: #10b981 !important; color: white !important; border: none !important; }
        .btn-primary { background-color: #6366f1 !important; color: white !important; border: none !important; }
        .btn-secondary { background-color: #64748b !important; color: white !important; border: none !important; }
        .btn-ghost { background-color: transparent !important; color: #64748b !important; border: 1px solid #e2e8f0 !important; }
        
        /* Input styling */
        input[type="text"], select, textarea { border-radius: 0; border: 1px solid #e2e8f0; padding: 0.625rem 1rem; font-size: 0.875rem; transition: all 0.2s ease; background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
        input[type="text"]:focus, select:focus, textarea:focus { outline: none; border-color: #475569 !important; box-shadow: none !important; }
        input#url_input { font-weight: 400 !important; }
        
        /* Section card styling */
        .section-card { border-radius: 0; padding: 1.5rem; box-shadow: 0 1px 3px 0 rgba(0, 0, 0, 0.1), 0 1px 2px 0 rgba(0, 0, 0, 0.06); background-color: #1e293b; border: 1px solid #334155; }
        
        /* ==================== WHITE THEME ==================== */
        body.white-theme { background-color: #f1f5f9 !important; color: #1e293b !important; }
        .white-theme .main-container { background-color: #f8fafc !important; color: #1e293b !important; border-radius: 0; }
        .white-theme input, .white-theme select, .white-theme textarea { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        body.white-theme input, body.white-theme select, body.white-theme textarea { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        .white-theme input:focus, .white-theme select:focus, .white-theme textarea:focus { outline: none !important; border-color: #e2e8f0 !important; box-shadow: none !important; }
        .white-theme label { color: #475569 !important; }
        .white-theme h1, .white-theme h2, .white-theme h3 { color: #1e293b !important; }
        .white-theme .main-container p, .white-theme .main-container div, .white-theme .main-container span { color: #1e293b !important; }
        .white-theme a { color: #6366f1 !important; }
        .white-theme a:hover { color: #4f46e5 !important; }
        .white-theme .btn-primary { background-color: #6366f1 !important; color: #ffffff !important; }
        .white-theme .btn-primary:hover:not(:disabled) { background-color: #4f46e5 !important; }
        .white-theme .btn-secondary { background-color: #64748b !important; color: #ffffff !important; }
        .white-theme .btn-secondary:hover:not(:disabled) { background-color: #475569 !important; }
        .white-theme .btn-success { background-color: #10b981 !important; color: #ffffff !important; }
        .white-theme .btn-success:hover:not(:disabled) { background-color: #059669 !important; }
        .white-theme .btn-danger { background-color: #ef4444 !important; color: #ffffff !important; }
        .white-theme .btn-danger:hover:not(:disabled) { background-color: #dc2626 !important; }
        .white-theme .btn-ghost { background-color: transparent !important; color: #64748b !important; border-color: #e2e8f0 !important; }
        .white-theme .btn-ghost:hover:not(:disabled) { background-color: #f1f5f9 !important; border-color: #cbd5e1 !important; }
        .white-theme .theme-select { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        body.white-theme .theme-select { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        .white-theme .theme-dropdown { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        body.white-theme .theme-dropdown { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        .white-theme .section-card { background-color: #ffffff; border: 1px solid #e2e8f0; }
        .white-theme .text-sm { color: #64748b !important; }
        .white-theme .text-lg { color: #1e293b !important; }
        .white-theme .font-semibold { color: #1e293b !important; }
        .white-theme .font-medium { color: #475569 !important; }
        .white-theme .greeting-text { color: #64748b !important; }
        .white-theme .witty-message { color: #64748b !important; }
        .white-theme button:disabled { background-color: #f3f4f6 !important; color: #9ca3af !important; border-color: #e5e7eb !important; }
        .white-theme .btn-ghost.selected, .white-theme .btn-ghost.selected:hover { background-color: rgba(0, 0, 0, 0.05) !important; border-color: rgba(0, 0, 0, 0.1) !important; }
        .white-theme #notesTextarea { background: #f9fafb !important; color: #4b5563 !important; caret-color: #4b5563 !important; }
        .white-theme .terminal-container { background: #f9fafb !important; border-color: #d1d5db !important; }
        .white-theme #home-terminal-output { background: #f9fafb !important; color: #4b5563 !important; }
        .white-theme #home-terminal-input { background: #f9fafb !important; color: #4b5563 !important; caret-color: #4b5563 !important; }
        .white-theme .terminal-input-area { background: #f9fafb !important; }
        .white-theme .modern-textarea { background-color: #f8fafc; color: #1a202c; border-color: #cbd5e0; }
        .white-theme .modern-textarea:focus { outline: none; border-color: #cbd5e0; box-shadow: none; }
        .white-theme .modern-encrypt-btn { background-color: #10b981; }
        .white-theme .modern-decrypt-btn { background-color: #06b6d4; }
        .white-theme .copy-icon-btn { background-color: #ffffff; color: #6b7280; border-color: #d1d5db; }
        .white-theme .copy-icon-btn:hover { background-color: #f3f4f6; color: #374151; border-color: #9ca3af; }
        .white-theme .loader { background-color: #e2e8f0; }
        .white-theme .loader::before { background-color: #6366f1; }
        /* ==================== JSON SYNTAX HIGHLIGHTING - WHITE THEME ==================== */
        .white-theme .json-key { color: #0451a5 !important; }
        .white-theme .json-string { color: #a31515 !important; }
        .white-theme .json-number { color: #098658 !important; }
        .white-theme .json-boolean { color: #0000ff !important; }
        .white-theme .json-null { color: #0000ff !important; }
        .white-theme .json-bracket { color: #000000 !important; }
        .white-theme .json-comma { color: #000000 !important; }
        .white-theme .json-toggle { color: #808080 !important; cursor: pointer; }
        .white-theme .json-toggle:hover { color: #000000 !important; }
        
        /* ==================== DARK THEME (Default) ==================== */
        body.dark-theme { background-color: #0f172a !important; color: #e2e8f0 !important; }
        .dark-theme .main-container { background-color: #1e293b !important; color: #e2e8f0 !important; border-radius: 0; }
        .dark-theme input, .dark-theme select, .dark-theme textarea { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
        .dark-theme input:focus, .dark-theme select:focus, .dark-theme textarea:focus { outline: none !important; border-color: #475569 !important; box-shadow: none !important; }
        .dark-theme label { color: #cbd5e1 !important; }
        .dark-theme h1, .dark-theme h2, .dark-theme h3 { color: #f1f5f9 !important; }
        .dark-theme .btn-primary { background-color: #6366f1 !important; color: #ffffff !important; }
        .dark-theme .btn-primary:hover:not(:disabled) { background-color: #4f46e5 !important; }
        .dark-theme .btn-secondary { background-color: #475569 !important; color: #ffffff !important; }
        .dark-theme .btn-secondary:hover:not(:disabled) { background-color: #334155 !important; }
        .dark-theme .btn-success { background-color: #10b981 !important; color: #ffffff !important; }
        .dark-theme .btn-success:hover:not(:disabled) { background-color: #059669 !important; }
        .dark-theme .btn-danger { background-color: #ef4444 !important; color: #ffffff !important; }
        .dark-theme .btn-danger:hover:not(:disabled) { background-color: #dc2626 !important; }
        .dark-theme .btn-ghost { background-color: transparent !important; color: #94a3b8 !important; border-color: #475569 !important; }
        .dark-theme .btn-ghost:hover:not(:disabled) { background-color: #334155 !important; border-color: #64748b !important; }
        .dark-theme .section-card { background-color: #1e293b; border: 1px solid #334155; }
        .dark-theme .big-time { color: #e2e8f0 !important; }
        .dark-theme .big-day-date { color: #94a3b8 !important; }
        .dark-theme #terminal-section { background-color: #1e293b !important; }
        .dark-theme .terminal-container { background-color: #0d1117 !important; border-color: #30363d !important; }
        .dark-theme #home-terminal-output { background-color: #0d1117 !important; color: #ffffff !important; }
        .dark-theme #home-terminal-input { background-color: #0d1117 !important; color: #ffffff !important; caret-color: #ffffff !important; }
        .dark-theme .terminal-input-area { background-color: #0d1117 !important; }
        .dark-theme #notesTextarea { background-color: #0d1117 !important; color: #ffffff !important; caret-color: #ffffff !important; }
    </style>
</head>
<body class="min-h-screen">
    <div class="w-full min-h-screen main-container p-8">
        <div class="flex items-center justify-between mb-12">
            <div class="flex items-center">
                <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
            </div>
            <div class="flex items-center space-x-4">
                <!-- Time display -->
                <div class="big-time-display">
                    <div class="time-section">
                        <div class="big-time">{{ big_time_display.big_time }}</div>
                        <div class="big-day-date">{{ big_time_display.day_date }}</div>
                    </div>
                </div>
                <!-- Theme selector -->
                <select id="theme-select" class="border px-4 py-2 text-base theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="setTheme(this.value)">
                    <option value="dark">🌃 Dark</option>
                    <option value="white">🔆 White</option>
                </select>
            </div>
        </div>
        
        <!-- Main form -->
        <form action="{{ url_for('home') }}" method="post" enctype="multipart/form-data" class="space-y-4" id="main-form" onsubmit="updatePaginationBeforeSubmit()">
            <!-- Row 1: URL Input -->
            <div class="flex items-center space-x-2">
                <!-- Paste button -->
                <button type="button" id="pasteBtn" class="btn btn-ghost btn-icon" title="Paste URL">📋</button>
                <!-- Edit URL button -->
                <button type="submit" id="editUrlBtn" name="action" value="view" class="btn btn-ghost btn-icon" title="View URL content" onclick="showEditLoader()">✏️</button>
                <!-- URL input -->
                <input type="text" id="url_input" name="url_input" 
                       class="flex-grow border px-4 py-2 text-base theme-transition" 
                       placeholder="Enter public URL (http:// or https://)" 
                       value="{{ last_url }}" style="height: 46px;" autocomplete="off" />
            </div>
            
            <!-- Row 2: Local File -->
            <div class="flex items-center space-x-2">
                <!-- Local browse button -->
                <button type="button" id="browseBtn" class="btn btn-ghost btn-icon" title="Select local file">📁</button>
                            <!-- Edit local button -->
            <button type="submit" id="editLocalBtn" name="action" value="edit_local" class="btn btn-ghost btn-icon" title="Edit local file" onclick="showEditLoader()">✏️</button>
            <input type="hidden" name="csv_per_page" id="csv_per_page_hidden" value="20" />
                <!-- Hidden file input -->
                <input type="file" id="upload_file" name="upload_file" accept="*" class="hidden" />
                <!-- Local file display -->
                <input type="text" id="local_path" class="flex-grow border px-4 py-2 text-base theme-transition" 
                       placeholder="No file selected" readonly style="height: 46px;" />
            </div>
            
            <!-- Hidden fields -->
            <input type="hidden" name="path" id="path_input" value="" />
            <input type="hidden" name="download_count" id="limit_input" value="All" />
            <input type="hidden" name="delim" id="delim_input" value="" />
            <input type="hidden" name="records_per_page" id="records_per_page_input" value="20" />
            <input type="hidden" name="orig_url" id="orig_url" value="" />
            <input type="hidden" name="raw_edit" id="raw_edit_input" value="" />
            
            <!-- Row 3: Action buttons -->
            <div class="flex items-center justify-between">
                <!-- Left side: Terminal -->
                <div class="flex items-center space-x-2">
                    <button id="terminalToggleBtn" type="button" class="btn btn-ghost theme-transition" 
                            title="Open Terminal" onclick="window.createAndShowTerminal(); return false;">🖥️ Terminal</button>
                </div>
                <!-- Right side: Records per page and Clear button -->
                <div class="flex items-center space-x-2">
                    <label class="text-sm font-medium">Pagination</label>
                    <span id="recordsPerPage" contenteditable="true" 
                          class="px-1 py-2 border border-gray-300 focus:outline-none focus:border-blue-500 inline-block min-w-[60px] text-center theme-transition" 
                          title="Number of records to show per page when editing CSV files">20</span>
                    <button id="clearBtn" type="button" class="btn btn-danger" onclick="clearAll(); return false;">Clear</button>
                </div>
            </div>
        </form>
        
        <!-- Terminal Section -->
        <div id="terminal-section" class="mt-8 section-card" style="display: none;">
            <div class="flex items-center justify-between mb-4">
                <h2 class="text-xl font-semibold">Terminal 🖥️</h2>
                <button onclick="closeTerminal(); return false;" class="btn btn-ghost" title="Close Terminal">⛌</button>
            </div>
            <div class="terminal-container" style="border: 1px solid #30363d; height: 400px; display: flex; flex-direction: column; overflow: hidden; margin-bottom: 10px;">
                <div id="home-terminal-output" class="terminal-output" style="flex: 1; font-family: 'Monaco', 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; padding: 15px; overflow-y: auto; white-space: pre-wrap; font-size: 15px !important; line-height: 1.6 !important; margin: 0; border-radius: 0;"></div>
                <div class="terminal-input-area" style="padding: 0; margin: 0; display: flex; align-items: center;">
                    <span id="terminal-prompt" style="font-family: 'Monaco', 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 15px !important; padding-left: 15px; user-select: none; pointer-events: none;">$</span>
                    <input type="text" id="home-terminal-input" class="terminal-input" style="flex: 1; border: none; font-weight: normal; font-family: 'Monaco', 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 15px !important; outline: none; padding: 15px; padding-left: 5px; box-shadow: none; border-radius: 0; text-align: left; -webkit-tap-highlight-color: transparent; -webkit-appearance: none; -moz-appearance: none; appearance: none;" />           </div>
            </div>
        </div>
        
        <!-- Notes Section (Default) -->
        <div id="notes-section" class="mt-8 section-card">
            <div class="flex items-center justify-between mb-4">
                <h2 class="text-xl font-semibold">Notes 📝</h2>
                <button onclick="saveNotesToFile(); return false;" class="btn btn-ghost theme-transition" title="Save notes to file">💾 Save</button>
            </div>
            <div class="terminal-container" style="border: 1px solid #30363d; height: 400px; display: flex; flex-direction: column; overflow: hidden; margin-bottom: 10px;">
                <textarea id="notesTextarea" class="notes-textarea" style="flex: 1; width: 100%; height: 100%; font-family: 'Monaco', 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; padding: 20px; overflow-y: auto; white-space: pre-wrap; font-size: 15px; line-height: 1.6; margin: 0; border-radius: 0; border: none; outline: none; resize: none;" onload="if(typeof initializeNotes === 'function') initializeNotes();"></textarea>
            </div>
        </div>
        

    </div>

    <script>
        // File browser functionality
        const browseBtn = document.getElementById('browseBtn');
        const uploadFile = document.getElementById('upload_file');
        const localPath = document.getElementById('local_path');
        
        if (browseBtn && uploadFile) {
            browseBtn.addEventListener('click', function() {
                uploadFile.click();
            });
        }
        
        if (uploadFile && localPath) {
            uploadFile.addEventListener('change', function() {
                const file = this.files[0];
                if (file) {
                    localPath.value = file.name;
                }
            });
        }
        
        // Theme switching function (copied from workbench.py)
        function setTheme(theme) {
            // Apply theme immediately without transition
            document.documentElement.className = theme + '-theme';
            document.body.className = 'min-h-screen ' + theme + '-theme';
            // Save to localStorage for persistence across sessions
            localStorage.setItem('workbench-theme', theme);
            // Update dropdown selection
            const dropdown = document.getElementById('theme-select');
            if (dropdown) dropdown.value = theme;

            // Save to server session
            fetch('/set-theme', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                },
                body: JSON.stringify({theme: theme})
            }).then(response => response.json())
                .then(data => {
                    console.log('Theme saved to server:', data);
                })
                .catch(error => {
                    console.error('Error saving theme:', error);
                });
        }
        
        // Get theme from server and localStorage, prioritize localStorage for persistence
        const serverTheme = 'dark'; // Default theme
        const savedTheme = localStorage.getItem('workbench-theme');
        const currentTheme = savedTheme || serverTheme || 'dark';

        // Apply the theme immediately
        document.documentElement.className = currentTheme + '-theme';
        document.body.className = 'min-h-screen ' + currentTheme + '-theme';

        // Save to localStorage if not already saved
        if (!savedTheme) {
            localStorage.setItem('workbench-theme', currentTheme);
        }

        // Set active dropdown on load
        window.addEventListener('DOMContentLoaded', function() {
            const activeTheme = localStorage.getItem('workbench-theme') || serverTheme || 'dark';
            const themeDropdown = document.getElementById('theme-select');
            if (themeDropdown) themeDropdown.value = activeTheme;
            // Apply theme immediately without transition
            document.documentElement.className = activeTheme + '-theme';
            document.body.className = 'min-h-screen ' + activeTheme + '-theme';
        });
        
        // Notes persistence
        const notesTextarea = document.getElementById('notesTextarea');
        if (notesTextarea) {
            const savedNotes = localStorage.getItem('workbench-notes');
            if (savedNotes) {
                notesTextarea.value = savedNotes;
            }
            
            notesTextarea.addEventListener('input', function() {
                localStorage.setItem('workbench-notes', this.value);
            });
        }
        
        // Pagination and URL persistence
        const recordsPerPage = document.getElementById('recordsPerPage');
        const urlInput = document.getElementById('url_input');
        
        // Load saved settings from session
        function loadSavedSettings() {
            fetch('/get-settings', { method: 'GET' })
                .then(response => response.json())
                .then(data => {
                    if (data.success) {
                        if (data.pagination_count && recordsPerPage) {
                            recordsPerPage.textContent = data.pagination_count;
                            // Update hidden field
                            const csvPerPageHidden = document.getElementById('csv_per_page_hidden');
                            if (csvPerPageHidden) csvPerPageHidden.value = data.pagination_count;
                        }
                        if (data.url_input && urlInput) {
                            urlInput.value = data.url_input;
                        }
                    }
                })
                .catch(error => console.error('Error loading settings:', error));
        }
        
        // Save settings when pagination changes
        if (recordsPerPage) {
            recordsPerPage.addEventListener('input', function() {
                const value = this.textContent;
                saveSettings(value, urlInput ? urlInput.value : '');
            });
        }
        
        // Save settings when URL changes
        if (urlInput) {
            urlInput.addEventListener('input', function() {
                const paginationValue = recordsPerPage ? recordsPerPage.textContent : '20';
                saveSettings(paginationValue, this.value);
            });
        }
        
        // Function to save settings to server
        function saveSettings(paginationCount, urlInput) {
            fetch('/save-settings', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                },
                body: JSON.stringify({
                    pagination_count: paginationCount,
                    url_input: urlInput
                })
            })
            .then(response => response.json())
            .then(data => {
                if (data.success) {
                    console.log('Settings saved successfully');
                }
            })
            .catch(error => console.error('Error saving settings:', error));
        }
        
        // Load settings when page loads
        loadSavedSettings();
        

        
        // Pagination persistence - run immediately on DOM load
        document.addEventListener('DOMContentLoaded', function() {
            const recordsPerPage = document.getElementById('recordsPerPage');
            const recordsPerPageHidden = document.getElementById('records_per_page_hidden');
            const csvPerPageHidden = document.getElementById('csv_per_page_hidden');
            
            console.log('Loading pagination from localStorage...');
            
            // Initialize records per page from localStorage or default to 20
            if (recordsPerPage) {
                let savedRecordsPerPage = localStorage.getItem('workbench-records-per-page');
                console.log('Saved pagination count:', savedRecordsPerPage);
                
                if (!savedRecordsPerPage) {
                    savedRecordsPerPage = '20';
                    localStorage.setItem('workbench-records-per-page', savedRecordsPerPage);
                }
                
                // Always set the display value
                recordsPerPage.textContent = savedRecordsPerPage;
                
                // Update hidden fields if they exist
                if (recordsPerPageHidden) {
                    recordsPerPageHidden.value = savedRecordsPerPage;
                }
                if (csvPerPageHidden) {
                    csvPerPageHidden.value = savedRecordsPerPage;
                }
                
                console.log('Set pagination display to:', savedRecordsPerPage);
            }
            
            // Add event listeners for the recordsPerPage element
            if (recordsPerPage) {
                recordsPerPage.addEventListener('blur', function() {
                    const value = this.textContent;
                    console.log('Saving pagination count:', value);
                    localStorage.setItem('workbench-records-per-page', value);

                    if (recordsPerPageHidden) {
                        recordsPerPageHidden.value = value;
                    }
                    if (csvPerPageHidden) {
                        csvPerPageHidden.value = value;
                    }
                });
                
                // Also update on input for real-time sync
                recordsPerPage.addEventListener('input', function() {
                    const value = this.textContent;
                    if (csvPerPageHidden) {
                        csvPerPageHidden.value = value;
                    }
                });
            }
        });
        
        // Function to update pagination before form submission
        window.updatePaginationBeforeSubmit = function() {
            const recordsPerPage = document.getElementById('recordsPerPage');
            const csvPerPageHidden = document.getElementById('csv_per_page_hidden');
            
            if (recordsPerPage && csvPerPageHidden) {
                const currentValue = recordsPerPage.textContent || '20';
                csvPerPageHidden.value = currentValue;
                console.log('Updated csv_per_page_hidden to:', currentValue);
            }
            
            // Also sync with localStorage
            const savedValue = localStorage.getItem('workbench-records-per-page') || '20';
            if (csvPerPageHidden) {
                csvPerPageHidden.value = savedValue;
                console.log('Set csv_per_page_hidden from localStorage:', savedValue);
            }
            
            return true; // Allow form submission to continue
        };
        
        // Function to show edit loader
        window.showEditLoader = function() {
            // Prevent multiple loaders
            if (document.getElementById('edit-loader')) {
                return;
            }

            const currentTheme = document.body.className;
            let progressColor = '#6366f1';
            let backgroundColor = '#334155';

            if (currentTheme.includes('white-theme')) {
                progressColor = '#6366f1';
                backgroundColor = '#e2e8f0';
            }

            const loader = document.createElement('div');
            loader.id = 'edit-loader';
            loader.style.cssText = `
                position: fixed;
                top: 0;
                left: 0;
                width: 100%;
                height: 100%;
                background: rgba(0, 0, 0, 0.3);
                backdrop-filter: blur(8px);
                display: flex;
                justify-content: center;
                align-items: center;
                z-index: 9999;
                font-family: 'Inter', sans-serif;
            `;

            loader.innerHTML = `
                <div style="text-align: center;">
                    <div style="color: white; font-size: 18px; font-weight: 600; margin-bottom: 20px;">LOADING EDITOR</div>
                    <div style="width: 800px; height: 5px; background-color: ${backgroundColor}; border-radius: 0px; overflow: hidden; position: relative; margin: 0 auto;">
                        <div id="edit-progress-bar" style="position: absolute; top: 0; left: 0; width: 0%; height: 100%; background-color: ${progressColor}; transition: width 0.3s ease; border-radius: 0px;"></div>
                    </div>
                    <div style="font-size: 24px; font-weight: 800; color: white; margin-top: 20px;" id="edit-progress-text">0%</div>
                </div>
            `;

            document.body.appendChild(loader);

            // Animate progress
            let progress = 0;
            const interval = setInterval(() => {
                progress += 5;
                document.getElementById('edit-progress-bar').style.width = progress + '%';
                document.getElementById('edit-progress-text').textContent = progress + '%';
                
                if (progress >= 100) {
                    clearInterval(interval);
                }
            }, 100);
        };
        
        // Terminal functionality with proper toggle
        window.createAndShowTerminal = function(showImmediately = true) {
            console.log('createAndShowTerminal called');
            
            var terminalSection = document.getElementById('terminal-section');
            var terminalBtn = document.getElementById('terminalToggleBtn');
            
            console.log('Terminal section found:', !!terminalSection);
            console.log('Terminal button found:', !!terminalBtn);
            
            if (!terminalSection) {
                console.error('Terminal section not found!');
                return false;
            }
            
            // Toggle terminal visibility
            if (terminalSection.style.display === 'none' || !terminalSection.style.display) {
                console.log('Opening terminal...');
                // Show the terminal and update button state
                terminalSection.style.display = 'block';
                if (terminalBtn) {
                    terminalBtn.classList.add('selected');
                }
                
                // Focus and scroll only if showImmediately is true
                if (showImmediately) {
                    setTimeout(function() {
                        var input = document.getElementById('home-terminal-input');
                        if (input) input.focus();
                        terminalSection.scrollIntoView({behavior: 'smooth'});
                    }, 100);
                }
                
                // Save state
                var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
                if (!openSections.includes('terminal')) {
                    openSections.push('terminal');
                    localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
                }
            } else {
                console.log('Closing terminal...');
                // Close terminal
                window.closeTerminal();
            }
            
            return false;
        };
        
        window.closeTerminal = function() {
            var terminalSection = document.getElementById('terminal-section');
            var terminalBtn = document.getElementById('terminalToggleBtn');
            if (terminalSection) {
                terminalSection.style.display = 'none';
                if (terminalBtn) {
                    terminalBtn.classList.remove('selected');
                }
                
                // Remove from open sections
                var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
                var index = openSections.indexOf('terminal');
                if (index > -1) {
                    openSections.splice(index, 1);
                    localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
                }
            }
        };
        
        // Terminal command execution
        const terminalInput = document.getElementById('home-terminal-input');
        if (terminalInput) {
            console.log('Terminal input element found, adding event listener...');
            terminalInput.addEventListener('keydown', function(e) {
                if (e.key === 'Enter') {
                    const command = this.value.trim();
                    console.log('Enter pressed, command:', command);
                    if (command) {
                        console.log('Executing command:', command);
                        window.executeTerminalCommand(command);
                        this.value = '';
                    }
                }
            });
            console.log('Event listener added successfully');
        } else {
            console.error('Terminal input element not found!');
        }
        
        window.executeTerminalCommand = function(command) {
            var output = document.getElementById('home-terminal-output');
            if (!output) return;

                        // Handle built-in commands
            if (command.toLowerCase() === 'clear' || command.toLowerCase() === 'cls') {
                output.innerHTML = '';

                // Restore welcome message after clearing (same as clear button)
                const theme = document.body.className.includes('white-theme') ? 'white' : 
                             document.body.className.includes('pink-theme') ? 'pink' : 'dark';

                const welcomeColor = theme === 'dark' ? '#ffffff' : 
                                    theme === 'white' ? '#4b5563' : '#831843';
                const helpColor = theme === 'dark' ? '#ffffff' : 
                                 theme === 'white' ? '#6b7280' : '#be185d';

                output.innerHTML = 'Welcome to WorkBench Terminal<br>Type some command e.g. pip install pandas<br><br>';
                return;
            }

            // Show command being executed with theme-aware colors
            var theme = document.body.className.includes('white-theme') ? 'white' : 
                       document.body.className.includes('pink-theme') ? 'pink' : 'dark';

            var promptColor = theme === 'dark' ? '#74c0fc' : 
                             theme === 'white' ? '#059669' : '#be185d';
            var commandColor = theme === 'dark' ? '#ffffff' : 
                              theme === 'white' ? '#4b5563' : '#831843';

            output.innerHTML += `<br>$ ${command}<br>`;

            // Send command to server
            fetch('/execute_command', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                },
                body: JSON.stringify({ command: command })
            })
            .then(response => response.json())
            .then(data => {
                // Theme-aware colors for command output
                var theme = document.body.className.includes('white-theme') ? 'white' : 
                           document.body.className.includes('pink-theme') ? 'pink' : 'dark';

                             var outputColor = theme === 'dark' ? '#ffffff' : 
                              theme === 'white' ? '#4b5563' : '#831843';
                var errorColor = theme === 'dark' ? '#ffffff' : 
                                theme === 'white' ? '#dc2626' : '#be185d';

                             if (data.error) {
               output.innerHTML += `Error: ${data.error}<br>`;
             } else {
               // Show output
               if (data.output) {
                 output.innerHTML += `${data.output}`;
               }
               // Show error output
               if (data.stderr) {
                 output.innerHTML += `${data.stderr}`;
               }
             }
                output.scrollTop = output.scrollHeight;
            })
            .catch(error => {
                // Theme-aware error color
                var theme = document.body.className.includes('white-theme') ? 'white' : 
                           document.body.className.includes('pink-theme') ? 'pink' : '#be185d';

                var errorColor = theme === 'dark' ? '#ffffff' : 
                                theme === 'white' ? '#dc2626' : '#be185d';

                output.innerHTML += `<span style="color: ${errorColor};">Error: ${error.message}</span><br>`;
                output.scrollTop = output.scrollHeight;
            });
        };
        
        // Clear all function
        function clearAll() {
            document.getElementById('url_input').value = '';
            document.getElementById('local_path').value = '';
            document.getElementById('notesTextarea').value = '';
            document.getElementById('home-terminal-output').innerHTML = '';
            localStorage.removeItem('workbench-notes');
            alert('All fields cleared!');
        }
        
        // Notes save to file function
        function saveNotesToFile() {
            const notes = document.getElementById('notesTextarea').value;
            if (notes) {
                const blob = new Blob([notes], {type: 'text/plain'});
                const a = document.createElement('a');
                a.href = URL.createObjectURL(blob);
                a.download = 'workbench_notes.txt';
                a.click();
            }
        }
        
        // Initialize terminal with welcome message and restore state
        document.addEventListener('DOMContentLoaded', function() {
            console.log('DOM loaded, checking terminal functions...');
            console.log('createAndShowTerminal available:', typeof window.createAndShowTerminal);
            console.log('closeTerminal available:', typeof window.closeTerminal);
            
            
            var output = document.getElementById('home-terminal-output');
            if (output) {
                const welcomeColor = '#ffffff';
                const helpColor = '#ffffff';
                output.innerHTML = 'Welcome to WorkBench Terminal<br>Type some command e.g. pip install pandas<br><br>';
            }
            
            // Restore terminal state
            var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
            if (openSections.includes('terminal')) {
                var terminalSection = document.getElementById('terminal-section');
                var terminalBtn = document.getElementById('terminalToggleBtn');
                if (terminalSection && terminalBtn) {
                    terminalSection.style.display = 'block';
                    terminalBtn.classList.add('selected');
                }
            }
            
            // Test terminal button click
            if (terminalBtn) {
                console.log('Terminal button found and ready!');
            }
        });
    </script>
</body>
</html>
"""
CSV_EDIT_HTML = r"""
<!doctype html>
<html>
   <head>
      <title>WorkBench</title>
      <script src="https://cdn.tailwindcss.com"></script>
      <link rel="preconnect" href="https://fonts.googleapis.com">
      <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
      <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&display=swap" rel="stylesheet">
      <link href="https://fonts.googleapis.com/css2?family=Ubuntu+Mono:wght@400;700&display=swap" rel="stylesheet">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/fira-code@5.0.18/400.css">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/cascadia-code@5.0.7/400.css">
      <style>
         /* ==================== BASE STYLES ==================== */
         * { font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif !important; }
         body, html, input, textarea, select, button, div, span, label, p, h1, h2, h3, h4, h5, h6, option, td, th { font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif !important; }
         .theme-transition { transition: all 0.3s ease; }
         /* ==================== BUTTON STYLES ==================== */
         .btn { padding: 0.625rem 1.25rem; font-weight: 500; border-radius: 0; transition: all 0.2s ease; border: none; cursor: pointer; display: inline-flex; align-items: center; justify-content: center; gap: 0.5rem; font-size: 0.875rem; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); height: 46px; }
         .btn:hover { transform: translateY(-1px); box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06); }
         .btn:active { transform: translateY(0); box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
         .btn:disabled { opacity: 0.5; cursor: not-allowed; transform: none; box-shadow: none; }
         .btn-primary { background-color: #6366f1; color: white; }
         .btn-primary:hover:not(:disabled) { background-color: #4f46e5; }
         .btn-secondary { background-color: #64748b; color: white; }
         .btn-secondary:hover:not(:disabled) { background-color: #475569; }
         .btn-success { background-color: #10b981; color: white; }
         .btn-success:hover:not(:disabled) { background-color: #059669; }
         .btn-ghost { background-color: transparent; color: #64748b; box-shadow: none; border: 1px solid #e2e8f0; }
         .btn-ghost:hover:not(:disabled) { background-color: #f8fafc; border-color: #cbd5e1; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
         /* ==================== INPUT STYLES ==================== */
         input[type="text"], select { border-radius: 0; border: 1px solid #e2e8f0; padding: 0.625rem 1rem; font-size: 0.875rem; transition: all 0.2s ease; }
         input[type="text"]:focus, select:focus { outline: none; border-color: inherit; box-shadow: none; }
         /* ==================== DARK THEME ==================== */
         body.dark-theme { background-color: #1e293b !important; color: #e2e8f0 !important; }
         .dark-theme input, .dark-theme select { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
         .dark-theme input:focus, .dark-theme select:focus { outline: none !important; border-color: #475569 !important; box-shadow: none !important; }
         .dark-theme table { background-color: #1e293b !important; border-radius: 0; overflow: hidden; }
         .dark-theme thead { background-color: #334155 !important; }
         .dark-theme th, .dark-theme td { border-color: #475569 !important; color: #e2e8f0 !important; }
         .dark-theme td[contenteditable] { background-color: #1e293b !important; }
         .dark-theme td[contenteditable]:hover { background-color: #334155 !important; }
         .dark-theme td[contenteditable]:focus { background-color: #334155 !important; outline: none !important; }
         .dark-theme .btn-primary { background-color: #6366f1 !important; }
         .dark-theme .btn-primary:hover:not(:disabled) { background-color: #4f46e5 !important; }
         .dark-theme .btn-secondary { background-color: #475569 !important; }
         .dark-theme .btn-secondary:hover:not(:disabled) { background-color: #334155 !important; }
         .dark-theme .btn-ghost { background-color: transparent !important; color: #94a3b8 !important; border-color: #475569 !important; }
         .dark-theme .btn-ghost:hover:not(:disabled) { background-color: #334155 !important; border-color: #64748b !important; }
         .dark-theme .theme-select { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
         .dark-theme .page-btn { background-color: #334155 !important; color: #e2e8f0 !important; border: 1px solid #475569 !important; }
         .dark-theme .page-btn:hover { background-color: #475569 !important; }
         .dark-theme .page-btn.active { background-color: #334155 !important; color: #94a3b8 !important; border-color: #64748b !important; }
         .dark-theme .record-info { color: #cbd5e1 !important; }
         .dark-theme .record-info span { color: #e2e8f0 !important; }
         /* ==================== WHITE THEME ==================== */
         body.white-theme { background-color: #f1f5f9 !important; }
         .white-theme table { background-color: #ffffff !important; border-radius: 0; overflow: hidden; }
         .white-theme thead { background-color: #f3f4f6 !important; }
         .white-theme th, .white-theme td { border-color: #e5e7eb !important; }
         .white-theme .page-btn { background-color: #ffffff !important; color: #1e293b !important; border: 1px solid #e2e8f0 !important; }
         .white-theme .page-btn:hover { background-color: #e5e7eb !important; color: #1e293b !important; border-color: #d1d5db !important; }
         .white-theme .page-btn.active { background-color: rgba(0, 0, 0, 0.05) !important; color: #64748b !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         .white-theme .btn-ghost { border-color: #e2e8f0 !important; }
         .white-theme .btn-ghost:hover:not(:disabled) { background-color: #f8fafc !important; }
         .white-theme .record-info { color: #6b7280 !important; }
         .white-theme .record-info span { color: #1f2937 !important; }
         .white-theme .main-container { background-color: #f8fafc !important; color: #1e293b !important; border-radius: 0; }
         .white-theme input, .white-theme select { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
         .white-theme input:focus, .white-theme select:focus { outline: none !important; border-color: #e2e8f0 !important; box-shadow: none !important; }
         /* ==================== PINK THEME ==================== */
         body.pink-theme { background-color: #fdf2f8 !important; color: #831843 !important; }
         .pink-theme input, .pink-theme select { background-color: #fce7f3 !important; color: #831843 !important; border-color: #fbcfe8 !important; }
         .pink-theme input:focus, .pink-theme select:focus { outline: none !important; border-color: #fbcfe8 !important; box-shadow: none !important; }
         .pink-theme table { background-color: #ffffff !important; border-radius: 0; overflow: hidden; }
         .pink-theme thead { background-color: #fce7f3 !important; }
         .pink-theme th, .pink-theme td { border-color: #fbcfe8 !important; color: #831843 !important; }
         .pink-theme td[contenteditable] { background-color: #ffffff !important; }
         .pink-theme td[contenteditable]:hover { background-color: #fce7f3 !important; }
         .pink-theme td[contenteditable]:focus { background-color: #fce7f3 !important; outline: none !important; }
         .pink-theme .btn-primary { background-color: #ec4899 !important; }
         .pink-theme .btn-primary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-success { background-color: #db2777 !important; color: #ffffff !important; }
         .pink-theme .btn-success:hover:not(:disabled) { background-color: #be185d !important; }
         .pink-theme .btn-secondary { background-color: #ec4899 !important; color: #ffffff !important; }
         .pink-theme .btn-secondary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-ghost { color: #be185d !important; border-color: #fbcfe8 !important; }
         .pink-theme .btn-ghost:hover:not(:disabled) { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
         .pink-theme .theme-select { background-color: #fce7f3 !important; color: #831843 !important; border-color: #fbcfe8 !important; }
         .pink-theme .page-btn { background-color: #fce7f3 !important; color: #831843 !important; border: 1px solid #fbcfe8 !important; }
         .pink-theme .page-btn:hover { background-color: #fbcfe8 !important; }
         .pink-theme .page-btn.active { background-color: #fce7f3 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         .pink-theme .record-info { color: #be185d !important; }
         .pink-theme .record-info span { color: #831843 !important; font-weight: 700 !important; }
         /* ==================== SELECTED BUTTON STATES ==================== */
         .btn-ghost.selected { background-color: #334155 !important; border-color: #64748b !important; }
         .dark-theme .btn-ghost.selected { background-color: #334155 !important; border-color: #64748b !important; }
         .white-theme .btn-ghost.selected { background-color: #f8fafc !important; border-color: #e2e8f0 !important; }
         .pink-theme .btn-ghost.selected { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
         /* ==================== COMMON STYLES ==================== */
         .witty-message { font-weight: 400 !important; font-size: 0.875rem !important; margin-top: 0.25rem !important; opacity: 0.8; }
         .dark-theme .witty-message { color: #cbd5e1 !important; }
         .white-theme .witty-message { color: #64748b !important; }
         .pink-theme .witty-message { color: #db2777 !important; }
         .greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; }
         p.greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; }
                   .dark-theme .greeting-text { color: #94a3b8 !important; }
          .white-theme .greeting-text { color: #64748b !important; }
          .pink-theme .greeting-text { color: #be185d !important; }
          .dark-theme .big-greeting { color: #94a3b8 !important; }
          .dark-theme .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; }
          .dark-theme .big-day-date { color: #94a3b8 !important; }
          .white-theme .big-greeting { color: #64748b !important; }
          .white-theme .big-time { color: #1e293b !important; font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
          .white-theme .big-day-date { color: #64748b !important; font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }
          .pink-theme .big-greeting { color: #be185d !important; }
          .pink-theme .big-time { color: #831843 !important; font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
          .pink-theme .big-day-date { color: #be185d !important; font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }
         /* ==================== MODULE BADGE ==================== */
         .module-badge { border-radius: 0; border: 1px solid; font-weight: 600; font-size: 14px; min-width: 60px; text-align: center; }
         .dark-theme .module-badge { background-color: #374151 !important; color: #e0e7ff !important; border-color: #4b5563 !important; }
         .white-theme .module-badge { background-color: #ffffff !important; color: #1e40af !important; border-color: #d1d5db !important; }
         .pink-theme .module-badge { background-color: #fdf2f8 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         /* ==================== DROPDOWNS ==================== */
         .module-dropdown { font-weight: 500; border-radius: 0px !important; }
         .theme-dropdown { border: 1px solid #d1d5db; font-weight: 500; padding: 8px 12px !important; border-radius: 0px !important; font-size: 14px !important; height: 46px !important; }
         .dark-theme .module-dropdown, .dark-theme .theme-dropdown { background-color: #374151 !important; color: #e0e7ff !important; border-color: #4b5563 !important; }
         .white-theme .module-dropdown, .white-theme .theme-dropdown { background-color: #f8fafc !important; color: #1e293b !important; border: 1px solid #e2e8f0 !important; padding: 8px 12px !important; border-radius: 0px !important; font-size: 14px !important; height: 46px !important; }
         .pink-theme .module-dropdown, .pink-theme .theme-dropdown { background-color: #fdf2f8 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         /* ==================== EDITED CELLS ==================== */
         td.edited { background-color: #fef3c7 !important; position: relative; }
         td.edited::after { content: ''; position: absolute; top: 0; right: 0; width: 0; height: 0; border-style: solid; border-width: 0 8px 8px 0; border-color: transparent #f59e0b transparent transparent; }
         .dark-theme td.edited { background-color: #1e3a8a !important; }
         .dark-theme td.edited::after { border-color: transparent #3b82f6 transparent transparent; }
         .white-theme td.edited { background-color: #fef3c7 !important; }
         .white-theme td.edited::after { border-color: transparent #f59e0b transparent transparent; }
         .pink-theme td.edited { background-color: #f3e8ff !important; }
         .pink-theme td.edited::after { border-color: transparent #a855f7 transparent transparent; }
         .edit-indicator { margin-left: 10px; padding: 2px 8px; background: #f59e0b; color: white; border-radius: 0; font-size: 0.75rem; font-weight: normal; }
         .dark-theme .edit-indicator { background: #3b82f6; }
         .pink-theme .edit-indicator { background: #a855f7; }
         /* ==================== CELL EDITING ==================== */
         td[contenteditable] { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; min-width: 80px; max-width: 500px; min-height: 24px; }
         td[contenteditable]:focus { overflow: visible; text-overflow: clip; max-width: none; }
         td[contenteditable] div { display: inline; }
         td[contenteditable]:empty { min-height: 24px; }
         td[contenteditable]:hover:not(.edited) { background-color: #f3f4f6 !important; }
         .dark-theme td[contenteditable]:hover:not(.edited) { background-color: #374151 !important; }
         .pink-theme td[contenteditable]:hover:not(.edited) { background-color: #fce7f3 !important; }
         table { width: auto !important; min-width: 100%; }
      </style>
   </head>
   <body class="min-h-screen theme-transition">
      <script>
         // Get theme from server and localStorage, prioritize localStorage for persistence
         const serverTheme = '{{ theme }}';
         const savedTheme = localStorage.getItem('workbench-theme');
         const currentTheme = savedTheme || serverTheme || 'dark';

         // Apply theme without transition
         document.documentElement.className = currentTheme + '-theme';
         document.body.className = 'min-h-screen ' + currentTheme + '-theme';

         // Save to localStorage if not already saved
         if (!savedTheme) {
         localStorage.setItem('workbench-theme', currentTheme);
         }

         // Sync with server if localStorage theme differs from server theme
         if (savedTheme && savedTheme !== serverTheme) {
         fetch('/set-theme', {
         method: 'POST',
         headers: {
           'Content-Type': 'application/json',
         },
         body: JSON.stringify({theme: savedTheme})
         });
         }

         // Set theme dropdown value
         document.addEventListener('DOMContentLoaded', function() {
         const themeDropdown = document.getElementById('theme-select');
         if (themeDropdown) {
         themeDropdown.value = currentTheme;
         console.log('Theme dropdown set to:', currentTheme);
         }
         });

         // Theme change function
         function setTheme(theme) {
         // Apply theme immediately without transition
         document.documentElement.className = theme + '-theme';
         document.body.className = 'min-h-screen ' + theme + '-theme';
         

         localStorage.setItem('workbench-theme', theme);

         // Update dropdown
         const dropdown = document.getElementById('theme-select');
         if (dropdown) dropdown.value = theme;

         // Save to server
         fetch('/set-theme', {
         method: 'POST',
         headers: {
           'Content-Type': 'application/json',
         },
         body: JSON.stringify({theme: theme})
         }).then(response => response.json())
         .then(data => {
           console.log('Theme saved to server:', data);
         })
         .catch(error => {
           console.error('Error saving theme:', error);
         });
         }

         
      </script>
      <!-- Add padding container -->
      <div class="w-full min-h-screen main-container theme-transition p-8 csv-edit-page">
                   <!-- CSV EDIT PAGE HEADER -->
          <!-- Header: no title, just back link -->
          <div class="flex items-center justify-between mb-6">
             <div class="flex items-center space-x-3">
                <a href="{{ url_for('home') }}">
                   <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
                </a>
                <span id="edit-indicator" class="edit-indicator" style="display: none;"></span>
             </div>
            <!-- Right side: Big Time Display, Environment, and Theme Toggle -->
            <div class="flex items-center space-x-4">
               <div class="text-right" style="display: flex !important; justify-content: flex-end !important; align-items: center !important;">
                  <div class="big-time-display" style="margin-top: 0px;">
                     <div class="time-section" style="align-items: flex-end !important; justify-content: flex-end !important;">
                        <div class="big-time" style="font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important;">{{ big_time_display.big_time }}</div>
                        <div class="big-day-date" style="font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important;">{{ big_time_display.day_date }}</div>
                     </div>
                  </div>
               </div>
               <div class="theme-toggle">
                  <select id="theme-select" class="border px-4 py-2 text-base theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="setTheme(this.value)">
                     <option value="dark">🌃   Dark</option>
                     <option value="white">🔆  White</option>
   
                  </select>
               </div>
            </div>
         </div>
                   <form
             id="save-form"
             method="post"
             action="{{ url_for('download_csv') }}"
             onsubmit="return true;"
             class="space-y-4 w-full"
             >
                         <!-- S3 Path & Controls -->
             <div class="flex items-center space-x-2 mb-4">
                <div class="flex-1 flex items-center space-x-2">
                   <input
                      type="text"
                      id="public_url"
                      name="public_url"
                      value="{{ public_url if public_url else 'Local file: ' + filename }}"
                      class="flex-grow border px-4 py-2 text-base theme-transition"
                      style="height: 46px;"
                      placeholder="Enter S3 path or URL"
                      autocomplete="off"
                      readonly
                      />
                </div>
               <div class="flex items-center space-x-2">
                  <input
                     id="delimiter"
                     name="delimiter"
                     value="{{ escaped_delimiter }}"
                     class="border px-2 py-2 text-sm theme-transition"
                     style="height: 46px; width: 10ch;"
                     />
               </div>
               
               <!-- Encryption toggle button removed -->
                               <button
                   type="submit"
                   form="save-form"
                   class="btn btn-ghost"
                   title="Download modified file"
                   style="height: 46px;">
                Download
                </button>
               <style>
                  /* CSV Don't Encrypt hover/selected */
                  #csvDontEncryptToggleBtn { height: 46px; width: 46px; }
                  /* Hover grey on white theme (match Home) */
                  .white-theme #csvDontEncryptToggleBtn:hover:not(:disabled) {
                  background-color: #f1f5f9 !important;
                  border-color: #cbd5e1 !important;
                  }
                  /* Persist selected highlight across themes (match Home) */
                  #csvDontEncryptToggleBtn.selected,
                  .white-theme #csvDontEncryptToggleBtn.selected { background-color: rgba(0, 0, 0, 0.05) !important; border-color: rgba(0, 0, 0, 0.1) !important; }
                  .dark-theme #csvDontEncryptToggleBtn.selected { background-color: #334155 !important; border-color: #64748b !important; }
                  .pink-theme #csvDontEncryptToggleBtn.selected { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
               </style>
               <!-- stash originals so we always re-load from the same source -->
               <input type="hidden" name="orig_public_url"      value="{{ public_url }}" />
               <input type="hidden" name="detected_delimiter" value="{{ escaped_delimiter }}" />
            </div>
                         <!-- Hidden state -->
             <input type="hidden" name="file_type"  value="{{ file_type }}" />
             <input type="hidden" name="gzipped"    value="{{ gzipped }}" />
             <input type="hidden" name="page"       value="{{ page }}" />
             <input type="hidden" name="table_data" id="table_data" />
             <input type="hidden" name="all_edits" id="all_edits" />
             <input type="hidden" name="cache_key" value="{{ cache_key }}" />
             <input type="hidden" name="filename" value="{{ filename }}" />
         </form>

         
         <!-- Top Controls (Outside Form) -->
         <div class="flex items-center justify-between mb-4 space-x-2">
            <!-- Left: Record count -->
            <div class="btn btn-ghost text-lg record-info whitespace-nowrap flex items-center" style="height: 46px; cursor: default; pointer-events: none;">
               <span class="font-bold">{{ start_rec }}</span>&nbsp;–&nbsp;<span class="font-bold">{{ end_rec }}</span>&nbsp;of&nbsp;<span class="font-bold">{{ total_rows }}</span>
            </div>
            <!-- Center: Pagination controls (only show if more than one page) -->
            {% if page_count > 1 %}
            {% set max_visible_pages = 7 %}
            {% set window_threshold = 5 %}
            {# Calculate pagination window - STABLE VERSION #}
            {% if page_count <= max_visible_pages %}
            {# Show all pages if they fit #}
            {% set start_page = 1 %}
            {% set end_page = page_count %}
            {% else %}
            {# Stable window logic: only shift when near edges #}
            {% if page <= window_threshold %}
            {# Near start: always show pages 1-7 #}
            {% set start_page = 1 %}
            {% set end_page = max_visible_pages %}
            {% elif page > page_count - window_threshold %}
            {# Near end: always show last 7 pages #}
            {% set start_page = page_count - max_visible_pages + 1 %}
            {% set end_page = page_count %}
            {% else %}
            {# Middle: center window on current page #}
            {% set start_page = page - 3 %}
            {% set end_page = page + 3 %}
            {% endif %}
            {% endif %}
            <div class="flex items-center justify-end flex-1">
               <div class="flex items-center space-x-2">
                  {# Previous page #}
                  {% if page > 1 %}
                  <a href="{{ url_for('csv_page', page=page-1) }}" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center; text-decoration: none;">‹</a>
                  {% endif %}
                  {# First page if not in window #}
                  {% if start_page > 1 %}
                  <a href="{{ url_for('csv_page', page=1) }}" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center; text-decoration: none;">1</a>
                  {% if start_page > 2 %}
                  <span class="px-2 text-gray-500 flex items-center" style="height: 46px;">…</span>
                  {% endif %}
                  {% endif %}
                  {# Page numbers in window #}
                  {% for p in range(start_page, end_page + 1) %}
                  {% if p == page %}
                  <span class="btn btn-ghost page-btn active" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center;">{{ p }}</span>
                  {% else %}
                  <a href="{{ url_for('csv_page', page=p) }}" class="btn btn-ghost page-btn {% if p == page %}active{% endif %}" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center; text-decoration: none;">{{ p }}</a>
                  {% endif %}
                  {% endfor %}
                  {# Last page if not in window #}
                  {% if end_page < page_count %}
                  {% if end_page < page_count - 1 %}
                  <span class="px-2 text-gray-500 flex items-center" style="height: 46px;">…</span>
                  {% endif %}
                  <a href="{{ url_for('csv_page', page=page_count) }}" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center; text-decoration: none;">{{ page_count }}</a>
                  {% endif %}
                  {# Next page #}
                  {% if page < page_count %}
                  <a href="{{ url_for('csv_page', page=page+1) }}" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center; text-decoration: none;">›</a>
                  {% endif %}

               </div>
            </div>
            {% else %}
            <!-- Empty flex space when no pagination -->
            <div class="flex-1"></div>
            {% endif %}
            <!-- Back button (always visible) -->
            <div class="flex items-center">
               <a
                  href="{{ url_for('home') }}"
                  class="btn btn-ghost btn-icon"
                  title="Back to home"
                  style="height: 46px; width: 46px;"
                  >
               ←
               </a>
            </div>
         </div>
         <!-- Add space after pagination -->
         <div class="mb-6"></div>
         <!-- Editable table slice -->
         <div class="overflow-x-auto">
            <table class="w-full table-auto border-collapse text-sm">
               <thead class="bg-blue-50">
                  <tr>
                     {% for col in columns %}
                     <th
                        class="border border-gray-300 px-2 py-1 text-left whitespace-nowrap"
                        >
                        {{ col }}
                     </th>
                     {% endfor %}
                  </tr>
               </thead>
               <tbody id="tableBody">
                  {% for row_idx in range(data|length) %}
                  {% set global_row_idx = start + row_idx %}
                  <tr data-row="{{ global_row_idx }}">
                     {% for col_idx in range(columns|length) %}
                     {% set col = columns[col_idx] %}
                     {% set cell_key = global_row_idx ~ ',' ~ col_idx %}
                     {% set is_edited = cell_key in edits %}
                     {% set cell_value = data[row_idx].get(col, '')|replace('\r\n', ' ')|replace('\n', ' ')|replace('\r', ' ')|trim %}
                     <td contenteditable="true" 
                        class="border px-2 py-1 {% if is_edited %}edited{% endif %}"
                        data-row="{{ global_row_idx }}"
                        data-col="{{ col_idx }}"
                        data-original="{{ cell_value }}"
                        style="white-space: nowrap;">{% if is_edited %}{{ edits[cell_key]|replace('\r\n', ' ')|replace('\n', ' ')|replace('\r', ' ')|trim }}{% else %}{{ cell_value }}{% endif %}</td>
                     {% endfor %}
                  </tr>
                  {% endfor %}
               </tbody>
            </table>
         </div>
         </form>
         
         <!-- Hidden field for per_page -->
         <input type="hidden" id="per_page_hidden" value="{{ per_page }}" />
         
         
      </div>
      <script>
         // Cache key for this file
         const cacheKey = "{{ cache_key }}";
         console.log('CSV Editor loaded with cache key:', cacheKey);

         // Load existing edits from server-provided data
         const existingEdits = {{ edits_json | safe }};
         console.log('CSV Editor data:', {
             columns: {{ columns | tojson | safe }},
             data: {{ data | tojson | safe }},
             total_rows: {{ total_rows }},
             per_page: {{ per_page }},
             page_count: {{ page_count }}
         });
         
         // Function to handle pagination count changes (kept for compatibility)
         function updatePaginationCount(newPerPage) {
             // This function is now handled by the form submission
             fetch('/update-pagination', {
                 method: 'POST',
                 headers: {
                     'Content-Type': 'application/x-www-form-urlencoded',
                 },
                 body: new URLSearchParams({
                     'cache_key': cacheKey,
                     'per_page': newPerPage
                 })
             })
             .then(response => response.json())
             .then(data => {
                 if (data.success) {
                     // Update hidden field
                     document.getElementById('per_page_hidden').value = newPerPage;
                     // Reload current page with new pagination
                     const currentPage = getCurrentPage();
                     changePage(currentPage);
                 } else {
                     alert('Error updating pagination: ' + data.error);
                 }
             })
             .catch(error => {
                 console.error('Error:', error);
                 alert('Error updating pagination. Please try again.');
             });
         }

         // Excel-like keyboard navigation
         document.getElementById('tableBody').addEventListener('keydown', function(e) {
           if (e.target.tagName === 'TD') {
             const currentCell = e.target;
             const currentRow = currentCell.parentElement;
             const cellIndex = Array.from(currentRow.cells).indexOf(currentCell);
             const rows = currentRow.parentElement.children;
             const rowIndex = Array.from(rows).indexOf(currentRow);

             // Both Enter and Shift+Enter move to next cell (like Excel)
             if (e.key === 'Enter') {
               e.preventDefault();
               if (e.shiftKey) {
                 // Move up
                 if (rowIndex > 0) {
                   rows[rowIndex - 1].cells[cellIndex].focus();
                 }
               } else {
                 // Move down
                 if (rowIndex < rows.length - 1) {
                   rows[rowIndex + 1].cells[cellIndex].focus();
                 } else {
                   // If at last row, move to next cell in current row
                   if (cellIndex < currentRow.cells.length - 1) {
                     currentRow.cells[cellIndex + 1].focus();
                   }
                 }
               }
               return;
             }

             // Tab navigation
             if (e.key === 'Tab') {
               e.preventDefault();
               if (e.shiftKey) {
                 // Move left
                 if (cellIndex > 0) {
                   currentRow.cells[cellIndex - 1].focus();
                 }
               } else {
                 // Move right
                 if (cellIndex < currentRow.cells.length - 1) {
                   currentRow.cells[cellIndex + 1].focus();
                 }
               }
               return;
             }

             // Arrow keys
             if (e.key === 'ArrowUp' && rowIndex > 0) {
               e.preventDefault();
               rows[rowIndex - 1].cells[cellIndex].focus();
             }
             if (e.key === 'ArrowDown' && rowIndex < rows.length - 1) {
               e.preventDefault();
               rows[rowIndex + 1].cells[cellIndex].focus();
             }
             if (e.key === 'ArrowLeft' && cellIndex > 0 && window.getSelection().anchorOffset === 0) {
               e.preventDefault();
               currentRow.cells[cellIndex - 1].focus();
             }
             if (e.key === 'ArrowRight' && cellIndex < currentRow.cells.length - 1) {
               const selection = window.getSelection();
               if (selection.anchorOffset === currentCell.textContent.length) {
                 e.preventDefault();
                 currentRow.cells[cellIndex + 1].focus();
               }
             }
           }
         });
         
         // Prevent Enter key from creating newlines
         document.getElementById('tableBody').addEventListener('keypress', function(e) {
           if (e.target.tagName === 'TD' && e.key === 'Enter') {
             e.preventDefault();
           }
         });

         // Handle special key combinations
         document.getElementById('tableBody').addEventListener('keydown', function(e) {
           if (e.target.tagName === 'TD') {
             // Handle Cmd+A or Ctrl+A followed by delete/backspace
             if ((e.key === 'Backspace' || e.key === 'Delete') && 
                 (e.metaKey || e.ctrlKey || window.getSelection().toString() === e.target.textContent)) {
               // Clear the cell completely
               setTimeout(() => {
                 if (e.target.textContent === '' || !e.target.textContent.trim()) {
                   e.target.innerHTML = '';
                   e.target.textContent = '';
                 }
               }, 0);
             }
           }
         });

         // Track cell edits with input event listener
         document.getElementById('tableBody').addEventListener('input', function(e) {
           if (e.target.tagName === 'TD') {
             const row = e.target.dataset.row;
             const col = e.target.dataset.col;
             const original = e.target.dataset.original;
             let current = e.target.textContent;

             // Remove any newlines that might have snuck in
             if (current.includes('\n') || current.includes('\r')) {
               current = current.replace(/[\r\n]+/g, ' ').trim();
               e.target.textContent = current;
             }

             // Fix empty cell issues - if cell is empty or just whitespace, clear it completely
             if (!current.trim()) {
               e.target.textContent = '';
               current = '';
             }

             const key = `${row},${col}`;

             if (current !== original) {
               existingEdits[key] = current;
               e.target.classList.add('edited');
             } else {
               delete existingEdits[key];
               e.target.classList.remove('edited');
             }

             updateEditCount();

             // Send update to server
             fetch('/update-csv-edit', {
               method: 'POST',
               headers: {
                 'Content-Type': 'application/json',
               },
               body: JSON.stringify({
                 cache_key: cacheKey,
                 edits: existingEdits
               })
             });
           }
         });
         
         // Update edit count indicator
         function updateEditCount() {
           const count = Object.keys(existingEdits).length;
           const indicator = document.getElementById('edit-indicator');

           if (count > 0) {
             indicator.textContent = `${count} edit${count !== 1 ? 's' : ''}`;
             indicator.style.display = 'inline';
           } else {
             indicator.style.display = 'none';
           }
         }

         // Clean up any empty cells on blur
         document.getElementById('tableBody').addEventListener('blur', function(e) {
           if (e.target.tagName === 'TD') {
             // If cell is empty or just whitespace, clear it completely
             if (!e.target.textContent.trim()) {
               e.target.innerHTML = '';
               e.target.textContent = '';
             }
           }
         }, true);

         // Handle paste to clean up formatting and remove newlines
         document.getElementById('tableBody').addEventListener('paste', function(e) {
           if (e.target.tagName === 'TD') {
             e.preventDefault();
             const text = (e.clipboardData || window.clipboardData).getData('text');
             // Replace all newlines with spaces
             const cleanText = text.replace(/[\r\n]+/g, ' ').trim();
             document.execCommand('insertText', false, cleanText);
           }
         });

         // Position cursor at end of text on focus
         document.getElementById('tableBody').addEventListener('focus', function(e) {
           if (e.target.tagName === 'TD') {
             setTimeout(() => {
               const cell = e.target;
               const range = document.createRange();
               const sel = window.getSelection();

               // Position cursor at the end of the text
               if (cell.textContent.length > 0) {
                 range.setStart(cell.firstChild || cell, cell.textContent.length);
                 range.setEnd(cell.firstChild || cell, cell.textContent.length);
               } else {
                 range.selectNodeContents(cell);
                 range.collapse(true);
               }

               sel.removeAllRanges();
               sel.addRange(range);
             }, 0);
           }
         }, true);
         
         // Update edit count indicator
         function updateEditCount() {
           const count = Object.keys(existingEdits).length;
           const indicator = document.getElementById('edit-indicator');

           if (count > 0) {
             indicator.textContent = `${count} edit${count !== 1 ? 's' : ''}`;
             indicator.style.display = 'inline';
           } else {
             indicator.style.display = 'none';
           }
         }

         // Initialize edit count on page load
         document.addEventListener('DOMContentLoaded', function() {
           updateEditCount();
         });

      </script>
      <script>

                   function submitData(form) {
            // Include all edits from all pages
            form.querySelector('#all_edits').value = JSON.stringify(existingEdits);

            // For backward compatibility, also include current page data
            const rows = form.querySelectorAll('#tableBody tr');
            const headers = Array.from(form.querySelectorAll('thead th')).map(th => th.innerText.trim());
            const data = [];
            rows.forEach(tr => {
              const cells = tr.querySelectorAll('td');
              const obj = {};
              headers.forEach((h,i) => {
                // Use textContent and remove any newlines
                obj[h] = cells[i].textContent.replace(/[\r\n]+/g, ' ').trim();
              });
              data.push(obj);
            });
            form.querySelector('#table_data').value = JSON.stringify(data);

            return true;
          }
      </script>
      <script>
         document.getElementById('save-form').addEventListener('submit', function(e) {
           const path = document.getElementById('s3_path').value.trim();
           // must start with s3://
           const s3Prefix = /^s3:\/\//i;
           // must end in .csv, .json, .jsonl or .csv.gz (case-insensitive)
           const validExt  = /\.(?:csv|json|jsonl|csv\.gz)$/i;

           if (!s3Prefix.test(path) || !validExt.test(path)) {
             e.preventDefault();
             showModalMessage('Save', 'Please provide a valid S3 path (e.g. s3://my-bucket/path/to/file.csv) with one of these extensions: .csv, .json, .jsonl, .csv.gz');
           }
         });
      </script>
      <script>
         // Toggle CSV don't encrypt preference
           function toggleCsvDontEncrypt() {
             const btn = document.getElementById('csvDontEncryptToggleBtn');
             if (btn) {
               const isCurrentlyEnabled = btn.classList.contains('selected');
               const newState = !isCurrentlyEnabled;

               if (newState) {
                 btn.classList.add('selected');
               } else {
                 btn.classList.remove('selected');
               }

               // Update hidden field for form submission
               updateCsvDontEncryptHiddenField();
             }
           }

           // Update hidden field for CSV don't encrypt
           function updateCsvDontEncryptHiddenField() {
             const btn = document.getElementById('csvDontEncryptToggleBtn');
             const form = document.getElementById('save-form');
             if (btn && form) {
               const isEnabled = btn.classList.contains('selected');

               // Remove existing dont_encrypt input if any
               const existingInput = form.querySelector('input[name="dont_encrypt"]');
               if (existingInput) {
                 existingInput.remove();
               }

               // Add hidden input if encryption is disabled (value = true means don't encrypt)
               if (isEnabled) {
                 const hiddenInput = document.createElement('input');
                 hiddenInput.type = 'hidden';
                 hiddenInput.name = 'dont_encrypt';
                 hiddenInput.value = 'true';
                 form.appendChild(hiddenInput);
               }
             }
           }

           // Update hidden field before form submission
           document.getElementById('save-form').addEventListener('submit', function() {
             updateCsvDontEncryptHiddenField();
           });

           // Pagination function
           function changePage(page) {
             // Save current page edits before changing pages
             saveCurrentPageEdits();
             
             // Show loading indicator
             const recordInfo = document.querySelector('.record-info');
             if (recordInfo) {
               recordInfo.innerHTML = '<span class="text-gray-500">Loading page ' + page + '...</span>';
             }

             // Call the CSV page endpoint
             fetch('/csv-page', {
               method: 'POST',
               headers: {
                 'Content-Type': 'application/x-www-form-urlencoded',
               },
               body: new URLSearchParams({
                 'page': page,
                 'cache_key': '{{ cache_key }}',
                 'public_url': '{{ public_url }}'
               })
             })
             .then(response => response.json())
             .then(data => {
               if (data.success) {
                 // Update the table with new data
                 updateTableWithData(data.data);
                 
                 // Update pagination info
                 if (recordInfo) {
                   recordInfo.innerHTML = '<span class="font-bold">' + data.start_rec + '</span>&nbsp;–&nbsp;<span class="font-bold">' + data.end_rec + '</span>&nbsp;of&nbsp;<span class="font-bold">' + data.total_rows + '</span>';
                 }
                 
                 // Update current page indicator
                 updatePaginationButtons(page, data.page_count);
                 
                 // Update URL without page reload
                 const url = new URL(window.location);
                 url.searchParams.set('page', page);
                 window.history.pushState({}, '', url);
               } else {
                 alert('Error loading page: ' + data.error);
               }
             })
             .catch(error => {
               console.error('Error:', error);
               alert('Error loading page. Please try again.');
             });
           }

           // Function to save edits from current page
           function saveCurrentPageEdits() {
             const tbody = document.getElementById('tableBody');
             if (!tbody) return;
             
             const rows = tbody.querySelectorAll('tr');
             const headers = Array.from(document.querySelectorAll('thead th')).map(th => th.textContent.trim());
             
             rows.forEach((tr, rowIndex) => {
               const cells = tr.querySelectorAll('td');
               cells.forEach((cell, colIndex) => {
                 if (cell.classList.contains('edited')) {
                   const header = headers[colIndex];
                   const originalValue = cell.getAttribute('data-original') || cell.textContent;
                   const currentValue = cell.textContent.trim();
                   
                   if (currentValue !== originalValue) {
                     // Calculate global row index based on current page
                     const currentPage = getCurrentPage();
                     const perPage = {{ per_page }};
                     const globalRowIndex = (currentPage - 1) * perPage + rowIndex;
                     
                     if (!existingEdits[globalRowIndex]) existingEdits[globalRowIndex] = {};
                     existingEdits[globalRowIndex][header] = currentValue;
                   }
                 }
               });
             });
           }

           // Function to get current page number
           function getCurrentPage() {
             const urlParams = new URLSearchParams(window.location.search);
             return parseInt(urlParams.get('page')) || 1;
           }

           // Function to update table with new data
           function updateTableWithData(data) {
             const tbody = document.getElementById('tableBody');
             if (!tbody) return;

             // Clear existing rows
             tbody.innerHTML = '';

             // Add new rows
             data.forEach((row, localRowIndex) => {
               const tr = document.createElement('tr');
               const headers = Array.from(document.querySelectorAll('thead th')).map(th => th.textContent.trim());
               
               headers.forEach((header, colIndex) => {
                 const td = document.createElement('td');
                 td.contentEditable = true;
                 
                 // Get the value, checking for edits first
                 const currentPage = getCurrentPage();
                 const perPage = {{ per_page }};
                 const globalRowIndex = (currentPage - 1) * perPage + localRowIndex;
                 
                 let value = row[header] || '';
                 
                 // Check if there's an edit for this cell
                 if (existingEdits[globalRowIndex] && existingEdits[globalRowIndex][header]) {
                   value = existingEdits[globalRowIndex][header];
                   td.classList.add('edited');
                 }
                 
                 // Store original value for comparison
                 td.setAttribute('data-original', row[header] || '');
                 td.textContent = value;
                 
                 td.addEventListener('blur', function() {
                   // Handle cell editing
                   const currentValue = td.textContent.trim();
                   const originalValue = td.getAttribute('data-original') || '';
                   
                   if (currentValue !== originalValue) {
                     if (!existingEdits[globalRowIndex]) existingEdits[globalRowIndex] = {};
                     existingEdits[globalRowIndex][header] = currentValue;
                     td.classList.add('edited');
                   } else {
                     td.classList.remove('edited');
                     if (existingEdits[globalRowIndex]) {
                       delete existingEdits[globalRowIndex][header];
                       if (Object.keys(existingEdits[globalRowIndex]).length === 0) {
                         delete existingEdits[globalRowIndex];
                       }
                     }
                   }
                 });
                 
                 tr.appendChild(td);
               });
               tbody.appendChild(tr);
             });
           }

           // Function to update pagination buttons
           function updatePaginationButtons(currentPage, totalPages) {
             const pageButtons = document.querySelectorAll('.page-btn');
             pageButtons.forEach(btn => {
               if (btn.textContent.trim() === currentPage.toString()) {
                 btn.classList.add('active');
                 btn.disabled = true;
               } else {
                 btn.classList.remove('active');
                 btn.disabled = false;
               }
             });
           }
      </script>
   </body>
</html>
"""

# Raw editor HTML template matching workbench.py Monaco editor styling
RAW_EDIT_HTML = r"""
<!doctype html>
<html>
   <head>
      <title>WorkBench</title>
      <!-- Immediate background before any content loads -->
      <script>
         // Apply theme immediately before any content loads
         (function() {
           const savedTheme = localStorage.getItem('workbench-theme') || 'dark';
           document.documentElement.className = savedTheme + '-theme';

           // Set appropriate background color based on theme
           const style = document.createElement('style');
           style.id = 'preload-theme';
           if (savedTheme === 'white') {
             style.textContent = 'html, body { background-color: #f8fafc !important; }';
           } else if (savedTheme === 'pink') {
             style.textContent = 'html, body { background-color: #fdf2f8 !important; }';
           } else {
             style.textContent = 'html, body { background-color: #1e293b !important; }';
           }
           document.head.appendChild(style);
         })();
      </script>
      <script src="https://cdn.tailwindcss.com"></script>
      <script>
         window.MonacoEnvironment = {
           getWorkerUrl: function (moduleId, label) {
             return 'data:text/javascript;charset=utf-8,' + encodeURIComponent(
               "self.MonacoEnvironment={baseUrl:'https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/'};importScripts('https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs/base/worker/workerMain.js');"
             );
           }
         };
      </script>
      <script src="https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs/loader.js"></script>
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs/editor/editor.main.css">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs/base/browser/ui/codicons/codicon/codicon.css">
      <link rel="preconnect" href="https://fonts.googleapis.com">
      <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
      <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&display=swap" rel="stylesheet">
      <link href="https://fonts.googleapis.com/css2?family=Ubuntu+Mono:wght@400;700&display=swap" rel="stylesheet">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/fira-code@5.0.18/400.css">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/cascadia-code@5.0.7/400.css">
      <style>
         /* ==================== BASE STYLES ==================== */
         * { font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif !important; }
         /* ==================== COMMON STYLES ==================== */
         .module-badge { border-radius: 0; border: 1px solid; font-weight: 600; font-size: 14px; min-width: 60px; text-align: center; }
         .greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; }
         p.greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; }
         .witty-message { font-weight: 400 !important; font-size: 0.875rem !important; margin-top: 0.25rem !important; opacity: 0.8; }
         .hidden-field { display: none !important; }
         /* ==================== DARK THEME ==================== */
         body.dark-theme { background-color: #1e293b !important; color: #e2e8f0 !important; }
         .dark-theme input[type="text"], .dark-theme select { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
         .dark-theme input:focus, .dark-theme select:focus { outline: none !important; border-color: #475569 !important; box-shadow: none !important; }
         .dark-theme #editor { border-color: #334155; background-color: #1e1e1e !important; }
         .dark-theme .btn-primary { background-color: #6366f1 !important; }
         .dark-theme .btn-primary:hover:not(:disabled) { background-color: #4f46e5 !important; }
         .dark-theme .btn-secondary { background-color: #475569 !important; }
         .dark-theme .btn-secondary:hover:not(:disabled) { background-color: #334155 !important; }
         .dark-theme .btn-ghost { background-color: transparent !important; color: #94a3b8 !important; border-color: #475569 !important; }
         .dark-theme .btn-ghost:hover:not(:disabled) { background-color: #334155 !important; border-color: #64748b !important; }
         .dark-theme .module-badge { background-color: #374151 !important; color: #e0e7ff !important; border-color: #4b5563 !important; }
         .dark-theme .greeting-text { color: #94a3b8 !important; }
         .dark-theme .witty-message { color: #cbd5e1 !important; }
         .dark-theme #terminal-modal .modal-content { background-color: #1e293b; color: #e2e8f0; border-color: #334155; }
         .dark-theme #terminal-modal .modal-header, .dark-theme #terminal-modal .modal-footer { border-color: #334155; }
         /* ==================== WHITE THEME ==================== */
         body.white-theme { background-color: #f1f5f9 !important; color: #1e293b !important; }
         .white-theme input[type="text"], .white-theme select { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
         .white-theme input:focus, .white-theme select:focus { outline: none !important; border-color: #e2e8f0 !important; box-shadow: none !important; }
         .white-theme #editor { border-color: #e2e8f0; background-color: #ffffff !important; }
         .white-theme .btn-ghost { border-color: #e2e8f0 !important; color: #64748b !important; }
         .white-theme .btn-ghost:hover:not(:disabled) { background-color: #f8fafc !important; border-color: #cbd5e1 !important; }
         .white-theme .module-badge { background-color: #ffffff !important; color: #1e40af !important; border-color: #d1d5db !important; }
         .white-theme .greeting-text { color: #64748b !important; }
         .white-theme .witty-message { color: #64748b !important; }
         .white-theme .main-container { background-color: #f8fafc !important; color: #1e293b !important; border-radius: 0; }
         .white-theme #public_url { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
         .white-theme #code-run-button { border: 1px solid #e2e8f0 !important; }
         /* ==================== PINK THEME ==================== */
         body.pink-theme { background-color: #fdf2f8 !important; color: #831843 !important; }
         .pink-theme input[type="text"], .pink-theme select { background-color: #fce7f3 !important; color: #831843 !important; border-color: #fbcfe8 !important; }
         .pink-theme input:focus, .pink-theme select:focus { outline: none !important; border-color: #fbcfe8 !important; box-shadow: none !important; }
         .pink-theme #editor { border-color: #f9a8d4; background-color: #fdf2f8 !important; }
         .pink-theme .btn-primary { background-color: #ec4899 !important; }
         .pink-theme .btn-primary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-success { background-color: #db2777 !important; color: #ffffff !important; }
         .pink-theme .btn-success:hover:not(:disabled) { background-color: #be185d !important; }
         .pink-theme .btn-secondary { background-color: #ec4899 !important; color: #ffffff !important; }
         .pink-theme .btn-secondary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-ghost { color: #be185d !important; border-color: #fbcfe8 !important; }
         .pink-theme .btn-ghost:hover:not(:disabled) { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
         .pink-theme .module-badge { background-color: #fdf2f8 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         .pink-theme .greeting-text { color: #be185d !important; }
         .pink-theme .witty-message { color: #db2777 !important; }
         /* Big Time Display Styling */
         .big-time-display { display: flex; flex-direction: row; justify-content: flex-end; align-items: center; margin-bottom: 0.5rem; }
         .time-section { text-align: right; height: 46px !important; display: flex !important; flex-direction: column !important; justify-content: center !important; align-items: flex-end !important; } }
         .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; margin-bottom: 0.125rem !important; }
         .big-day-date { font-size: 0.875rem !important; font-weight: 500 !important; color: #94a3b8 !important; line-height: 1.2 !important; }
         .dark-theme .big-greeting { color: #94a3b8 !important; }
         .dark-theme .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; }
         .dark-theme .big-day-date { color: #94a3b8 !important; }
         .white-theme .big-greeting { color: #64748b !important; }
         .white-theme .big-time { color: #1e293b !important; font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
         .white-theme .big-day-date { color: #64748b !important; font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }
         .pink-theme .big-greeting { color: #be185d !important; }
         .pink-theme .big-time { color: #831843 !important; font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
         .pink-theme .big-day-date { color: #be185d !important; font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }

         /* ==================== COMMON BUTTON STYLES ==================== */
         .btn { padding: 0.625rem 1.25rem; font-weight: 500; border-radius: 0; transition: all 0.2s ease; border: none; cursor: pointer; display: inline-flex; align-items: center; justify-content: center; gap: 0.5rem; font-size: 0.875rem; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); height: 46px; }
         .btn:hover { transform: translateY(-1px); box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06); }
         .btn:active { transform: translateY(0); box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
         .btn:disabled { opacity: 0.5; cursor: not-allowed; transform: none; box-shadow: none; }
         .btn-primary { background-color: #6366f1; color: white; }
         .btn-primary:hover:not(:disabled) { background-color: #4f46e5; }
         .btn-secondary { background-color: #64748b; color: white; }
         .btn-secondary:hover:not(:disabled) { background-color: #475569; }
         .btn-success { background-color: #10b981; color: white; }
         .btn-success:hover:not(:disabled) { background-color: #059669; }
         .btn-ghost { background-color: transparent; color: #64748b; box-shadow: none; border: 1px solid #e2e8f0; }
         .btn-ghost:hover:not(:disabled) { background-color: #f8fafc; border-color: #cbd5e1; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
         /* ==================== COMMON INPUT STYLES ==================== */
         input[type="text"], select { border-radius: 0; border: 1px solid #e2e8f0; padding: 0.625rem 1rem; font-size: 0.875rem; transition: all 0.2s ease; }
         input[type="text"]:focus, select:focus { outline: none; border-color: inherit; box-shadow: none; }
         .theme-select { border: 1px solid #d1d5db; padding: 8px 12px; height: 40px; }
         /* ==================== EDITOR STYLES ==================== */
         #editor { width: 100%; height: 70vh; border: 1px solid #e2e8f0; font-family: Consolas, "Liberation Mono", "Courier New", ui-monospace, SFMono-Regular, Menlo, Monaco, monospace !important; font-size: 14px !important; line-height: 1.6 !important; }
         .monaco-editor .codicon, .codicon { font: normal normal normal 16px/1 codicon !important; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale; }
         .monaco-editor, .monaco-editor *:not(.codicon) { font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace !important; font-variant-ligatures: contextual; }
         .monaco-editor .glyph-margin, .monaco-editor .folding, .monaco-editor .margin-view-overlays { font-family: codicon !important; }
      </style>
   </head>
   <body class="min-h-screen">
      <script>
         // Set dark theme by default
         document.documentElement.className = 'dark-theme';
         document.body.className = 'min-h-screen dark-theme';
         
  
      </script>
      <div class="w-full min-h-screen main-container theme-transition p-8">
         <!-- Header Section - Simplified -->
         <div class="flex items-center justify-between mb-6">
            <div class="flex items-center space-x-3">
               <a href="{{ url_for('home') }}">
                  <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
               </a>
            </div>
            <!-- Right side: Theme selector -->
            <div class="flex items-center space-x-4">
               <!-- Theme Selector -->
               <div class="flex items-center space-x-2">
                  <select id="theme-select" class="theme-select" onchange="changeTheme(this.value)" style="height: 40px;">
                     <option value="dark">🌃 Dark</option>
                     <option value="white">🔆 White</option>
                  </select>
               </div>
            </div>
         </div>
         
         <!-- File Path Input Section with Controls -->
         <div class="mb-4">
            <div class="flex items-center space-x-2">
               <input 
                  type="text" 
                  id="file-path-input" 
                  name="file_path" 
                  value="{{ actual_file_path if actual_file_path else '' }}"
                  placeholder="Enter file path or URL"
                  class="flex-1 border px-4 py-2 text-base theme-transition"
                  style="height: 46px;"
                  readonly>
               <a
                  href="{{ url_for('home') }}"
                  class="btn btn-ghost btn-icon"
                  title="Back to home"
                  style="height: 46px; width: 46px; padding: 0; font-size: 14px;">
               ←
               </a>
               <button type="button" id="fullscreen-btn" class="btn btn-ghost btn-icon" title="Fullscreen" aria-label="Fullscreen" style="display:inline-flex;align-items:center;justify-content:center;width:46px;height:46px;padding:0;">
                  <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                     <polyline points="15 3 21 3 21 9"></polyline>
                     <polyline points="9 21 3 21 3 15"></polyline>
                     <line x1="21" y1="3" x2="14" y2="10"></line>
                     <line x1="3" y1="21" x2="10" y2="14"></line>
                  </svg>
               </button>
               <button
                  type="button"
                  id="download-btn"
                  class="btn btn-ghost"
                  title="Download file content"
                  style="height: 46px;"
                  onclick="downloadContent()">
               Download
               </button>
            </div>
         </div>
         <!-- Code Editor Section -->
         <textarea id="code_text" name="code_text" class="hidden-field">{{ code_text | safe }}</textarea>
         <div class="bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 mb-4">
            <div id="editor" style="height: 75vh; min-height: 500px; width: 100%; font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, 'Liberation Mono', 'Courier New', monospace !important; background: transparent; color: inherit; position: relative;">
            </div>
         </div>
      </div>
      <script>
         // Define before any use
         const USE_PLAIN_EDITOR = false;
         
         // Theme switching function
         function changeTheme(theme) {
           if (!theme) return;
          
           // Save theme preference
           localStorage.setItem('workbench-theme', theme);
          
           // Remove existing theme classes
           document.documentElement.classList.remove('dark-theme', 'white-theme');
           document.body.classList.remove('dark-theme', 'white-theme');
          
           // Add the selected theme class
           if (theme === 'white') {
               document.documentElement.classList.add('white-theme');
               document.body.classList.add('white-theme');
           } else {
               document.documentElement.classList.add('dark-theme');
               document.body.classList.add('dark-theme');
           }
           
           // Add new theme class
           document.documentElement.classList.add(theme + '-theme');
           document.body.classList.add(theme + '-theme');
           
           // Save to localStorage
           localStorage.setItem('workbench-theme', theme);
           
           // Update Monaco editor theme if available
           if (window.monaco && editor) {
             if (theme === 'white') {
               monaco.editor.setTheme('vs');
             } else {
               monaco.editor.setTheme('vs-dark');
             }
           }
         }

         // Download content function
         function downloadContent() {
           let content = '';
           if (window.monaco && editor) {
             content = editor.getValue();
           } else {
             content = document.getElementById('code_text').value;
           }
           
           // Create blob and download
           const blob = new Blob([content], { type: 'text/plain' });
           const url = window.URL.createObjectURL(blob);
           const a = document.createElement('a');
           a.href = url;
           a.download = 'workbench_file.txt';
           document.body.appendChild(a);
           a.click();
           document.body.removeChild(a);
           window.URL.revokeObjectURL(url);
         }

         // Show loading overlay for code editor
         function showCodeLoadingOverlay() {
           if (document.getElementById('code-loading-overlay')) return;
           const overlay = document.createElement('div');
           overlay.id = 'code-loading-overlay';
           overlay.style.cssText = `position: fixed; top:0; left:0; width:100%; height:100%; background: rgba(0,0,0,0.3); backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px); display:flex; justify-content:center; align-items:center; z-index:9999;`;
           overlay.innerHTML = `
             <div style="text-align:center;">
               <div style="color:white; font-size:18px; font-weight:600; margin-bottom:20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">LOADING</div>
               <div style="width:800px; height:5px; background-color:#334155; overflow:hidden; position:relative; margin:0 auto;">
                 <div style="position:absolute; top:0; left:0; width:30%; height:100%; background-color:#6366f1; animation: loading-bar 1.5s ease-in-out infinite;"></div>
               </div>
               <style>
                 @keyframes loading-bar { 0% { left:-30%; } 100% { left:100%; } }
               </style>
             </div>`;
           document.body.appendChild(overlay);
           setTimeout(() => { const el = document.getElementById('code-loading-overlay'); if (el) el.remove(); }, 10000);
         }

         // Show saving overlay (copied pattern from JSON editor)
         function showCodeSaveLoaderAndRedirect() {
           if (document.getElementById('code-save-loader')) return;
           const currentTheme = document.body.className;
           let progressColor = '#6366f1';
           let backgroundColor = '#334155';
           if (currentTheme.includes('pink-theme')) {
             progressColor = '#ec4899';
             backgroundColor = '#fbcfe8';
           } else if (currentTheme.includes('white-theme')) {
             progressColor = '#6366f1';
             backgroundColor = '#e2e8f0';
           }
           const loader = document.createElement('div');
           loader.id = 'code-save-loader';
           loader.style.cssText = `
             position: fixed; top: 0; left: 0; width: 100%; height: 100%;
             background: rgba(0,0,0,0.3); backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px);
             display: flex; justify-content: center; align-items: center; z-index: 9999; font-family: 'Inter', sans-serif;`;
           loader.innerHTML = `
             <div style="text-align: center;">
               <div id="code-save-loader-text" style="color: white; font-size: 18px; font-weight: 600; margin-bottom: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">PREPARING DATA</div>
               <div style="width: 800px; height: 5px; background-color: ${backgroundColor}; border-radius: 0px; overflow: hidden; position: relative; margin: 0 auto;">
                 <div id="code-save-progress-bar" style="position: absolute; top: 0; left: 0; width: 0%; height: 100%; background-color: ${progressColor}; transition: width 0.3s ease; border-radius: 0px;"></div>
               </div>
               <div style="font-size: 24px; font-weight: 800; color: white; margin-top: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;" id="code-save-progress-text">0%</div>
             </div>`;
           document.body.appendChild(loader);
           let progress = 0;
           const steps = [
             { text: 'PREPARING TO SAVE', target: 20 },
             { text: 'VALIDATING FILE', target: 35 },
             { text: 'UPLOADING TO S3', target: 80 },
             { text: 'SAVED', target: 100 }
           ];
           let stepIndex = 0;
           const stepInterval = setInterval(() => {
             if (stepIndex < steps.length) {
               const step = steps[stepIndex];
               document.getElementById('code-save-loader-text').textContent = step.text;
               const progressInterval = setInterval(() => {
                 progress += 2;
                 if (progress >= step.target) { progress = step.target; clearInterval(progressInterval); }
                 document.getElementById('code-save-progress-bar').style.width = progress + '%';
                 document.getElementById('code-save-progress-text').textContent = progress + '%';
               }, 50);
               stepIndex++;
               if (stepIndex === steps.length) {
                 setTimeout(() => { /* let redirect from server handle nav */ }, 1200);
               }
             }
           }, 700);
         }

         function handleCodeSaveSubmit(e) {
           if (e && e.preventDefault) e.preventDefault();
           const btn = document.getElementById('code-save-button');
           if (btn) { btn.disabled = true; btn.textContent = 'Saving...'; }
           try {
             // Show progress animation
             showCodeSaveLoaderAndRedirect();

             // Update hidden public_url field with current visible value
             const visiblePublicUrl = document.getElementById('public_url').value;
             const codeForm = document.getElementById('code-save-form');
             const hiddenPublicUrl = codeForm ? codeForm.querySelector('input[name="public_url"]') : null;
             if (hiddenPublicUrl) {
               hiddenPublicUrl.value = visiblePublicUrl;
             }

             const hidden = document.getElementById('code_text');
             const value = (typeof editor !== 'undefined' && editor) ? editor.getValue() : hidden.value;
             hidden.value = (value || '').replace(/\r\n/g, '\n').replace(/\r/g, '\n');

             // Simple form submit - no chunking
             document.getElementById('code-save-form').submit();
           } catch (err) {
             console.error('Save submit failed', err);
             if (btn) { btn.disabled = false; btn.textContent = 'Save'; }
           }
           return false;
         }

         let editor;
         (function(){
           const themeDropdown = document.getElementById('theme-select');
           let currentTheme = localStorage.getItem('workbench-theme');
           if (!currentTheme) {
               currentTheme = 'dark';
               localStorage.setItem('workbench-theme', currentTheme);
           }
           if (themeDropdown) themeDropdown.value = currentTheme;
           
           // Apply initial theme
           changeTheme(currentTheme);
           
           // Add event listener for theme changes
           if (themeDropdown) {
               themeDropdown.addEventListener('change', function() {
                   changeTheme(this.value);
               });
           }

           // Clean any accidental quotes around inputs
           const publicUrlEl = document.getElementById('public_url');
           if (publicUrlEl) publicUrlEl.value = stripOuterQuotes(publicUrlEl.value || '');

           // Sync hidden public_url field with visible field on any change
           if (publicUrlEl) {
             publicUrlEl.addEventListener('input', function() {
               const codeForm = document.getElementById('code-save-form');
               const hiddenPublicUrl = codeForm ? codeForm.querySelector('input[name="public_url"]') : null;
               console.log('Input Event - Visible value:', this.value);
               console.log('Input Event - Code form found:', !!codeForm);
               console.log('Input Event - Hidden field found:', !!hiddenPublicUrl);
               if (hiddenS3Path) {
                 console.log('Input Event - Hidden field old value:', hiddenS3Path.value);
                 hiddenS3Path.value = this.value;
                 console.log('Input Event - Hidden field new value:', hiddenS3Path.value);
               }
             });
             s3PathEl.addEventListener('change', function() {
               const codeForm = document.getElementById('code-save-form');
               const hiddenS3Path = codeForm ? codeForm.querySelector('input[name="s3_path"]') : null;
               console.log('Change Event - Visible value:', this.value);
               console.log('Change Event - Code form found:', !!codeForm);
               console.log('Change Event - Hidden field found:', !!hiddenS3Path);
               if (hiddenS3Path) {
                 console.log('Change Event - Hidden field old value:', hiddenS3Path.value);
                 hiddenS3Path.value = this.value;
                 console.log('Change Event - Hidden field new value:', hiddenS3Path.value);
               }
             });
           }





           // Module change handler
           function updateModule(module) {
             console.log('Setting module to:', module);
             // Update hidden field in form
             const codeForm = document.getElementById('code-save-form');
             const hiddenModuleField = codeForm ? codeForm.querySelector('input[name="module"]') : null;
             if (hiddenModuleField) {
               hiddenModuleField.value = module;
             }

             // Save to server session
             fetch('/set-module', {
               method: 'POST',
               headers: {
                 'Content-Type': 'application/json',
               },
               body: JSON.stringify({module: module})
             }).then(response => response.json())
               .then(data => {
                 console.log('Module saved to server:', data);
               })
               .catch(error => {
                 console.error('Error saving module:', error);
               });
           }

           // Initialize Monaco editor
           function initializeEditor() {
             try {
               console.log('Initializing Monaco Editor...');
               const editorDivEl = document.getElementById('editor');
               if (!editorDivEl) return;



               // Use the actual file path passed from server for detection
               const actualFilePath = '{{ actual_file_path }}';
               let detectedLang = inferLangFromPath(actualFilePath);
               const initialContent = document.getElementById('code_text').value || '';
               // Guess language for extensionless paths (prefer Python)
               if (!/\.[a-z0-9]+(\.|$)/i.test(actualFilePath)) {
                 const sample = (initialContent || '').slice(0, 50000);
                 if (/^\s*(from |import |def |class |if __name__ == ['\"]__main__['\"]:)/m.test(sample)) detectedLang = 'python';
                 else if (/<(html|head|body|script|style)/i.test(sample)) detectedLang = 'html';
                 else if (/\b(function|const|let|=>)\b/.test(sample)) detectedLang = 'javascript';
                 else if (/\b(SELECT|INSERT|UPDATE|DELETE|CREATE|ALTER|DROP|WITH)\b/i.test(sample)) detectedLang = 'sql';
                 else if (/^\s*#!/.test(sample)) detectedLang = 'sh';
               }
                            // Use fixed dark theme for Monaco editor
                            function applyDarkTheme(){
                   const themeId = 'workbench-dark-theme';
                   monaco.editor.defineTheme(themeId, {
                     base: 'vs-dark', inherit: true,
                     rules: [],
                     colors: {
                       'editor.background': '#1e293b',
                       'editor.foreground': '#e2e8f0',
                       'editorGutter.background': '#1e293b',
                       'editorLineNumber.foreground': '#94a3b8',
                       'editorLineNumber.activeForeground': '#ffffff',
                       'editor.selectionBackground': '#334155',
                       'editorIndentGuide.background': '#334155',
                       'editorIndentGuide.activeBackground': '#64748b'
                     }
                   });
                   monaco.editor.setTheme(themeId);
                   return themeId;
                 }

                 // Load Monaco
                 require.config({ paths: { 'vs': 'https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs' } });
                 require(['vs/editor/editor.main'], function() {
                   const themeId = applyDarkTheme();
                   editor = monaco.editor.create(editorDivEl, {
                   value: initialContent,
                   language: mapToMonacoLang(detectedLang),
                   theme: 'workbench-dark-theme',
                   automaticLayout: true,
                   minimap: { enabled: false },
                   scrollBeyondLastLine: false,
                   wordWrap: 'on',
                   fontSize: 14,
                   fontLigatures: true,
                   fontFamily: "'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace",
                   tabSize: 4,
                   insertSpaces: true,
                   renderWhitespace: 'boundary',
                   cursorBlinking: 'solid',
                   cursorStyle: 'line',
                   smoothScrolling: true,
                   mouseWheelZoom: false,
                   roundedSelection: false,
                   renderLineHighlight: 'gutter',
                   lineDecorationsWidth: 16,
                   glyphMargin: true,
                   folding: true,
                   foldingHighlight: true,
                   showFoldingControls: 'always'
                 });

                                // Ensure Monaco editor is positioned correctly and starts invisible
                  const monacoContainer = editor.getContainerDomNode();
                  monacoContainer.style.position = 'relative';
                  monacoContainer.style.zIndex = '2';
                  monacoContainer.style.opacity = '0';
                  monacoContainer.style.transition = 'opacity 0.3s ease';

                  // Fade in Monaco editor
                  setTimeout(() => {
                    monacoContainer.style.opacity = '1';
                  }, 50);
                 editor.updateOptions({ fontFamily: "'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace"});
                 try { monaco.editor.remeasureFonts(); } catch(e) {}



                 // Sync hidden textarea on change
                 document.getElementById('code_text').value = editor.getValue().replace(/\r\n/g,'\n').replace(/\r/g,'\n');
                 editor.getModel().onDidChangeContent(function(){
                   document.getElementById('code_text').value = editor.getValue().replace(/\r\n/g,'\n').replace(/\r/g,'\n');
                 });

                 // Save shortcut - removed since no save functionality
                 // editor.addCommand(monaco.KeyMod.CtrlCmd | monaco.KeyCode.KeyS, function(){
                 //   try { document.getElementById('code-save-form').dispatchEvent(new Event('submit', {cancelable:true})); }
                 //   catch(e) { handleCodeSaveSubmit(e); }
                 // });

                 // Focus editor
                 editor.focus();
                             console.log('Monaco Editor setup complete');

               // Fullscreen toggle handlers
               const fsBtn = document.getElementById('fullscreen-btn');
               function enterFullscreen(){
                 const container = document.getElementById('editor');
                 container.requestFullscreen ? container.requestFullscreen() : (container.webkitRequestFullscreen && container.webkitRequestFullscreen());
                 setTimeout(() => editor.layout(), 100);
               }
               function exitFullscreen(){
                 document.exitFullscreen ? document.exitFullscreen() : (document.webkitExitFullscreen && document.webkitExitFullscreen());
                 setTimeout(() => editor.layout(), 100);
               }
               if (fsBtn) fsBtn.onclick = () => enterFullscreen();
               document.addEventListener('keydown', (e)=>{ if (e.key === 'Escape') { setTimeout(()=>editor.layout(), 50); }});
               document.addEventListener('fullscreenchange', ()=> setTimeout(()=>editor.layout(), 50));
             });

             } catch (error) {
               console.error('Error initializing Monaco Editor:', error);

             }
           }

           // Initialize after a short delay to ensure Ace is loaded
           showCodeLoadingOverlay();
           setTimeout(() => { try { initializeEditor(); } finally { const el = document.getElementById('code-loading-overlay'); if (el) el.remove(); } }, 200);

           function inferLangFromPath(path){
             const p = (path || '').toLowerCase();
             if (p.endsWith('.py')) return 'python';
             if (p.endsWith('.html') || p.endsWith('.htm')) return 'html';
             if (p.endsWith('.js')) return 'javascript';
             if (p.endsWith('.go')) return 'golang';
             if (p.endsWith('.md')) return 'markdown';
             if (p.endsWith('.json')) return 'json';
             if (p.endsWith('.xml')) return 'xml';
             if (p.endsWith('.css')) return 'css';
             if (p.endsWith('.sql')) return 'sql';
             if (p.endsWith('.sh') || p.endsWith('.bash')) return 'sh';
                        if (p.endsWith('.yaml')) return 'yaml';
              if (p.endsWith('.yml')) return 'yml';
              if (p.endsWith('.toml')) return 'toml';
              if (p.endsWith('.ini')) return 'ini';
              if (p.endsWith('.conf')) return 'ini';
              if (p.endsWith('.cfg')) return 'ini';
              if (p.endsWith('.properties')) return 'ini';
              if (p.endsWith('.dockerfile')) return 'text';
              if (p.endsWith('.txt')) return 'text';
              return 'text';
           }

           function mapToMonacoLang(lang){
             const langMap = {
               python: 'python',
               html: 'html',
               javascript: 'javascript',
               json: 'json',
               golang: 'go',
               markdown: 'markdown',
               text: 'plaintext',
               xml: 'xml',
               css: 'css',
               sql: 'sql',
               sh: 'shell',
               yaml: 'yaml',
               yml: 'yaml',
               toml: 'plaintext',
               ini: 'plaintext'
             };
             return langMap[lang] || 'plaintext';
           }

           function applyLanguage(lang){
             if (!editor || !window.monaco) return;
             const finalLang = mapToMonacoLang(lang);
             try { monaco.editor.setModelLanguage(editor.getModel(), finalLang); } catch (e) {}
           }

           function updateSyntaxDisplay(lang) {
             const display = document.getElementById('syntax-display');
             if (display) {
               const langNames = {
                 python: 'Python',
                 html: 'HTML',
                 javascript: 'JavaScript',
                 json: 'JSON',
                 golang: 'Go',
                 markdown: 'Markdown',
                 text: 'Plain Text',
                 xml: 'XML',
                 css: 'CSS',
                 sql: 'SQL',
                 sh: 'Shell',
                 yaml: 'YAML',
                 yml: 'YAML',
                 toml: 'TOML',
                 ini: 'INI'
               };
               display.textContent = langNames[lang] || 'Text';
             }
           }





           // RAW_EDIT_HTML - No code execution functionality needed
           // Removed all run/terminal code since buttons don't exist

           /*
           // REMOVED: Run button click handler - button doesn't exist in RAW_EDIT_HTML
           document.getElementById('code-run-button').addEventListener('click', function() {
             console.log('Run button clicked!');
             const codeText = (typeof editor !== 'undefined' && editor) ? 
               editor.getValue() : 
               document.getElementById('code_text').value;

             // Use the actual file path passed from server for detection
             const actualFilePath = '{{ actual_file_path }}';
             const fileExt = '.' + actualFilePath.toLowerCase().split('.').pop();

             if (!codeText.trim()) {
               alert('No code to run');
               return;
             }

             // Show terminal modal
             const modal = document.getElementById('terminal-modal');
             const output = document.getElementById('terminal-output');

                         console.log('Modal elements:', { modal: !!modal, output: !!output });

             if (!modal || !output) {
               console.error('Terminal modal elements not found!');
               alert('Terminal modal not found. Please refresh the page.');
               return;
             }

             modal.style.display = 'flex';



             output.innerHTML = '\n';

             // Force terminal font to match editor
             output.style.fontFamily = "'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace";
             output.style.fontVariantLigatures = "contextual";

             // Focus the command input
             setTimeout(() => {
               const input = document.getElementById('terminal-input');
               if (input) input.focus();
             }, 100);

             // Add welcome message if terminal is empty
             if (output.innerHTML.trim() === '') {
               output.innerHTML = `<span style="color: #58a6ff;">Welcome to Sequoia WorkBench Terminal</span><br><span style="color: #7d8590;">Type some command e.g. pip install pandas</span><br><br>`;
             }

             // Show pause and stop buttons, hide run button
             this.style.display = 'none';
             document.getElementById('code-pause-button').style.display = 'inline-flex';
             document.getElementById('code-stop-button').style.display = 'inline-flex';

             // Start execution
             console.log('Sending request to /run_code with:', { codeText: codeText.substring(0, 100) + '...', fileExt });
             fetch('/run_code', {
               method: 'POST',
               headers: {
                 'Content-Type': 'application/x-www-form-urlencoded',
               },
               body: `code_text=${encodeURIComponent(codeText)}&file_extension=${encodeURIComponent(fileExt)}`
             })
             .then(response => response.json())
             .then(data => {
               if (data.error) {
                 output.textContent += `Error: ${data.error}\n`;
                 resetButtons();
                 return;
               }

               currentSessionId = data.session_id;
               outputStreaming = true;
               streamOutput();
             })
             .catch(error => {
               output.textContent += `Error: ${error.message}\n`;
               resetButtons();
             });
           });

           // Stream output from server
           function streamOutput() {
             if (!currentSessionId || !outputStreaming) return;

             fetch(`/stream_output/${currentSessionId}`)
               .then(response => response.json())
               .then(data => {
                 const output = document.getElementById('terminal-output');

                 if (data.error) {
                   output.textContent += `Error: ${data.error}\n`;
                   stopExecution();
                   return;
                 }

                 if (data.output && data.output.length > 0) {
                   console.log('Received output:', data.output);
                   data.output.forEach(line => {
                     const color = line.type === 'stderr' ? '#ff6b6b' : '#ffffff';
                     output.innerHTML += `<span style="color: ${color}">${line.content}</span>`;
                   });
                   output.scrollTop = output.scrollHeight;
                 }

                 if (data.complete) {
                   // Append message without replacing existing content
                   output.innerHTML += `\n<span>${data.message}</span>\n`;
                   stopExecution();
                 } else {
                   // Continue streaming
                   setTimeout(streamOutput, 100);
                 }
               })
               .catch(error => {
                 const output = document.getElementById('terminal-output');
                 output.textContent += `Error: ${error.message}\n`;
                 stopExecution();
               });
           }

           // Reset buttons to initial state
           function resetButtons() {
             const runBtn = document.getElementById('code-run-button');
             const pauseBtn = document.getElementById('code-pause-button');
             const stopBtn = document.getElementById('code-stop-button');

             runBtn.style.display = 'inline-flex';
             pauseBtn.style.display = 'none';
             stopBtn.style.display = 'none';


           }

           // Stop execution
           function stopExecution() {
             outputStreaming = false;
             currentSessionId = null;
             resetButtons();
           }

           // Pause button click handler
           document.getElementById('code-pause-button').addEventListener('click', function() {
             console.log('Pause button clicked!');
             // For now, pause just shows a message - you can implement actual pausing later
             const output = document.getElementById('terminal-output');
             if (output) {
               output.textContent += '\n[PAUSED] - Execution paused by user\n';
             }
           });

           // Stop button click handler
           document.getElementById('code-stop-button').addEventListener('click', function() {
             console.log('Stop button clicked!');
             stopExecution();
             const output = document.getElementById('terminal-output');
             if (output) {
               output.textContent += '\n[STOPPED] - Execution stopped by user\n';
             }
           });

           // Terminal modal event handlers






           // Interactive terminal functionality
           const terminalInput = document.getElementById('terminal-input');
           if (terminalInput) {
             // Focus input when terminal opens
             terminalInput.addEventListener('focus', function() {
               this.select();
             });

             // Handle Enter key to execute command
                         terminalInput.addEventListener('keydown', function(e) {
                 if (e.key === 'Enter') {
                   e.preventDefault();
                   const command = this.value.trim();
                   if (command) {
                     executeCommand(command);
                     this.value = '';
                   }
                 }
               });
           }

           // Function to execute commands
           // Add ESC key to close terminal
           document.addEventListener('keydown', function(e) {
             if (e.key === 'Escape' && document.getElementById('terminal-modal').style.display !== 'none') {
               document.getElementById('terminal-modal').style.display = 'none';

             }
           });

           function executeCommand(command) {
             const output = document.getElementById('terminal-output');
             if (!output) return;

             // Handle built-in commands
             if (command.toLowerCase() === 'clear' || command.toLowerCase() === 'cls') {
               output.innerHTML = '';

               // Restore welcome message after clearing (same as clear button)
               output.innerHTML = '<span style="color: #58a6ff;">Welcome to Sequoia WorkBench Terminal</span><br><span style="color: #7d8590;">Type some command e.g. pip install pandas</span><br><br>';
               return;
             }



             // Show only the command being executed
             output.innerHTML += `<br><span style="color: #74c0fc;">$</span> <span style="color: #ffffff;">${command}</span><br>`;

             // Send command to server
             fetch('/execute_command', {
               method: 'POST',
               headers: {
                 'Content-Type': 'application/json',
               },
               body: JSON.stringify({ command: command })
             })
             .then(response => response.json())
             .then(data => {
               if (data.error) {
                 output.innerHTML += `<span style="color: #ff6b6b;">Error: ${data.error}</span><br>`;
               } else {
                 // Show output
                 if (data.output) {
                   output.innerHTML += `<span style="color: #ffffff;">${data.output}</span>`;
                 }
                 // Show error output
                 if (data.error) {
                   output.innerHTML += `<span style="color: #ff6b6b;">${data.error}</span>`;
                 }

               }
               output.scrollTop = output.scrollHeight;
             })
             .catch(error => {
               output.innerHTML += `<span style="color: #ff6b6b;">Error: ${error.message}</span><br>`;
               output.scrollTop = output.scrollHeight;
             });
           }

           // Close modal when clicking outside
           window.addEventListener('click', function(event) {
             const modal = document.getElementById('terminal-modal');
             if (event.target === modal) {
               modal.style.display = 'none';
             }
           });
           */
           // END OF REMOVED CODE


         })();
      </script>


   </body>
</html>
"""

def get_big_time_display():
    """Get current time and date for display"""
    now = datetime.now()
    time_str = now.strftime("%I:%M %p")  # 11:50 AM format
    date_str = now.strftime("%A, %B %d")
    return {"big_time": time_str, "day_date": date_str}

@app.route("/", methods=["GET", "POST"])
def home():
    if request.method == "GET":
        return render_template_string(
            HTML_TEMPLATE,
            last_url=session.get('last_url', ''),
            big_time_display=get_big_time_display()
        )
    
    # POST handling
    action = request.form.get("action", "")
    
    if action == "download":
        url = request.form.get("url_input", "").strip()
        if not url:
            flash("Please provide a valid URL")
            return redirect(url_for("home"))
        
        try:
            # Download file from URL
            response = requests.get(url, stream=True)
            response.raise_for_status()
            
            # Get filename from URL or content-disposition header
            filename = url.split('/')[-1]
            if not filename or '.' not in filename:
                content_type = response.headers.get('content-type', '')
                if 'text' in content_type:
                    filename = 'downloaded_file.txt'
                elif 'json' in content_type:
                    filename = 'downloaded_file.json'
                elif 'csv' in content_type:
                    filename = 'downloaded_file.csv'
                else:
                    filename = 'downloaded_file'
            
            # Save to temporary file and send
            temp_file = tempfile.NamedTemporaryFile(delete=False)
            for chunk in response.iter_content(chunk_size=8192):
                temp_file.write(chunk)
            temp_file.close()
            
            session['last_url'] = url
            flash(f"File downloaded successfully: {filename}")
            
            return send_file(temp_file.name, as_attachment=True, download_name=filename)
            
        except Exception as e:
            flash(f"Error downloading file: {str(e)}")
            return redirect(url_for("home"))
    
    elif action == "view":
        url = request.form.get("url_input", "").strip()
        if not url:
            flash("Please provide a valid URL")
            return redirect(url_for("home"))
        
        try:
            # Fetch content from URL
            response = requests.get(url)
            response.raise_for_status()
            
            content = response.text
            content_type = response.headers.get('content-type', '')
            
            session['last_url'] = url
            
            # Detect file type from URL or content type
            filename = url.split('/')[-1] or 'url_content'
            if not filename or '.' not in filename:
                if 'text/html' in content_type:
                    filename = 'webpage.html'
                elif 'application/json' in content_type:
                    filename = 'data.json'
                elif 'text/plain' in content_type:
                    filename = 'content.txt'
                else:
                    filename = 'url_content'
            
            # Check if it's a CSV file
            file_extension = filename.lower().split('.')[-1]
            if file_extension == 'gz':
                # Handle .csv.gz case
                file_extension = filename.lower().split('.')[-2]
            
            if file_extension in ['csv']:
                # Use CSV editor for CSV files from URLs
                per_page = int(request.form.get('csv_per_page', 20))
                return render_csv_editor_from_url(url, content, filename, per_page)
            else:
                # Use raw editor for other file types
                return render_template_string(
                    RAW_EDIT_HTML,
                    filename=filename,
                    code_text=content,
                    actual_file_path=filename,
                    big_time_display=get_big_time_display()
                )
            
        except Exception as e:
            flash(f"Error viewing content: {str(e)}")
            return redirect(url_for("home"))
    
    elif action == "edit":
        # Handle CSV/JSON editing from S3
        s3_path = request.form.get("s3_path", "").strip()
        if not s3_path:
            flash("Please provide a valid S3 path")
            return redirect(url_for("home"))
        
        try:
            # Detect file type from extension
            file_extension = s3_path.lower().split('.')[-1]
            if file_extension == 'gz':
                # Handle .csv.gz case
                file_extension = s3_path.lower().split('.')[-2]
            
            if file_extension in ['csv']:
                # Use CSV editor for CSV files
                return render_csv_editor(s3_path)
            else:
                # Use raw editor for other file types
                return render_raw_editor(s3_path)
                
        except Exception as e:
            flash(f"Error editing file: {str(e)}")
            return redirect(url_for("home"))
    
    elif action == "edit_local":
        upload = request.files.get("upload_file")
        if not upload or not upload.filename:
            flash("Please select a local file")
            return redirect(url_for("home"))
        
        try:
            # Read file content
            content = upload.read()
            filename = upload.filename
            
            # Detect file type from extension
            file_extension = filename.lower().split('.')[-1]
            if file_extension == 'gz':
                # Handle .csv.gz case
                file_extension = filename.lower().split('.')[-2]
            
            if file_extension in ['csv']:
                # Use CSV editor for CSV files
                per_page = int(request.form.get('csv_per_page', 20))
                return render_csv_editor_local(content, filename, per_page)
            else:
                # Use raw editor for everything else
                try:
                    text_content = content.decode('utf-8')
                except UnicodeDecodeError:
                    text_content = str(content)
                
                return render_template_string(
                    RAW_EDIT_HTML,
                    filename=filename,
                    code_text=text_content,
                    actual_file_path=filename,
                    big_time_display=get_big_time_display()
                )
            
        except Exception as e:
            flash(f"Error reading file: {str(e)}")
            return redirect(url_for("home"))
    
    return redirect(url_for("home"))

def render_csv_editor(s3_path):
    """Render CSV editor for S3 files"""
    try:
        # For now, redirect to home since S3 functionality is not fully implemented
        flash("S3 CSV editing is not yet implemented. Please use local file upload or URL.")
        return redirect(url_for("home"))
    except Exception as e:
        flash(f"Error editing file: {str(e)}")
        return redirect(url_for("home"))

def render_csv_editor_local(content, filename, per_page=20):
    """Render CSV editor for local files"""
    try:
        # Parse CSV content (already read from upload)
        try:
            text_content = content.decode('utf-8')
        except UnicodeDecodeError:
            flash("File must be text-based (UTF-8)")
            return redirect(url_for("home"))
        
        # Simple CSV parsing (split by lines and commas)
        lines = text_content.strip().split('\n')
        if not lines:
            flash("CSV file is empty")
            return redirect(url_for("home"))
        
        # Parse headers and data
        headers = [h.strip() for h in lines[0].split(',')]
        data = []
        for line in lines[1:]:
            if line.strip():
                values = [v.strip() for v in line.split(',')]
        CSV_DATA_CACHE[cache_key] = {
            'data': data.to_dict('records'),
            'columns': columns,
            'public_url': public_url,
            'module': module,
            'file_type': file_type,
            'gzipped': gzipped,
            'filename': filename,
            'detected_delimiter': detected_delimiter
        }
        
        # Get pagination count from form or session
        # The form should have the updated value from JavaScript localStorage sync
        per_page = int(request.form.get('csv_per_page', session.get('csv_per_page', 20)))
        
        # Store cache key in session for clean URLs
        session['csv_cache_key'] = cache_key
        session['csv_per_page'] = per_page
        
        print(f"DEBUG: Home route - csv_per_page from form: {request.form.get('csv_per_page')}")
        print(f"DEBUG: Home route - final per_page: {per_page}")
        print(f"DEBUG: Home route - all form data: {dict(request.form)}")
        
        # Redirect to the clean CSV editor URL
        return redirect(url_for('csv_page', page=1))
    # ... existing code ...
        total_rows = len(data)
        page_count = (total_rows + per_page - 1) // per_page  # Ceiling division
        
        # Get first page data
        start = 0
        end = min(per_page, total_rows)
        page_data = data[start:end]
        
        return render_template_string(
            CSV_EDIT_HTML,
            filename=filename,
            s3_path=f"Local file: {filename}",
            gzipped=False,
            cache_key=cache_key,
            theme="dark",
            big_time_display=get_big_time_display(),
            # CSV specific data
            columns=headers,
            data=page_data,
            edits={},
            edits_json="{}",
            start_rec=start + 1,
            end_rec=end,
            total_rows=total_rows,
            page=1,
            page_count=page_count,
            per_page=per_page,
            start=start,
            escaped_delimiter=",",
            file_type="csv"
        )
    except Exception as e:
        flash(f"Error rendering CSV editor: {str(e)}")
        return redirect(url_for("home"))

def render_csv_editor_from_url(url, content, filename, per_page=20):
    """Render CSV editor for CSV files from URLs"""
    try:
        # Simple CSV parsing (split by lines and commas)
        lines = content.strip().split('\n')
        if not lines:
            flash("CSV file is empty")
            return redirect(url_for("home"))
        
        # Parse headers and data
        headers = [h.strip() for h in lines[0].split(',')]
        data = []
        for line in lines[1:]:
            if line.strip():
                values = [v.strip() for v in line.split(',')]
                row = {}
                for i, header in enumerate(headers):
                    row[header] = values[i] if i < len(values) else ""
                data.append(row)
        
        # Store data in cache system (same as workbench.py)
        import time
        cache_key = f"url_csv_{hash(filename)}_{int(time.time())}"
        
        # Store full data in cache - keep as list of dicts for template compatibility
        CSV_DATA_CACHE[cache_key] = {
            'data': data,  # Keep as list of dicts, not DataFrame
            'columns': headers,
            'public_url': url,
            'module': 'csv',
            'file_type': 'csv',
            'gzipped': False,
            'filename': filename,
            'detected_delimiter': ',',
            'per_page': per_page  # Store the pagination count
        }
        
        # Store cache key in session for clean URLs
        session['csv_cache_key'] = cache_key
        session['csv_per_page'] = per_page
        
        # Debug information
        print(f"DEBUG: Stored {len(data)} rows in cache with key: {cache_key}")
        print(f"DEBUG: Cache keys: {list(CSV_DATA_CACHE.keys())}")
        print(f"DEBUG: Data format: {type(data)}, first row: {data[0] if data else 'None'}")
        
        # Redirect to clean CSV editor URL
        return redirect(url_for('csv_page', page=1))
    except Exception as e:
        flash(f"Error rendering CSV editor: {str(e)}")
        return redirect(url_for("home"))

def render_raw_editor(s3_path):
    """Render raw editor for non-CSV files"""
    try:
        # For now, return a simple raw editor
        # In a real implementation, you would read the file from S3
        sample_content = f"# Content from {s3_path}\n\nThis is a sample file content."
        
        return render_template_string(
            RAW_EDIT_HTML,
            filename=s3_path.split('/')[-1],
            code_text=sample_content,
            actual_file_path=s3_path,
            big_time_display=get_big_time_display()
        )
    except Exception as e:
        flash(f"Error rendering raw editor: {str(e)}")
        return redirect(url_for("home"))

@app.route('/download_csv', methods=['POST'])
def download_csv():
    try:
        print(f"DEBUG: Download CSV form data: {dict(request.form)}")
        print(f"DEBUG: Session keys: {list(session.keys())}")
        print(f"DEBUG: CSV_DATA_CACHE keys: {list(CSV_DATA_CACHE.keys())}")
        
        # Get cache key from session or form
        cache_key = request.form.get('cache_key') or session.get('cache_key')
        print(f"DEBUG: Cache key: {cache_key}")
        
        if not cache_key:
            print("DEBUG: No cache key found")
            flash("No data available for download")
            return redirect(url_for('home'))
        
        # Get data from cache
        cached_data = CSV_DATA_CACHE.get(cache_key)
        print(f"DEBUG: Cached data found: {cached_data is not None}")
        if not cached_data:
            print(f"DEBUG: Available cache keys: {list(CSV_DATA_CACHE.keys())}")
            flash("Data not found in cache")
            return redirect(url_for('home'))
        
        data = cached_data['data']
        filename = cached_data.get('filename', 'modified_file.csv')
        
        # Get edits from session
        edits = session.get(f'csv_edits_{cache_key}', {})
        print(f"DEBUG: Looking for edits with key: csv_edits_{cache_key}")
        print(f"DEBUG: Found {len(edits)} edits: {edits}")
        
        # Apply edits to data
        for key, new_value in edits.items():
            try:
                row_idx, col_idx = key.split(',')
                row_idx = int(row_idx)
                col_idx = int(col_idx)
                
                if row_idx < len(data) and col_idx < len(data[0]):
                    # Get column name from first row
                    columns = list(data[0].keys())
                    if col_idx < len(columns):
                        col_name = columns[col_idx]
                        data[row_idx][col_name] = new_value
            except (ValueError, IndexError, KeyError):
                continue
        
        # Get delimiter from form
        delimiter = request.form.get('delimiter', ',')
        
        # Convert to CSV format with specified delimiter
        if data:
            import csv
            from io import StringIO
            
            output = StringIO()
            writer = csv.DictWriter(output, fieldnames=data[0].keys(), delimiter=delimiter)
            writer.writeheader()
            writer.writerows(data)
            
            csv_content = output.getvalue()
            output.close()
            
            # Create response with CSV content
            from flask import Response
            response = Response(csv_content, mimetype='text/csv')
            response.headers['Content-Disposition'] = f'attachment; filename="{filename}"'
            return response
        else:
            flash("No data to download")
            return redirect(url_for('home'))
        
    except Exception as e:
        print(f"DEBUG: Download CSV error: {str(e)}")
        flash(f"Error downloading CSV: {str(e)}")
        return redirect(url_for('home'))

@app.route('/save_raw', methods=['POST'])
def save_raw():
    try:
        # Get form data
        code_text = request.form.get('code_text', '')
        
        # For now, just flash a success message
        # In a real implementation, you would save the content
        flash(f"Content saved successfully! Length: {len(code_text)} characters")
        
        return redirect(url_for('home'))
        
    except Exception as e:
        flash(f"Error saving content: {str(e)}")
        return redirect(url_for('home'))







@app.route('/set-theme', methods=['POST'])
def set_theme():
    try:
        data = request.get_json()
        theme = data.get('theme', 'dark')
        session['theme'] = theme
        return jsonify({'success': True, 'theme': theme})
    except Exception as e:
        return jsonify({'error': str(e)})




@app.route('/csv-edit', methods=['GET', 'POST'])
@app.route('/csv-edit/<int:page>', methods=['GET'])
def csv_page(page=1):
    try:
        # Get pagination parameters from session or URL
        cache_key = session.get('csv_cache_key', '')
        # Try to get from session first, then default to localStorage value or 20
        per_page = int(session.get('csv_per_page', 20))
        
        # Override from URL if provided (clean URLs)
        if request.method == 'GET':
            # Only override per_page if explicitly provided in URL, otherwise use session
            if 'per_page' in request.args:
                per_page = int(request.args.get('per_page'))
                session['csv_per_page'] = per_page  # Update session
            if 'cache_key' in request.args:
                cache_key = request.args['cache_key']
                session['csv_cache_key'] = cache_key  # Update session
        else:
            page = int(request.form.get('page', 1))
            if 'per_page' in request.form:
                per_page = int(request.form.get('per_page'))
                session['csv_per_page'] = per_page  # Update session
            if 'cache_key' in request.form:
                cache_key = request.form['cache_key']
                session['csv_cache_key'] = cache_key  # Update session
        
        s3_path = request.form.get('s3_path', '') if request.method == 'POST' else ''
        
        # Debug information
        print(f"DEBUG: Session cache_key: {session.get('csv_cache_key')}")
        print(f"DEBUG: Session per_page: {session.get('csv_per_page')}")
        print(f"DEBUG: URL per_page: {request.args.get('per_page')}")
        print(f"DEBUG: Final per_page: {per_page}")
        print(f"DEBUG: Cache keys available: {list(CSV_DATA_CACHE.keys())}")
        print(f"DEBUG: Using cache_key: {cache_key}")
        
        # Get the stored CSV data from cache system (same as workbench.py)
        if not cache_key or cache_key not in CSV_DATA_CACHE:
            return jsonify({'error': 'No CSV data found in cache. Please reload the CSV file.'})
        
        cached_data = CSV_DATA_CACHE[cache_key]
        data_full = cached_data['data']  # Use 'data' not 'dataframe'
        
        # Use pagination count from session (user preference) instead of cache
        # per_page = cached_data.get('per_page', 20)  # Don't use cache value
        
        # Debug information
        print(f"DEBUG: Cache keys: {list(CSV_DATA_CACHE.keys())}")
        print(f"DEBUG: Found data for cache_key: {cache_key}")
        print(f"DEBUG: Data length: {len(data_full)}")
        print(f"DEBUG: Request form data: {dict(request.form)}")
        print(f"DEBUG: Page: {page}, Per_page from cache: {per_page}")
        
        # Calculate pagination
        total_rows = len(data_full)
        page_count = (total_rows + per_page - 1) // per_page
        
        # Validate page number
        if page < 1:
            page = 1
        elif page > page_count:
            page = page_count
            # For POST requests or when cache_key is in URL, redirect to clean URL
            if request.method == 'POST' or request.args.get('cache_key'):
                # Store cache_key in session for clean URLs
                if cache_key:
                    session['csv_cache_key'] = cache_key
                    session['csv_per_page'] = per_page
                return redirect(url_for('csv_page', page=page))
            
            # For GET requests, render the template
            return render_template_string(CSV_EDIT_HTML,
                s3_path=s3_path,
                module=module,
                file_type=file_type,
                gzipped=gzipped,
                filename=filename,
                columns=columns,
                data=data,
                clean_url=url_for('csv_page', page=page),
                page=page,
                per_page=per_page,
                total_rows=total_rows,
                page_count=page_count,
                cache_key=cache_key,
                escaped_delimiter=escaped_delimiter,
                edits=edits,
                edits_json=json.dumps(edits, default=str)
            )
        
        # Calculate start and end indices
        start = (page - 1) * per_page
        end = min(start + per_page, total_rows)
        
        # Get the page data
        page_data = data_full[start:end]
        
        # Get cached data details
        columns = cached_data.get('columns', [])
        public_url = cached_data.get('public_url', '')
        module = cached_data.get('module', 'csv')
        file_type = cached_data.get('file_type', 'csv')
        gzipped = cached_data.get('gzipped', False)
        filename = cached_data.get('filename', 'data.csv')
        detected_delimiter = cached_data.get('detected_delimiter', ',')
        escaped_delimiter = detected_delimiter.replace('\\', '\\\\').replace('"', '\\"')
        
        # Get existing edits from session
        edits = session.get(f'csv_edits_{cache_key}', {})
        
        # Render the CSV editor template
        return render_template_string(
            CSV_EDIT_HTML,
            public_url=public_url,
            s3_path=public_url,  # Use public_url as s3_path for compatibility
            module=module,
            file_type=file_type,
            gzipped=gzipped,
            filename=filename,
            columns=columns,
            data=page_data,
            page=page,
            per_page=per_page,
            total_rows=total_rows,
            page_count=page_count,
            cache_key=cache_key,
            escaped_delimiter=escaped_delimiter,
            edits=edits,
            edits_json=json.dumps(edits, default=str),
            start_rec=start + 1,
            end_rec=end,
            start=start,  # Add missing start variable
            theme=session.get('theme', 'dark'),
            big_time_display=get_big_time_display()
        )
        
    except Exception as e:
        return jsonify({'error': str(e)})



@app.route('/update-pagination', methods=['POST'])
def update_pagination():
    """Update pagination count for a specific CSV file in cache"""
    try:
        cache_key = request.form.get('cache_key', '')
        new_per_page = int(request.form.get('per_page', 20))
        
        print(f"DEBUG: update-pagination called with cache_key: {cache_key}, new_per_page: {new_per_page}")
        print(f"DEBUG: Available cache keys: {list(CSV_DATA_CACHE.keys())}")
        
        if not cache_key or cache_key not in CSV_DATA_CACHE:
            print(f"DEBUG: Cache key not found: {cache_key}")
            return jsonify({'error': 'No CSV data found in cache'})
        
        # Update the pagination count in cache
        CSV_DATA_CACHE[cache_key]['per_page'] = new_per_page
        
        print(f"DEBUG: Updated pagination for {cache_key} to {new_per_page}")
        print(f"DEBUG: Cache data now: {CSV_DATA_CACHE[cache_key]}")
        
        return jsonify({'success': True, 'per_page': new_per_page})
        
    except Exception as e:
        print(f"DEBUG: Error in update-pagination: {str(e)}")
        return jsonify({'error': str(e)})

@app.route('/save-settings', methods=['POST'])
def save_settings():
    """Save pagination count and URL input to session memory"""
    try:
        data = request.get_json()
        pagination_count = data.get('pagination_count', 20)
        url_input = data.get('url_input', '')
        
        # Save to session memory
        session['pagination_count'] = pagination_count
        session['url_input'] = url_input
        
        print(f"DEBUG: Settings saved - pagination: {pagination_count}, URL: {url_input}")
        
        return jsonify({'success': True, 'pagination_count': pagination_count, 'url_input': url_input})
        
    except Exception as e:
        print(f"DEBUG: Error saving settings: {str(e)}")
        return jsonify({'error': str(e)})

@app.route('/get-settings', methods=['GET'])
def get_settings():
    """Get saved pagination count and URL input from session memory"""
    try:
        pagination_count = session.get('pagination_count', 20)
        url_input = session.get('url_input', '')
        
        print(f"DEBUG: Settings retrieved - pagination: {pagination_count}, URL: {url_input}")
        
        return jsonify({
            'success': True, 
            'pagination_count': pagination_count, 
            'url_input': url_input
        })
        
    except Exception as e:
        print(f"DEBUG: Error getting settings: {str(e)}")
        return jsonify({'error': str(e)})

@app.route('/update-csv-edit', methods=['POST'])
def update_csv_edit():
    try:
        data = request.get_json()
        cache_key = data.get('cache_key')
        edits = data.get('edits', {})
        
        print(f"DEBUG: Update CSV edit - cache_key: {cache_key}, edits: {edits}")
        
        if not cache_key:
            return jsonify({'success': False, 'error': 'No cache key provided'})
        
        # Store all edits in session
        edits_key = f'csv_edits_{cache_key}'
        session[edits_key] = edits
        
        print(f"DEBUG: Saved {len(edits)} edits to session key {edits_key}")
        
        return jsonify({'success': True})
        
    except Exception as e:
        print(f"DEBUG: Error updating CSV edit: {str(e)}")
        return jsonify({'success': False, 'error': str(e)})

@app.route('/save', methods=['POST'])
def save():
    try:
        # Get form data
        s3_path = request.form.get('s3_path', '')
        table_data = request.form.get('table_data', '')
        all_edits = request.form.get('all_edits', '')
        
        # For now, just flash a success message
        # In a real implementation, you would save the CSV data
        flash(f"CSV saved successfully to {s3_path}")
        
        return redirect(url_for('home'))
        
    except Exception as e:
        flash(f"Error saving CSV: {str(e)}")
        return redirect(url_for('home'))

@app.route('/execute_command', methods=['POST'])
def execute_command():
    try:
        data = request.get_json()
        command = data.get('command', '')
        
        if not command:
            return jsonify({'error': 'No command provided'})
        
        # Execute command using subprocess
        import subprocess
        import shlex
        
        # Split command into arguments safely
        args = shlex.split(command)
        
        # Execute command
        result = subprocess.run(args, capture_output=True, text=True, timeout=30)
        
        return jsonify({'output': result.stdout, 'stderr': result.stderr, 'returncode': result.returncode})
        
    except subprocess.TimeoutExpired:
        return jsonify({'error': 'Command timed out'})
    except FileNotFoundError:
        return jsonify({'error': f'Command not found: {command.split()[0]}'})
    except Exception as e:
        return jsonify({'error': str(e)})

@app.route('/csv-editor')
def csv_editor_route():
    """Direct route to CSV editor"""
    return render_template_string(
        CSV_EDIT_HTML,
        filename="",
        s3_path="",
        gzipped=False,
        cache_key="direct_csv",
        theme="dark",
        big_time_display=get_big_time_display(),
        # CSV specific data
        columns=[],
        data=[],
        edits={},
        edits_json="{}",
        start_rec=0,
        end_rec=0,
        total_rows=0,
        page=1,
        page_count=0,
        per_page=20,
        start=0,
        escaped_delimiter=",",
        file_type="csv"
    )

@app.route('/raw-editor')
def raw_editor_route():
    """Direct route to raw editor"""
    return render_template_string(
        RAW_EDIT_HTML,
        filename="",
        code_text="",
        actual_file_path="",
        big_time_display=get_big_time_display()
    )

if __name__ == "__main__":
    port = int(os.environ.get("PORT", "9000"))
    try:
        webbrowser.open(f"http://localhost:{port}")
    except Exception:
        pass
    app.run(debug=True, port=port, use_reloader=True)
