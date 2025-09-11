# pylint: skip-file
# flake8: noqa
import csv
import gzip
import hashlib
import io
import json
import logging
import math
import os
import platform
import queue
import random
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import uuid
import webbrowser
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from json import JSONDecodeError

import pandas as pd
from botocore.exceptions import ClientError

logger = logging.getLogger(__name__)

# Configure module-level logger with enhanced debugging for parameter retrieval
logger = logging.getLogger(__name__)
# Change to INFO level to see parameter retrieval logs and debug stage environment key requests
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')

# Enable AWS SDK logging for parameter calls to track SSM GetParameter requests
boto_logger = logging.getLogger('boto3')
boto_logger.setLevel(logging.INFO)
botocore_logger = logging.getLogger('botocore')
botocore_logger.setLevel(logging.INFO)

# Environment persistence file - Windows compatible
if os.name == 'nt':  # Windows
    ENV_CONFIG_FILE = os.path.join(os.path.expanduser("~"), "sequoia_workbench_env.txt")
else:  # Unix-like (macOS, Linux)
    ENV_CONFIG_FILE = os.path.expanduser("~/.sequoia_workbench_env")


def load_environment():
    """Load environment from persistent storage"""
    try:
        if os.path.exists(ENV_CONFIG_FILE):
            with open(ENV_CONFIG_FILE, 'r') as f:
                saved_env = f.read().strip()
                if saved_env in ['dev', 'stage', 'production']:
                    return saved_env
    except Exception as e:
        print(f"Warning: Could not load environment config: {e}")
    return 'dev'  # Default fallback


def save_environment(environment):
    """Save environment to persistent storage"""
    try:
        # Ensure directory exists on Windows
        config_dir = os.path.dirname(ENV_CONFIG_FILE)
        if config_dir and not os.path.exists(config_dir):
            os.makedirs(config_dir, exist_ok=True)

        with open(ENV_CONFIG_FILE, 'w') as f:
            f.write(environment)
        print(f"Environment saved: {environment} to {ENV_CONFIG_FILE}")
    except Exception as e:
        print(f"Warning: Could not save environment config: {e}")
        if os.name == 'nt':
            print(f"Windows debugging: Attempted to write to {ENV_CONFIG_FILE}")
            print(f"User home directory: {os.path.expanduser('~')}")


# Use persistent cache directory in user's home (cross-platform)
S3_CACHE_DIR = os.path.join(os.path.expanduser('~'), '.s3_cache')

# Windows compatible extraction directory
if os.name == 'nt':  # Windows
    EXTRACT_DIR = os.path.join(os.path.expanduser('~'), 'dxpflow')
else:  # Unix-like (macOS, Linux)
    EXTRACT_DIR = os.path.expanduser('~/dxpflow')

# Load environment from persistent storage
env = load_environment()
print(f"Starting with environment: {env}")
print(f"Operating System: {os.name} ({'Windows' if os.name == 'nt' else 'Unix-like'})")
print(f"Environment config file: {ENV_CONFIG_FILE}")
print(f"Cache directory: {S3_CACHE_DIR}")
print(f"Extraction directory: {EXTRACT_DIR}")

# Force AWS_PROFILE to loaded environment before any AWS imports
os.environ['AWS_PROFILE'] = env
os.environ['AWS_CA_BUNDLE'] = ''
CACHE_EXPIRY_HOURS = 24
MAX_PARALLEL_WORKERS = 50

# CSV Edit tracking cache
CSV_DATA_CACHE = {}  # Stores full DataFrame for each file
CSV_EDITS_CACHE = {}  # Stores edits by page and cell
JSON_DATA_CACHE = {}  # Stores parsed JSON data
JSON_EDITS_CACHE = {}  # Stores JSON edits by record and path

# Initialize cache directory
os.makedirs(S3_CACHE_DIR, exist_ok=True)

# Global cache structures
S3_BUCKET_CACHE = {}
PATH_CACHE = {}  # Separate cache for individual paths
CACHE_LOCK = threading.Lock()
PATH_CACHE_LOCK = threading.Lock()
# In-flight fetch registry for path listings (server-side de-dup)
INFLIGHT_PATH_FETCHES = {}
INFLIGHT_LOCK = threading.Lock()

# Crypto key cache for Parameter Store keys
CRYPTO_KEY_CACHE = {}
CRYPTO_CACHE_LOCK = threading.Lock()
CRYPTO_CACHE_EXPIRY = 3600  # 1 hour cache expiry

# Batch download tracking
BATCH_DOWNLOADS = {}
BATCH_LOCK = threading.Lock()

# Code execution tracking
RUNNING_PROCESSES = {}  # For code execution sessions

# Cache tuning (PATH_CACHE LRU and persistence)
PATH_CACHE_MAX_ENTRIES = 1000  # Maximum entries for comprehensive caching
try:
    import pickle  # simple disk persistence
except Exception:
    pickle = None
PATH_CACHE_PERSIST = os.path.join(S3_CACHE_DIR, "path_cache.pkl")


def make_path_cache_key(bucket: str, prefix: str) -> str:
    profile = os.environ.get("AWS_PROFILE", "dev")
    current_env = os.environ.get("ENVIRONMENT", "dev")
    norm_prefix = (prefix or "")
    if norm_prefix and not norm_prefix.endswith('/'):
        norm_prefix += '/'
    cache_key = f"{profile}:{current_env}:{bucket}:{norm_prefix}"
    # Debug: Log cache key generation
    if 'logger' in globals():
        logger.debug(f"Generated cache key: {cache_key} (profile={profile}, env={current_env})")
    return cache_key


def get_parent_path(bucket: str, prefix: str) -> tuple:
    """Get parent path for a given path"""
    if not prefix:
        return bucket, ""
    parent_prefix = '/'.join(prefix.rstrip('/').split('/')[:-1])
    if parent_prefix:
        parent_prefix += '/'
    return bucket, parent_prefix


def get_sibling_paths(bucket: str, prefix: str) -> list:
    """Get potential sibling paths for faster navigation"""
    if not prefix:
        return []

    parent_prefix = '/'.join(prefix.rstrip('/').split('/')[:-1])
    if parent_prefix:
        parent_prefix += '/'

    # Return common sibling prefixes
    siblings = []
    current_folder = prefix.rstrip('/').split('/')[-1]
    if current_folder:
        # Add some common sibling patterns
        for sibling in ['data', 'logs', 'config', 'temp', 'backup', 'archive']:
            sibling_path = parent_prefix + sibling + '/'
            siblings.append((bucket, sibling_path))

    return siblings


def warm_cache_for_path(bucket: str, prefix: str, module: str):
    """Background cache warming for frequently accessed paths"""
    try:
        # Cache the current path if not already cached
        cache_key = make_path_cache_key(bucket, prefix)
        with PATH_CACHE_LOCK:
            if cache_key not in PATH_CACHE:
                logger.info(f"Warming cache for path: {bucket}/{prefix}")
                # This will trigger a background fetch
                return True
        return False
    except Exception as e:
        logger.error(f"Error warming cache for {bucket}/{prefix}: {e}")
        return False


def _prune_path_cache():
    with PATH_CACHE_LOCK:
        if len(PATH_CACHE) <= PATH_CACHE_MAX_ENTRIES:
            return
        items = sorted(PATH_CACHE.items(), key=lambda kv: kv[1].get('timestamp', 0))
        to_remove = len(PATH_CACHE) - PATH_CACHE_MAX_ENTRIES
        for i in range(to_remove):
            try:
                del PATH_CACHE[items[i][0]]
            except Exception:
                pass


def _persist_path_cache():
    if not pickle:
        return
    try:
        with open(PATH_CACHE_PERSIST, 'wb') as f:
            pickle.dump(PATH_CACHE, f, protocol=pickle.HIGHEST_PROTOCOL)
    except Exception:
        pass


# Warm load PATH_CACHE from disk on startup
if pickle:
    try:
        if os.path.exists(PATH_CACHE_PERSIST):
            with open(PATH_CACHE_PERSIST, 'rb') as f:
                persisted = pickle.load(f)
                if isinstance(persisted, dict):
                    with PATH_CACHE_LOCK:
                        PATH_CACHE.update(persisted)
    except Exception:
        pass

# figure out where this script lives on disk and find dxpflow.zip
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
ZIP_PATH = os.path.join(BASE_DIR, 'dxpflow.zip')

# If zip file not found in script directory, check current working directory
if not os.path.exists(ZIP_PATH):
    cwd_zip_path = os.path.join(os.getcwd(), 'dxpflow.zip')
    if os.path.exists(cwd_zip_path):
        ZIP_PATH = cwd_zip_path
        print(f"Found dxpflow.zip in current working directory: {ZIP_PATH}")
    else:
        print(f"ERROR: dxpflow.zip not found!")
        print(f"Looked in script directory: {os.path.join(BASE_DIR, 'dxpflow.zip')}")
        print(f"Looked in current directory: {cwd_zip_path}")
        print(f"Current working directory: {os.getcwd()}")
        print(f"Script directory: {BASE_DIR}")
        print(
            "\nPlease ensure dxpflow.zip is in the same directory as this script or in your current working directory.")
        sys.exit(1)

NESTED_DIR = os.path.join(EXTRACT_DIR, 'dxpflow')

# Check if extraction is needed
if not os.path.isdir(EXTRACT_DIR) or not os.listdir(EXTRACT_DIR):
    # Create extract directory if it doesn't exist
    os.makedirs(EXTRACT_DIR, exist_ok=True)

    # unpack
    with zipfile.ZipFile(ZIP_PATH, 'r') as z:
        z.extractall(EXTRACT_DIR)

    # flatten nested dxpflow/ folder
    if os.path.isdir(NESTED_DIR):
        for item in os.listdir(NESTED_DIR):
            src = os.path.join(NESTED_DIR, item)
            dst = os.path.join(EXTRACT_DIR, item)
            if os.path.exists(dst):
                if os.path.isdir(dst):
                    shutil.rmtree(dst)
                else:
                    os.remove(dst)
            shutil.move(src, dst)
        shutil.rmtree(NESTED_DIR)

    print("Extracted dxpflow.zip successfully")
else:
    print("Using existing extracted files from", EXTRACT_DIR)

if 'conf' not in globals():
    conf = None

env_vars = {
    'AWS_PROFILE': env,
    'ENVIRONMENT': env,
    'MODULE_HOME': EXTRACT_DIR,
    'DXPFLOW_HOME': EXTRACT_DIR,
}
for k, v in env_vars.items():
    os.environ[k] = v
    if conf is not None and hasattr(conf, 'setExecutorEnv'):
        conf = conf.setExecutorEnv(k, v)

parent = os.path.dirname(EXTRACT_DIR)
if parent not in sys.path:
    sys.path.insert(0, parent)

from dxpflow.common.utils.aws_helpers import S3Utils
from dxpflow.secure.crypto import CryptoAPI
from dxpflow.common.base import DXPFlowComponent

# Add boto3 event handler to log SSM parameter requests
import boto3


def log_ssm_parameter_calls(event_name, **kwargs):
    """Log AWS SSM GetParameter and GetParameters calls to track key retrieval"""
    if 'ssm' in event_name.lower() and ('GetParameter' in event_name or 'get-parameter' in str(kwargs).lower()):
        logger.info(f"SSM PARAMETER DEBUG - Event: {event_name}")
        logger.info(f"SSM PARAMETER DEBUG - Current environment: {env}")
        logger.info(f"SSM PARAMETER DEBUG - AWS Profile: {os.environ.get('AWS_PROFILE')}")
        if 'params' in kwargs:
            params = kwargs.get('params', {})
            if 'Name' in params:
                logger.info(f"SSM PARAMETER DEBUG - Parameter name being requested: {params['Name']}")
            if 'Names' in params:
                logger.info(f"SSM PARAMETER DEBUG - Parameter names being requested: {params['Names']}")
        logger.info(f"SSM PARAMETER DEBUG - All kwargs: {kwargs}")


def get_cached_crypto_api(module, operation="general"):
    """
    Get a cached CryptoAPI instance to avoid repeated Parameter Store calls.
    The crypto keys are cached for 1 hour to improve performance.
    """
    cache_key = f"{module}:{env}"  # Cache per module and environment

    with CRYPTO_CACHE_LOCK:
        # Check if we have a valid cached instance
        if cache_key in CRYPTO_KEY_CACHE:
            cached_data = CRYPTO_KEY_CACHE[cache_key]
            if time.time() - cached_data['timestamp'] < CRYPTO_CACHE_EXPIRY:
                logger.info(f"CRYPTO CACHE HIT - Using cached CryptoAPI for module: {module}")
                return cached_data['crypto_api']
            else:
                # Cache expired, remove it
                logger.info(f"CRYPTO CACHE EXPIRED - Removing expired cache for module: {module}")
                del CRYPTO_KEY_CACHE[cache_key]

        # Cache miss or expired, create new instance
        logger.info(f"CRYPTO CACHE MISS - Creating new CryptoAPI for module: {module}")
        logger.info(f"CRYPTO DEBUG - {operation} - Environment: {env}")
        logger.info(f"CRYPTO DEBUG - {operation} - AWS_PROFILE: {os.environ.get('AWS_PROFILE')}")
        logger.info(f"CRYPTO DEBUG - {operation} - ENVIRONMENT: {os.environ.get('ENVIRONMENT')}")

        try:
            crypto_api = CryptoAPI(module)
            logger.info(f"CRYPTO DEBUG - {operation} - CryptoAPI instance created successfully for module: {module}")

            # Cache the instance
            CRYPTO_KEY_CACHE[cache_key] = {
                'crypto_api': crypto_api,
                'timestamp': time.time(),
                'module': module,
                'environment': env
            }
            logger.info(f"CRYPTO CACHE STORED - Cached CryptoAPI for module: {module}")

            return crypto_api
        except Exception as e:
            logger.error(f"CRYPTO DEBUG - {operation} - Failed to create CryptoAPI for module {module}: {e}")
            raise


def clear_crypto_cache():
    """Clear the crypto key cache"""
    with CRYPTO_CACHE_LOCK:
        cache_size = len(CRYPTO_KEY_CACHE)
        CRYPTO_KEY_CACHE.clear()
        logger.info(f"CRYPTO CACHE CLEARED - Removed {cache_size} cached entries")


def get_crypto_cache_stats():
    """Get crypto cache statistics"""
    with CRYPTO_CACHE_LOCK:
        return {
            'cache_size': len(CRYPTO_KEY_CACHE),
            'cache_keys': list(CRYPTO_KEY_CACHE.keys()),
            'cache_expiry': CRYPTO_CACHE_EXPIRY
        }


# Register the event handler for all boto3 events
try:
    boto3.set_stream_logger('boto3', logging.INFO)
    boto3.set_stream_logger('botocore', logging.INFO)
    # This will capture before-call events
    import botocore.hooks

    event_system = botocore.hooks.HierarchicalEmitter()
    event_system.register('before-call.*', log_ssm_parameter_calls)
    logger.info("SSM PARAMETER DEBUG - Registered boto3 event handlers for parameter tracking")
except Exception as e:
    logger.warning(f"Failed to register boto3 event handlers: {e}")

from flask import Flask, send_file, session
from flask import request, redirect, url_for, flash, render_template_string, jsonify
from werkzeug.exceptions import RequestEntityTooLarge, HTTPException

app = Flask(__name__)
LOGO_URL = "https://marvel-b1-cdn.bc0a.com/f00000000236542/www.sequoia.com/wp-content/uploads/2019/12/sequoia-logo@2x.png"
app.secret_key = secrets.token_hex(32)


@app.errorhandler(RequestEntityTooLarge)
def handle_413(e):
    logger.error(f"413 Request too large: {e}")
    # AJAX callers get JSON so UI can show modal inline
    if request.headers.get('X-Requested-With') == 'XMLHttpRequest':
        return jsonify(ok=False, message="File too large to save."), 413
    # Others: set modal message and redirect to home
    return _modal_redirect("File too large to save.")


@app.errorhandler(Exception)
def handle_unhandled(e):
    # Convert to HTTPException if applicable to keep status code
    code = 500
    message = str(e)
    if isinstance(e, HTTPException):
        code = e.code or 500
        # Some HTTPExceptions have a .description
        try:
            message = getattr(e, 'description', message) or message
        except Exception:
            pass

    logger.error(f"Unhandled error ({code}): {message}", exc_info=True)
    if request.headers.get('X-Requested-With') == 'XMLHttpRequest':
        return jsonify(ok=False, message=message), code
    return _modal_redirect(message)


# Optional: reduce third-party noise
try:
    logging.getLogger('urllib3').setLevel(logging.ERROR)
    logging.getLogger('botocore').setLevel(logging.ERROR)
except Exception:
    pass

# Suppress werkzeug access logs entirely
try:
    logging.getLogger('werkzeug').setLevel(logging.CRITICAL)
    logging.getLogger('werkzeug').propagate = False
    from werkzeug import serving as _wzs


    class _SilentWSGIRequestHandler(_wzs.WSGIRequestHandler):
        def log(self, type, message, *args):
            pass


    _wzs.WSGIRequestHandler = _SilentWSGIRequestHandler
except Exception:
    pass

# Dedicated app logger without timestamp/module
DXP_LOGGER = logging.getLogger('DXPUtility')
DXP_LOGGER.propagate = False
if not DXP_LOGGER.handlers:
    _h = logging.StreamHandler(sys.stdout)
    _h.setFormatter(logging.Formatter('%(levelname)s - %(message)s'))
    DXP_LOGGER.addHandler(_h)
DXP_LOGGER.setLevel(logging.INFO)

# In-memory cache of local uploads
LOCAL_UPLOADS: dict[str, str] = {}

# Cache parsed JSON data to avoid re-parsing
JSON_DATA_CACHE: dict[str, tuple] = {}


## HTML

# Shared S3 Browser partials to include across templates
def render_s3_browser_modal(env):
    """Render S3 browser modal with environment-specific bucket list"""
    return render_template_string(S3_BROWSER_MODAL_TEMPLATE, env=env)


S3_BROWSER_MODAL_TEMPLATE = r"""
      <!-- S3 Browser Modal (shared) -->
      <div id="s3Modal" class="modal">
         <div class="modal-content">
            <div class="modal-header">
               <strong><h2 style="margin: 0;">Amazon S3</h2></strong>
               <span class="close">&times;</span>
            </div>
            <div style="margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
               <select id="bucketSelect" class="border px-4 py-2 theme-transition" style="flex: 1; height: 46px;">
                  <option value="">Select a bucket...</option>
                  {% if env == 'dev' %}
                     <option value="pp-sequoiacloud-ods-us-west-2-dev">pp-sequoiacloud-ods-us-west-2-dev</option>
                     <option value="pp-sequoiacloud-ads-us-west-2-dev">pp-sequoiacloud-ads-us-west-2-dev</option>
                     <option value="pp-sequoiacloud-dwd-us-west-2-dev">pp-sequoiacloud-dwd-us-west-2-dev</option>
                     <option value="pp-data-us-west-2-dev">pp-data-us-west-2-dev</option>
                     <option value="aws-glue-scripts-512094374371-us-west-2">aws-glue-scripts-512094374371-us-west-2</option>
                  {% elif env == 'stage' %}
                     <option value="pp-sequoiacloud-ods-us-west-2-stage">pp-sequoiacloud-ods-us-west-2-stage</option>
                     <option value="pp-sequoiacloud-ads-us-west-2-stage">pp-sequoiacloud-ads-us-west-2-stage</option>
                     <option value="pp-sequoiacloud-dwd-us-west-2-stage">pp-sequoiacloud-dwd-us-west-2-stage</option>
                     <option value="pp-sequoiacloud-public-us-west-2-stage">pp-sequoiacloud-public-us-west-2-stage</option>
                     <option value="pp-data-us-west-2-stage">pp-data-us-west-2-stage</option>
                     <option value="aws-glue-scripts-749518382711-us-west-2">aws-glue-scripts-749518382711-us-west-2</option>
                  {% elif env == 'production' %}
                     <option value="pp-sequoiacloud-ods-us-west-2-production">pp-sequoiacloud-ods-us-west-2-production</option>
                     <option value="pp-sequoiacloud-ads-us-west-2-production">pp-sequoiacloud-ads-us-west-2-production</option>
                     <option value="pp-sequoiacloud-dwd-us-west-2-production">pp-sequoiacloud-dwd-us-west-2-production</option>
                     <option value="pp-data-us-west-2-production">pp-data-us-west-2-production</option>
                  {% endif %}
               </select>
               <button id="refreshBucketBtn" class="btn btn-ghost" title="Refresh current folder" style="height: 46px;">Refresh</button>
            </div>
            <div class="breadcrumb" id="breadcrumb"></div>
            <input type="text" class="browser-search" id="browserSearch" placeholder="Search files and folders..." style="height: 46px;">
            <div class="browser-content" id="browserContent">
               <div class="loading-spinner">Select a bucket to start browsing...</div>
            </div>
            <div style="margin-top: 15px; display: flex; justify-content: space-between; align-items: center;">
               <div style="font-size: 0.85em; color: #666;">
                  <span>💡 Tip: Press Refresh to get latest file</span>
               </div>
               <div>
                  <button id="selectFileBtn" class="btn btn-primary ml-2" disabled>Select File</button>
                  <button id="useFolderBtn" class="btn btn-secondary ml-2" disabled>Select Folder</button>
                  <button id="cancelBrowseBtn" class="btn btn-secondary ml-2">Cancel</button>
               </div>
            </div>
         </div>
      </div>
"""

S3_BROWSER_STYLES = r"""
      <style>
        /* S3 Browser Modal Styles (shared) */
        .modal { display: none; position: fixed; z-index: 10000; left: 0; top: 0; width: 100%; height: 100%; background-color: rgba(0, 0, 0, 0.5); backdrop-filter: blur(5px); -webkit-backdrop-filter: blur(5px); align-items: center; justify-content: center; }
        .modal-content { background-color: #fefefe; padding: 20px; border: 1px solid #888; width: 80%; max-width: 800px; max-height: 80vh; display: flex; flex-direction: column; }
        .modal-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 20px; }
        .close { color: #aaa; font-size: 28px; font-weight: 900; cursor: pointer; }
        .close:hover, .close:focus { color: black; }
        .breadcrumb { display: flex; align-items: center; gap: 5px; margin-bottom: 15px; flex-wrap: wrap; }
        .breadcrumb-item { cursor: pointer; color: #2563eb; text-decoration: underline; }
        .breadcrumb-item:hover { color: #1d4ed8; }
        .browser-content { flex: 1; overflow-y: auto; border: 1px solid #ddd; padding: 10px; }
        .browser-item { display: flex; align-items: center; gap: 8px; padding: 8px; cursor: pointer; justify-content: space-between; }
        .browser-item:hover { background-color: #f0f0f0; }
        .browser-item.selected { background-color: #e0e7ff; }
        .browser-search { width: 100%; padding: 8px; margin-bottom: 10px; border: 1px solid #ddd; height: 46px; }
        .loading-spinner { text-align: center; padding: 20px; }
        /* Dark Theme */
        body.dark-theme .modal-content { background-color: #1e293b; color: #e2e8f0; border-color: #334155; }
        body.dark-theme .close { color: #94a3b8; }
        body.dark-theme .close:hover { color: #e2e8f0; }
        body.dark-theme .browser-content { border-color: #334155; background-color: #0f172a; }
        body.dark-theme .browser-item:hover { background-color: #334155; }
        body.dark-theme .browser-item.selected { background-color: #475569; }
        body.dark-theme .browser-search { background-color: #334155; color: #e2e8f0; border-color: #475569; }
        body.dark-theme .breadcrumb-item { color: #ffffff; text-decoration: underline; }
        body.dark-theme #bucketSelect { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
        body.dark-theme #refreshBucketBtn { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
        body.dark-theme #refreshBucketBtn:hover { background-color: #475569 !important; }
        body.dark-theme #selectFileBtn { background-color: #1e3a8a !important; color: white !important; }
        body.dark-theme #selectFileBtn:hover { background-color: #1e40af !important; }
        body.dark-theme #selectFileBtn:disabled { background-color: #4b5563 !important; color: #9ca3af !important; }
        body.dark-theme #cancelBrowseBtn { background-color: #4b5563 !important; color: #e0e0e0 !important; }
        body.dark-theme #cancelBrowseBtn:hover { background-color: #6b7280 !important; }
        /* Pink Theme */
        body.pink-theme .modal-content { background-color: #fdf2f8; color: #831843; border-color: #f9a8d4; }
        body.white-theme .modal-content { background-color: #f8fafc; color: #1e293b; border-color: #e2e8f0; }
        body.pink-theme .browser-content { border-color: #f9a8d4; }
        body.pink-theme .browser-item:hover { background-color: #fce7f3; }
        body.pink-theme .browser-item.selected { background-color: #fbcfe8; }
        body.pink-theme .browser-search { background-color: #fce7f3; color: #831843; border-color: #f9a8d4; }
        body.pink-theme .breadcrumb-item { color: #ec4899; }
        body.pink-theme #bucketSelect { background-color: #fce7f3 !important; color: #831843 !important; border-color: #f9a8d4 !important; }
        body.pink-theme #refreshBucketBtn { background-color: #fce7f3 !important; color: #831843 !important; border-color: #f9a8d4 !important; }
        body.pink-theme #refreshBucketBtn:hover { background-color: #fbcfe8 !important; }
        body.pink-theme #selectFileBtn { background-color: #be185d !important; color: white !important; }
        body.pink-theme #selectFileBtn:hover { background-color: #9d174d !important; }
        body.pink-theme #cancelBrowseBtn { background-color: #f9a8d4 !important; color: #831843 !important; }
        /* White Theme */
        body.white-theme #bucketSelect { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        body.white-theme #refreshBucketBtn { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
        body.white-theme #refreshBucketBtn:hover { background-color: #f3f4f6 !important; }
        body.white-theme #selectFileBtn { background-color: #34d399 !important; color: white !important; }
        body.white-theme #selectFileBtn:hover:not(:disabled) { background-color: #10b981 !important; }
        body.white-theme #selectFileBtn:disabled { background-color: #9ca3af !important; }
        body.white-theme #cancelBrowseBtn { background-color: #e5e7eb !important; color: #1f2937 !important; }
        body.white-theme #cancelBrowseBtn:hover { background-color: #d1d5db !important; }
        body.white-theme .browser-search { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
      </style>
"""

S3_BROWSER_SCRIPT = r"""
      <script>
        // S3 Browser functionality (shared)
        (function(){
          const modal = document.getElementById('s3Modal');
          if (!modal) return; // If template doesn't include modal, skip
          const s3BrowseBtns = document.querySelectorAll('.s3BrowseBtn, #s3BrowseBtn');
          const closeBtn = document.getElementsByClassName('close')[0];
          const cancelBtn = document.getElementById('cancelBrowseBtn');
          const selectBtn = document.getElementById('selectFileBtn');
          const bucketSelect = document.getElementById('bucketSelect');
          const browserContent = document.getElementById('browserContent');
          const breadcrumb = document.getElementById('breadcrumb');
          const browserSearch = document.getElementById('browserSearch');
          const useFolderBtn = document.getElementById('useFolderBtn');

          let currentPath = '';
          let selectedFile = null;
          let allItems = [];
          let isLoading = false;
          let activeS3Input = null;

          const BUCKET_PATHS_KEY = 's3BrowserBucketPaths';
          function getSavedBucketPaths(){ try{ const s=localStorage.getItem(BUCKET_PATHS_KEY); return s?JSON.parse(s):{}; }catch(e){ return {}; } }
          function saveBucketPath(bucket, path){ try{ const p=getSavedBucketPaths(); p[bucket]=path; localStorage.setItem(BUCKET_PATHS_KEY, JSON.stringify(p)); }catch(e){} }
          function getLastPathForBucket(bucket){ const p=getSavedBucketPaths(); return p[bucket]||bucket; }

          s3BrowseBtns.forEach(btn => {
            btn.addEventListener('click', function(){
              const container = this.closest('.flex-1');
              activeS3Input = container ? container.querySelector('#s3_path') : document.getElementById('s3_path');
              modal.style.display = 'flex';
              const lastBucket = localStorage.getItem('lastS3Bucket');
              if (lastBucket && bucketSelect && bucketSelect.querySelector(`option[value="${lastBucket}"]`)){
                bucketSelect.value = lastBucket;
                bucketSelect.dispatchEvent(new Event('change'));
              }
            });
          });

          if (closeBtn) closeBtn.onclick = () => modal.style.display = 'none';
          if (cancelBtn) cancelBtn.onclick = () => modal.style.display = 'none';
          window.addEventListener('click', (e)=>{ if (e.target===modal) modal.style.display='none'; });

          if (bucketSelect) bucketSelect.onchange = function(){
            if (!this.value) return;
            const bucket=this.value; localStorage.setItem('lastS3Bucket', bucket);
            const lastPath=getLastPathForBucket(bucket); currentPath=lastPath; navigateToPath(lastPath);
          };

          function navigateToPath(path){ currentPath = path.replace(/\/+$/, ''); const currentBucket=currentPath.split('/')[0]; saveBucketPath(currentBucket, currentPath); updateBreadcrumb(); loadS3Content(currentPath); }

          let browseController=null;
          function loadS3Content(path, forceRefresh=false){
            isLoading=true; browserContent.innerHTML='<div class="loading-spinner">Loading...</div>'; selectedFile=null; selectBtn.disabled=true;
            try{ if (browseController) browseController.abort(); }catch(e){}
            browseController=new AbortController();
            return fetch('/browse-s3', {
              method:'POST', headers:{'Content-Type':'application/json'},
              body: JSON.stringify({ path: path, module: (document.querySelector('select[name="module"]')||{value:'dxp'}).value, force_refresh: forceRefresh }),
              signal: browseController.signal
            })
            .then(r=>r.json())
            .then(data=>{ isLoading=false; if (data.error){ browserContent.innerHTML = '<div style="color:red;padding:20px;">Error: '+data.error+'</div>'; return; } displayItems(data.items); })
            .catch(err=>{ if (String(err).includes('Abort')) return; isLoading=false; browserContent.innerHTML='<div style="color:red;padding:20px;">Error loading content: '+err+'</div>'; });
          }

          function displayItems(items){ browserContent.innerHTML=''; allItems = items||[]; allItems.sort((a,b)=>{ if(a.type==='folder'&&b.type==='file') return -1; if(a.type==='file'&&b.type==='folder') return 1; return a.name.localeCompare(b.name); });
            const canUseFolder = !!currentPath && currentPath.split('/').length>=1; if (useFolderBtn) useFolderBtn.disabled = !canUseFolder;
            allItems.forEach(item=>{ const div=document.createElement('div'); div.className='browser-item';
              let extra=''; 
              if(item.modified){ 
                const t=new Date(item.modified); 
                const today = new Date();
                const isToday = t.toDateString() === today.toDateString();
                const dateTimeText = isToday ? t.toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'}) : t.toLocaleDateString();
                extra += `<span style=\"color:#999;font-size:0.85em; display: inline; width: 80px; text-align: right;\">${dateTimeText}</span>`; 
              }
              if(item.size){ 
                extra += `<span style=\"color:#999;font-size:0.85em; display: inline; width: 60px; text-align: right;\">${item.size}</span>`; 
              }
              const canDelete = item.type==='file';
              const rightHtml = `${extra}${canDelete ? ' <button class=\"file-del\" title=\"Delete\" aria-label=\"Delete\" style=\"background:none;border:none;cursor:pointer;font-size:16px;\">🗑️</button>' : ''}`;
              div.innerHTML = `<div style=\"display: flex; align-items: center; gap: 8px; flex: 1;\"><span>${item.type==='folder'?'📁':'📄'}</span><span>${item.name}</span></div><div style=\"margin-left: auto; display: flex; gap: 10px; align-items: center;\">${rightHtml}</div>`;
              div.onclick=function(e){
                // Ignore clicks on delete icon
                if (e.target && e.target.classList && e.target.classList.contains('file-del')) return;
                if(item.type==='folder'){ browserSearch.value=''; navigateToPath((currentPath.replace(/\\+$/, '')) + '/' + item.name); }
                else { document.querySelectorAll('.browser-item').forEach(el=>el.classList.remove('selected')); div.classList.add('selected'); selectedFile = currentPath + '/' + item.name; selectBtn.disabled=false; }
              };
              // Hook delete icon
              if (canDelete) {
                const delBtn = div.querySelector('.file-del');
                if (delBtn) {
                  delBtn.addEventListener('click', function(ev){
                    ev.stopPropagation();
                    const full = currentPath + '/' + item.name;
                    const bucket = full.split('/')[0];
                    const key = full.substring(bucket.length + 1);
                    fetch('/delete-s3', { method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({ bucket, key }) })
                      .then(r=>r.json())
                      .then(data=>{ if (data && data.success) { loadS3Content(currentPath, true); } })
                      .catch(()=>{});
                  });
                }
              }
              browserContent.appendChild(div);
            });
            if (allItems.length===0){ browserContent.innerHTML='<div style="padding:20px;color:#666;">No files or folders found</div>'; }
            updateSearch();
          }

                     function updateBreadcrumb(){ 
             breadcrumb.innerHTML=''; 
             const parts=currentPath.split('/'); 
             parts.forEach((part, idx)=>{
               if(part){ 
                 const span=document.createElement('span'); 
                 span.className='breadcrumb-item'; 
                 span.textContent=part; 
                 span.onclick=function(){ 
                   const newPath=parts.slice(0, idx+1).join('/').replace(/\/+$/, ''); 
                   navigateToPath(newPath); 
                 }; 
                 breadcrumb.appendChild(span); 
                 if(idx<parts.length-1){ 
                   const chevron = document.createElement('span');
                   chevron.innerHTML = '&#x276F;'; // Unicode right-pointing chevron
                   chevron.style.cssText = 'margin: 0 3px; color: #666; font-size: 12px; font-weight: bold;';
                   breadcrumb.appendChild(chevron); 
                 } 
               } 
             }); 
           }

          function updateSearch(){ const q = (browserSearch.value||'').toLowerCase(); const items=[...document.querySelectorAll('.browser-item')]; items.forEach(div=>{ const name = (div.children[1]||{}).textContent||''; div.style.display = name.toLowerCase().includes(q) ? '' : 'none'; }); }
          if (browserSearch) browserSearch.addEventListener('input', updateSearch);

          if (selectBtn) selectBtn.onclick = function(){ if(!selectedFile||!activeS3Input) return; const s3url = 's3://' + selectedFile; activeS3Input.value = s3url; modal.style.display='none'; activeS3Input.dispatchEvent(new Event('input')); };
          if (useFolderBtn) useFolderBtn.onclick = function(){ if(!currentPath||!activeS3Input) return; let folderPath = currentPath; if (!/\/$/.test(folderPath)) folderPath += '/'; const s3url = 's3://' + folderPath; activeS3Input.value = s3url; modal.style.display='none'; activeS3Input.dispatchEvent(new Event('input')); };

          const refreshBtn = document.getElementById('refreshBucketBtn');
          if (refreshBtn) refreshBtn.onclick = function(){ if(!currentPath) return; const original=this.innerHTML; this.disabled=true; this.innerHTML='⏳ Refreshing...'; loadS3Content(currentPath, true).finally(()=>{ this.innerHTML=original; this.disabled=false; }); };

          document.addEventListener('keydown', function(e){ if(modal.style.display==='flex'){ if(e.key==='Escape'){ modal.style.display='none'; } else if (e.key==='F5' || (e.ctrlKey && e.key==='r')){ e.preventDefault(); if (refreshBtn) refreshBtn.click(); } } });
        })();
      </script>
"""

HOME_HTML = r"""
<!doctype html>
<html>
   <head>
      <title>Sequoia WorkBench</title>
      <link rel="icon" href="https://www.sequoia.com/wp-content/uploads/2020/03/sequoia-symbol.png" />
      <script src="https://cdn.tailwindcss.com"></script>
      <link rel="preconnect" href="https://fonts.googleapis.com">
      <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
      <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&display=swap" rel="stylesheet">
      <link href="https://fonts.googleapis.com/css2?family=Ubuntu+Mono:wght@400;700&display=swap" rel="stylesheet">
      <link href="https://fonts.googleapis.com/css2?family=Fira+Code:wght@400;700&display=swap" rel="stylesheet">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/fira-code@5.0.18/400.css">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/cascadia-code@5.0.7/400.css">
      <!-- Markdown rendering and syntax highlighting -->
      <link id="hljs-dark-css" rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/github-dark-dimmed.min.css">
      <link id="hljs-light-css" rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/github.min.css" disabled>
      <script src="https://cdnjs.cloudflare.com/ajax/libs/marked/12.0.2/marked.min.js"></script>
      <script src="https://cdnjs.cloudflare.com/ajax/libs/dompurify/3.1.6/purify.min.js"></script>
      <script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"></script>
      <script>
        try { marked.setOptions({ gfm: true, breaks: false, smartypants: true }); } catch (e) {}
      </script>
      <style>
         /* ==================== BASE STYLES ==================== */
         * { font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif !important; box-sizing: border-box; }
         body, html { margin: 0; padding: 0; }
         .theme-transition { transition: all 0.3s ease; }
         /* ==================== DARK THEME ==================== */
         body.dark-theme { background-color: #0f172a !important; color: #e2e8f0 !important; }
         .dark-theme .main-container { background-color: #1e293b !important; color: #e2e8f0 !important; border-radius: 0; }
         .dark-theme input, .dark-theme select, .dark-theme textarea { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
         .dark-theme input:focus, .dark-theme select:focus, .dark-theme textarea:focus { outline: none !important; border-color: #475569 !important; box-shadow: none !important; }
         .dark-theme label { color: #cbd5e1 !important; }
         .dark-theme h1, .dark-theme h2, .dark-theme h3 { color: #f1f5f9 !important; }
         .dark-theme .main-container p, .dark-theme .main-container div, .dark-theme .main-container span { color: #e2e8f0 !important; }
         .dark-theme a { color: #6366f1 !important; }
         .dark-theme a:hover { color: #818cf8 !important; }
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
         .dark-theme .theme-select { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
         .dark-theme .theme-dropdown { background-color: #374151 !important; color: #e0e7ff !important; border-color: #4b5563 !important; }
         .dark-theme .section-card { background-color: #1e293b; border: 1px solid #334155; }
         .dark-theme .greeting-text { color: #94a3b8 !important; }
         .dark-theme .witty-message { color: #cbd5e1 !important; }
         .dark-theme .big-greeting { color: #94a3b8 !important; }
         .dark-theme .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; }
         .dark-theme .big-day-date { color: #94a3b8 !important; }
         .dark-theme button:disabled { background-color: #2d2d2d !important; color: #666 !important; border-color: #444 !important; }
         .dark-theme .btn-ghost.selected, .dark-theme .btn-ghost.selected:hover { background-color: rgba(255, 255, 255, 0.1) !important; border-color: rgba(255, 255, 255, 0.2) !important; }
         .dark-theme .terminal-container { background: #0d1117 !important; border-color: #30363d !important; }
         .dark-theme #home-terminal-output { background: #0d1117 !important; color: #ffffff !important; }
         .dark-theme #home-terminal-input { background: #0d1117 !important; color: #ffffff !important; caret-color: #ffffff !important; }
         .dark-theme #chatbot-output { background: #0d1117 !important; color: #ffffff !important; }
         .dark-theme #chatbot-input { background: #0d1117 !important; color: #ffffff !important; caret-color: #ffffff !important; }
         .dark-theme #notesTextarea { background: #0d1117 !important; color: #ffffff !important; caret-color: #ffffff !important; }
         .dark-theme .modern-textarea { background-color: #1e293b; color: #e2e8f0; border-color: #4a5568; }
         .dark-theme .modern-textarea:focus { outline: none; border-color: #4a5568; box-shadow: none; }
         .dark-theme .modern-encrypt-btn { background-color: #1e3a8a; }
         .dark-theme .modern-decrypt-btn { background-color: #7c3aed; }
         .dark-theme .copy-icon-btn { background-color: #2d3748; color: #a0aec0; border-color: #4a5568; }
         .dark-theme .copy-icon-btn:hover { background-color: #4a5568; color: #e2e8f0; border-color: #718096; }
         .dark-theme .loader { background-color: #334155; }
         .dark-theme .loader::before { background-color: #6366f1; }
         /* ==================== JSON SYNTAX HIGHLIGHTING - DARK THEME ==================== */
         .dark-theme .json-key { color: #9cdcfe !important; }
         .dark-theme .json-string { color: #ce9178 !important; }
         .dark-theme .json-number { color: #b5cea8 !important; }
         .dark-theme .json-boolean { color: #569cd6 !important; }
         .dark-theme .json-null { color: #569cd6 !important; }
         .dark-theme .json-bracket { color: #ffd700 !important; }
         .dark-theme .json-comma { color: #cccccc !important; }
         .dark-theme .json-toggle { color: #808080 !important; cursor: pointer; }
         .dark-theme .json-toggle:hover { color: #cccccc !important; }
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
         .white-theme .terminal-container { background: #f9fafb !important; border-color: #d1d5db !important; }
         .white-theme #home-terminal-output { background: #f9fafb !important; color: #4b5563 !important; }
         .white-theme #home-terminal-input { background: #f9fafb !important; color: #4b5563 !important; caret-color: #4b5563 !important; }
         .white-theme #chatbot-output { background: #f9fafb !important; color: #4b5563 !important; }
         .white-theme #chatbot-input { background: #f9fafb !important; color: #4b5563 !important; caret-color: #4b5563 !important; }
         .white-theme #notesTextarea { background: #f9fafb !important; color: #4b5563 !important; caret-color: #4b5563 !important; }
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
         /* ==================== PINK THEME ==================== */
         body.pink-theme { background-color: #fdf2f8 !important; color: #831843 !important; }
         .pink-theme .main-container { background-color: #fdf2f8 !important; color: #831843 !important; border-radius: 0; }
         .pink-theme input, .pink-theme select, .pink-theme textarea { background-color: #fdf2f8 !important; color: #831843 !important; border-color: #fbcfe8 !important; }
         .pink-theme input:focus, .pink-theme select:focus, .pink-theme textarea:focus { outline: none !important; border-color: #fbcfe8 !important; box-shadow: none !important; }
         .pink-theme label { color: #be185d !important; }
         .pink-theme h1, .pink-theme h2, .pink-theme h3 { color: #831843 !important; }
         .pink-theme .main-container p, .pink-theme .main-container div, .pink-theme .main-container span { color: #831843 !important; }
         .pink-theme a { color: #ec4899 !important; }
         .pink-theme a:hover { color: #db2777 !important; }
         .pink-theme .btn-primary { background-color: #ec4899 !important; color: #ffffff !important; }
         .pink-theme .btn-primary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-secondary { background-color: #ec4899 !important; color: #ffffff !important; }
         .pink-theme .btn-secondary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-success { background-color: #db2777 !important; color: #ffffff !important; }
         .pink-theme .btn-success:hover:not(:disabled) { background-color: #be185d !important; }
         .pink-theme .btn-danger { background-color: #be185d !important; color: #ffffff !important; }
         .pink-theme .btn-danger:hover:not(:disabled) { background-color: #9d174d !important; }
         .pink-theme .btn-ghost { background-color: transparent !important; color: #be185d !important; border-color: #fbcfe8 !important; }
         .pink-theme .btn-ghost:hover:not(:disabled) { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
         .pink-theme .theme-select { background-color: #fce7f3 !important; color: #831843 !important; border-color: #fbcfe8 !important; }
         .pink-theme .theme-dropdown { background-color: #fdf2f8 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         .pink-theme .section-card { background-color: #fdf2f8; border: 1px solid #fbcfe8; }
         .pink-theme .greeting-text { color: #be185d !important; }
         .pink-theme .witty-message { color: #db2777 !important; }
         .pink-theme button:disabled { background-color: #fce7f3 !important; color: #d8b4c6 !important; border-color: #f3c6dd !important; }
         .pink-theme .btn-ghost.selected, .pink-theme .btn-ghost.selected:hover { background-color: rgba(236, 72, 153, 0.1) !important; border-color: rgba(236, 72, 153, 0.2) !important; }
         .pink-theme .terminal-container { background: #fce7f3 !important; border-color: #fbcfe8 !important; }
         .pink-theme #home-terminal-output { background: #fce7f3 !important; color: #831843 !important; }
         .pink-theme #home-terminal-input { background: #fce7f3 !important; color: #be185d !important; caret-color: #be185d !important; }
         .pink-theme #chatbot-output { background: #fce7f3 !important; color: #831843 !important; }
         .pink-theme #chatbot-input { background: #fce7f3 !important; color: #be185d !important; caret-color: #be185d !important; }
         .pink-theme #notesTextarea { background: #fce7f3 !important; color: #831843 !important; caret-color: #831843 !important; }
         .pink-theme .modern-textarea { background-color: #fdf2f8; color: #831843; border-color: #f3e8ff; }
         .pink-theme .modern-textarea:focus { outline: none; border-color: #f3e8ff; box-shadow: none; }
         .pink-theme .modern-encrypt-btn { background-color: #f9a8d4; }
         .pink-theme .modern-decrypt-btn { background-color: #c084fc; }
         .pink-theme .copy-icon-btn { background-color: #fce7f3; color: #be185d; border-color: #f9a8d4; }
         .pink-theme .copy-icon-btn:hover { background-color: #fbcfe8; color: #831843; border-color: #ec4899; }
         .pink-theme .loader { background-color: #fbcfe8; }
         .pink-theme .loader::before { background-color: #ec4899; }
         /* ==================== JSON SYNTAX HIGHLIGHTING - PINK THEME ==================== */
         .pink-theme .json-key { color: #be185d !important; }
         .pink-theme .json-string { color: #db2777 !important; }
         .pink-theme .json-number { color: #059669 !important; }
         .pink-theme .json-boolean { color: #7c3aed !important; }
         .pink-theme .json-null { color: #7c3aed !important; }
         .pink-theme .json-bracket { color: #831843 !important; }
         .pink-theme .json-comma { color: #831843 !important; }
         .pink-theme .json-toggle { color: #ec4899 !important; cursor: pointer; }
         .pink-theme .json-toggle:hover { color: #be185d !important; }
         /* ==================== COMMON BUTTON STYLES ==================== */
         .btn { padding: 0.625rem 1.25rem; font-weight: 500; border-radius: 0; transition: all 0.2s ease; border: none; cursor: pointer; display: inline-flex; align-items: center; justify-content: center; gap: 0.5rem; font-size: 0.875rem; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
         .btn:hover { transform: translateY(-1px); box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06); }
         .btn:active { transform: translateY(0); box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
         .btn:disabled { opacity: 0.5; cursor: not-allowed; transform: none; box-shadow: none; }
         .btn-primary { background-color: #6366f1; color: white !important; }
         .btn-primary:hover:not(:disabled) { background-color: #4f46e5; }
         .btn-secondary { background-color: #64748b; color: white !important; }
         .btn-secondary:hover:not(:disabled) { background-color: #475569; }
         .btn-success { background-color: #10b981; color: white !important; }
         .btn-success:hover:not(:disabled) { background-color: #059669; }
         .btn-danger { background-color: #ef4444; color: white !important; }
         .btn-danger:hover:not(:disabled) { background-color: #dc2626; }
         .btn-warning { background-color: #f59e0b; color: white !important; }
         .btn-warning:hover:not(:disabled) { background-color: #d97706; }
         .btn-ghost { background-color: transparent; color: #64748b; box-shadow: none; border: 1px solid #e2e8f0; }
         .btn-ghost:hover:not(:disabled) { background-color: #f8fafc; border-color: #cbd5e1; box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); }
         .btn-icon { padding: 0 !important; font-size: 1.125rem !important; line-height: 1 !important; height: 46px; width: 46px; display: inline-flex; align-items: center; justify-content: center; }
         button.s3BrowseBtn.btn.btn-ghost.btn-icon, #s3BrowseBtn.btn-icon { font-size: 18px !important; line-height: 1 !important; }
         button.s3BrowseBtn, #s3BrowseBtn { height: 46px !important; width: 46px !important; padding: 0 !important; display: inline-flex !important; align-items: center !important; justify-content: center !important; line-height: 46px !important; font-family: 'Apple Color Emoji','Segoe UI Emoji','Noto Color Emoji', system-ui, sans-serif !important; }
         button:disabled { opacity: 0.4; cursor: not-allowed; }
         /* ==================== COMMON INPUT STYLES ==================== */
         input[type="text"], select, textarea { border-radius: 0; border: 1px solid #e2e8f0; padding: 0.625rem 1rem; font-size: 0.875rem; transition: all 0.2s ease; }
         input[type="text"]:focus, select:focus, textarea:focus { outline: none; border-color: inherit; box-shadow: none; }
         input#s3_path { font-weight: 400 !important; }
         /* ==================== COMMON STYLES ==================== */
         .section-card { border-radius: 0; padding: 1.5rem; box-shadow: 0 1px 3px 0 rgba(0, 0, 0, 0.1), 0 1px 2px 0 rgba(0, 0, 0, 0.06); }
         .greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; }
         p.greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; }
         .witty-message { font-weight: 400 !important; font-size: 0.875rem !important; margin-top: 0.25rem !important; opacity: 0.8; }
         .btn-ghost.selected, .btn-ghost.selected:hover { background-color: rgba(255, 255, 255, 0.1) !important; border-color: rgba(255, 255, 255, 0.2) !important; }
         /* Big Time Display Styling */
         .big-time-display { display: flex; flex-direction: row; justify-content: flex-end; align-items: center; margin-bottom: 0.5rem; }
         .time-section { text-align: right; height: 46px !important; display: flex !important; flex-direction: column !important; justify-content: center !important; align-items: flex-end !important; } }
         .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; margin-bottom: 0.125rem !important; }
         .big-day-date { font-size: 0.875rem !important; font-weight: 500 !important; color: #94a3b8 !important; line-height: 1.2 !important; }

         /* Theme-specific time display colors for home page */
         body.dark-theme .big-time-display .big-time { color: #e2e8f0 !important; }
         body.dark-theme .big-time-display .big-day-date { color: #94a3b8 !important; }
         body.white-theme .big-time-display .big-time { color: #1e293b !important; }
         body.white-theme .big-time-display .big-day-date { color: #64748b !important; }
         body.pink-theme .big-time-display .big-time { color: #831843 !important; }
         body.pink-theme .big-time-display .big-day-date { color: #be185d !important; }

         /* Code editor page time display font sizes */
         .code-edit-page .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
         .code-edit-page .big-day-date { font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }

         /* Force font sizes for all time displays */
         .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
         .big-day-date { font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }
         /* ==================== LOADER STYLES ==================== */
         .loader-overlay { position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0, 0, 0, 0.3); backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px); display: none; justify-content: center; align-items: center; z-index: 9999; }
         .loader-container { display: flex; flex-direction: column; align-items: center; justify-content: center; text-align: center; }
         .loader { width: 800px !important; height: 5px !important; max-width: 90vw !important; min-width: 300px !important; background-color: #e2e8f0; border-radius: 0; overflow: hidden; position: relative; margin: 0 auto; }
         .loader-container .loader { height: 5px !important; }
         .loader::before { content: ''; position: absolute; top: 0; left: 0; width: var(--progress, 0%); height: 100%; background-color: #6366f1; transition: width 0.3s ease; border-radius: 0; }
         .loader-percentage { font-size: 24px; font-weight: 800; color: white; margin-top: 20px; text-align: center; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale; }
         .loader-text { color: white; margin-top: 20px; font-size: 18px; font-weight: 600; text-align: center; width: 100%; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale; }
         .download-animation { display: inline-block; width: 20px; height: 20px; margin-left: 10px; border: 3px solid rgba(255,255,255,.3); border-radius: 50%; border-top-color: #fff; animation: spin 1s ease-in-out infinite; }
         @keyframes slide { 0% { left: -100%; } 50% { left: 100%; } 100% { left: -100%; } }
         /* ==================== TERMINAL STYLES ==================== */
         .terminal-container { border: 1px solid #30363d; overflow: hidden; }
         /* Restrict monospace to terminal only; do not affect chat */
         #home-terminal-output, #home-terminal-output *, #home-terminal-input, #home-terminal-input * { font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 14px !important; line-height: 1.5 !important; font-weight: normal !important; }
         #home-terminal-input { font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 14px; line-height: 1.5; font-weight: normal; color: #ffffff !important; }
         #home-terminal-output { font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 14px; line-height: 1.5; font-weight: normal; color: #ffffff !important; }
         #home-terminal-input:focus { outline: none !important; box-shadow: none !important; -webkit-box-shadow: none !important; border-color: transparent !important; }
         .dark-theme #home-terminal-output, .dark-theme #home-terminal-output * { color: #ffffff !important; }
         .dark-theme #home-terminal-input { color: #ffffff !important; }
         .dark-theme #home-terminal-output, .dark-theme #home-terminal-output *, .dark-theme #home-terminal-input, .dark-theme #home-terminal-input * { font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 14px !important; line-height: 1.5 !important; font-weight: normal !important; color: #ffffff !important; }
         /* Chat bubbles */
         .chat-output { display: flex; flex-direction: column; gap: 12px; padding: 16px; overflow-y: auto; flex: 1 1 auto; min-height: 0; overflow-anchor: none; }
         /* Make chatbot input scrollable with a sensible cap */
         #chatbot-input { max-height: 30vh; overflow-y: auto !important; box-sizing: border-box; }
         .chat-row { display: flex; width: 100%; }
         .chat-msg { max-width: 80%; padding: 10px 12px; border-radius: 0; box-shadow: 0 1px 2px 0 rgba(0,0,0,0.05); word-wrap: break-word; white-space: normal; line-height: 1.6; font-size: 0.95rem; }
         .chat-msg p { margin: 0.25rem 0; }
         .chat-msg pre, .chat-msg code { font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; }
         .chat-msg pre { padding: 10px; border-radius: 0; overflow: auto; }
         .chat-msg code { padding: 1px 4px; border-radius: 0; }
         .chat-user-line { margin: 4px 2px; font-size: 0.95rem; line-height: 1.6; white-space: pre-wrap; color: inherit; align-self: flex-end; text-align: right; max-width: 80%; }

         /* Theme-aware bubble colors */
         .dark-theme .chat-msg.user { background: #334155; color: #e2e8f0; margin-left: auto; }
         .dark-theme .chat-msg.assistant { background: #1f2937; color: #e5e7eb; margin-right: auto; }
         .dark-theme .chat-msg pre, .dark-theme .chat-msg code { background: #0b1220; color: #e2e8f0; }

         .white-theme .chat-msg.user { background: #e5e7eb; color: #111827; margin-left: auto; }
         .white-theme .chat-msg.assistant { background: #ffffff; color: #1f2937; border: 1px solid #e5e7eb; margin-right: auto; }
         .white-theme .chat-msg pre, .white-theme .chat-msg code { background: #f3f4f6; color: #111827; }

         .pink-theme .chat-msg.user { background: #f9a8d4; color: #831843; margin-left: auto; }
         .pink-theme .chat-msg.assistant { background: #fce7f3; color: #831843; border: 1px solid #fbcfe8; margin-right: auto; }
         .pink-theme .chat-msg pre, .pink-theme .chat-msg code { background: #fbcfe8; color: #831843; }

         /* Fullscreen Chat */
         #chatbot-section.chat-fullscreen { position: fixed; inset: 0; z-index: 9999; background: inherit; padding: 0; margin: 0 !important; display: flex; flex-direction: column; height: 100vh; width: 100vw; overflow: hidden; }
         #chatbot-section.chat-fullscreen .terminal-container { height: 100% !important; flex: 1 1 auto; margin: 0 !important; min-height: 0; display: grid !important; grid-template-rows: 1fr auto; overflow-anchor: none; }
         #chatbot-section.chat-fullscreen .chat-output { flex: 1 1 auto; min-height: 0; overflow-y: auto; grid-row: 1; }
         /* Hide chat header and section chrome in fullscreen */
         #chatbot-section.chat-fullscreen { box-shadow: none; border: none; }
         #chatbot-section.chat-fullscreen > .flex.items-center { display: none !important; }
         #chatbot-section.chat-fullscreen .terminal-container { border: none !important; }
         /* Keep input row pinned to bottom in fullscreen and prevent bleed */
         #chatbot-section.chat-fullscreen .terminal-container > div:last-child { grid-row: 2; position: static; height: 56px; }
         #chatbot-section.chat-fullscreen #chatbot-input { height: 100% !important; max-height: 35vh !important; overflow-y: auto !important; }

         /* Theme-aware fullscreen backgrounds/colors */
         .dark-theme #chatbot-section.chat-fullscreen,
         .dark-theme #chatbot-section.chat-fullscreen .terminal-container,
         .dark-theme #chatbot-section.chat-fullscreen #chatbot-output,
         .dark-theme #chatbot-section.chat-fullscreen #chatbot-input { background: #0d1117 !important; color: #ffffff !important; }

         .white-theme #chatbot-section.chat-fullscreen,
         .white-theme #chatbot-section.chat-fullscreen .terminal-container,
         .white-theme #chatbot-section.chat-fullscreen #chatbot-output,
         .white-theme #chatbot-section.chat-fullscreen #chatbot-input { background: #ffffff !important; color: #1f2937 !important; }

         .pink-theme #chatbot-section.chat-fullscreen,
         .pink-theme #chatbot-section.chat-fullscreen .terminal-container,
         .pink-theme #chatbot-section.chat-fullscreen #chatbot-output,
         .pink-theme #chatbot-section.chat-fullscreen #chatbot-input { background: #fdf2f8 !important; color: #831843 !important; }

         /* Theme-aware borders for terminal container */
         .dark-theme #chatbot-section .terminal-container { border-color: #30363d !important; }
         .white-theme #chatbot-section .terminal-container { border-color: #e2e8f0 !important; }
         .pink-theme #chatbot-section .terminal-container { border-color: #f9a8d4 !important; }

         /* Theme-aware border for input divider (override inline grey) */
         .dark-theme #chatbot-section .terminal-container > div:last-child { border-top: 1px solid #30363d !important; }
         .white-theme #chatbot-section .terminal-container > div:last-child { border-top: 1px solid #e2e8f0 !important; }
         .pink-theme  #chatbot-section .terminal-container > div:last-child { border-top: 1px solid #f9a8d4 !important; }

         /* Typing indicator (no bubble) */
         .typing-row { display: flex; width: 100%; }
         .typing-indicator { margin-right: auto; display: inline-flex; gap: 6px; padding: 6px 0; align-items: center; opacity: 0.85; }
         .typing-indicator .dot { width: 6px; height: 6px; border-radius: 50%; background: currentColor; animation: typing-bounce 1.2s infinite ease-in-out; }
         .typing-indicator .dot:nth-child(2) { animation-delay: 0.2s; }
         .typing-indicator .dot:nth-child(3) { animation-delay: 0.4s; }
         @keyframes typing-bounce { 0%, 80%, 100% { transform: translateY(0); opacity: 0.3; } 40% { transform: translateY(-4px); opacity: 1; } }

         /* User messages: normal font and sizing */
         .chat-user-line { font-family: inherit !important; font-size: 0.95rem; line-height: 1.6; }
         .chat-user-line pre, .chat-user-line code { font-family: inherit !important; font-size: inherit; }
         .chat-user-line pre { text-align: left; background: transparent; border: none; padding: 0; margin: 0; white-space: pre-wrap; overflow: hidden; max-width: 100%; }
         @media (max-width: 640px) {
           #textEditToggleBtn .vs-icon { display: none !important; }
           #textEditToggleBtn .vs-emoji { display: inline !important; }
         }
         @media (min-width: 641px) {
           #textEditToggleBtn .vs-emoji { display: none !important; }
         }
      </style>
   </head>
   <body class="min-h-screen theme-transition">
      <script>
         // Get theme from server and localStorage, prioritize localStorage for persistence
         const serverTheme = '{{ theme }}';
         const savedTheme = localStorage.getItem('workbench-theme');
         const currentTheme = savedTheme || serverTheme || 'dark';

         // Apply the theme
         document.body.className = document.body.className.replace(/\s*(dark|white|pink)-theme/g, '') + ' ' + currentTheme + '-theme';

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
      </script>
      <script>
         function setTheme(theme) {
           // Apply theme immediately without transition
           document.documentElement.className = theme + '-theme';
           document.body.className = 'min-h-screen ' + theme + '-theme';
           // Save to localStorage for persistence across sessions
           localStorage.setItem('workbench-theme', theme);
           // Update dropdown selection
           const dropdown = document.getElementById('theme-select');
           if (dropdown) dropdown.value = theme;

           // Update highlight.js theme based on app theme
           if (typeof updateHljsTheme === 'function') updateHljsTheme();

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

         // Toggle highlight.js stylesheet for current theme
        function updateHljsTheme() {
          try {
            const darkLink = document.getElementById('hljs-dark-css');
            const lightLink = document.getElementById('hljs-light-css');
            const isLight = document.body.className.includes('white-theme') || document.body.className.includes('pink-theme');
            if (darkLink && lightLink) {
              lightLink.disabled = !isLight;
              darkLink.disabled = isLight;
            }
          } catch (e) {}
        }

        function setEnvironment(environment) {
           console.log('Environment changed to:', environment);

           // Save to server session and reload page to update all bucket references
           fetch('/set-environment', {
             method: 'POST',
             headers: {
               'Content-Type': 'application/json',
             },
             body: JSON.stringify({environment: environment})
           }).then(response => response.json())
             .then(data => {
               console.log('Environment saved to server:', data);
               // Reload page to update all bucket references
               window.location.reload();
             })
             .catch(error => {
               console.error('Error saving environment:', error);
             });
         }

         // Set active dropdown on load
         window.addEventListener('DOMContentLoaded', function() {
           // Immediate notes initialization on DOM ready
           setTimeout(function() {
             const notesTextarea = document.getElementById('notesTextarea');
             if (notesTextarea) {
               const savedNotes = localStorage.getItem('sequoia-notes');
               if (savedNotes) {
                 notesTextarea.value = savedNotes;
                 console.log('Notes loaded on DOM ready:', savedNotes.length, 'characters');
               }
             }
           }, 50);
           const activeTheme = localStorage.getItem('workbench-theme') || serverTheme || 'dark';
           const themeDropdown = document.getElementById('theme-select');
           if (themeDropdown) themeDropdown.value = activeTheme;
           // Apply theme immediately without transition
           document.documentElement.className = activeTheme + '-theme';
           document.body.className = 'min-h-screen ' + activeTheme + '-theme';
           if (typeof updateHljsTheme === 'function') updateHljsTheme();

           // Set environment dropdown value from server
           const envDropdown = document.getElementById('env-select');
           if (envDropdown) {
             envDropdown.value = '{{ env }}';
           }

           // Load and set text edit button state
           const textEditBtn = document.getElementById('textEditToggleBtn');
           if (textEditBtn) {
             const isEnabled = loadRawEditPreference();
             if (isEnabled) {
               textEditBtn.classList.add('selected');
             } else {
               textEditBtn.classList.remove('selected');
             }
             console.log('Text edit button loaded:', isEnabled);
           }

           // Add form submission handler to update hidden field
           const mainForm = document.getElementById('main-form');
           if (mainForm) {
             mainForm.addEventListener('submit', function() {
               updateRawEditHiddenField();
             });
           }

           // Initialize terminal input event listener
           setTimeout(function() {
             var input = document.getElementById('home-terminal-input');
             if (input) {
               input.addEventListener('keydown', function(e) {
                 if (e.key === 'Enter') {
                   e.preventDefault();
                   var command = this.value.trim();
                   if (command) {
                     window.executeTerminalCommand(command);
                     this.value = '';
                   }
                 }
               });
             }

             // Initialize chatbot input event listener
             var chatbotInput = document.getElementById('chatbot-input');
             if (chatbotInput) {
               // Auto-resize on input (respects CSS max-height)
              const autoResize = function(el){
                const section = document.getElementById('chatbot-section');
                const inFullscreen = !!(section && section.classList.contains('chat-fullscreen'));
                if (inFullscreen) {
                  // Keep fixed height in fullscreen to avoid pushing the divider upwards
                  el.style.height = '56px';
                  return;
                }
                const min=44;
                el.style.height = 'auto';
                const h = Math.max(el.scrollHeight, min);
                const computed = window.getComputedStyle(el);
                const maxH = parseFloat(computed.maxHeight) || Infinity;
                el.style.height = Math.min(h, maxH) + 'px';
              };
              chatbotInput.addEventListener('input', function(){ autoResize(this); });
               // Initialize height
               autoResize(chatbotInput);
               // Key handling: Enter to send, Shift+Enter for newline
               chatbotInput.addEventListener('keydown', function(e) {
                 if (e.key === 'Enter') {
                   if (e.shiftKey) {
                     // allow newline and grow
                     return;
                   }
                   e.preventDefault();
                   var query = this.value.trim();
                   if (query) {
                     window.executeChatbotQuery(query);
                     this.value = '';
                     autoResize(this);
                   }
                 }
               });
             }
                      }, 100);

           // Add welcome messages
           setTimeout(function() {
             // Add welcome message to terminal
             var output = document.getElementById('home-terminal-output');
             if (output) {
               // Theme-aware welcome message
               var theme = document.body.className.includes('white-theme') ? 'white' : 
                          document.body.className.includes('pink-theme') ? 'pink' : 'dark';

               var welcomeColor = theme === 'dark' ? '#00ff00' : 
                                 theme === 'white' ? '#4b5563' : '#831843';
               var helpColor = theme === 'dark' ? '#00ff00' : 
                              theme === 'white' ? '#6b7280' : '#be185d';

               output.innerHTML = '<span style="color: ' + welcomeColor + ';">Welcome to Sequoia WorkBench Terminal</span><br><span style="color: ' + helpColor + ';">Type some command e.g. pip install pandas</span><br><br>';
             }

            }, 100);

           // Restore open section state
           setTimeout(function() {
             console.log('About to restore sections...');
             restoreOpenSection();
           }, 1000);

           // FORCE MONACO FONT - JAVASCRIPT OVERRIDE
           setTimeout(function() {
             var terminalOutput = document.getElementById('home-terminal-output');
             var terminalInput = document.getElementById('home-terminal-input');

             if (terminalOutput) {
               terminalOutput.style.fontFamily = "'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace";
               terminalOutput.style.fontSize = "14px";
               terminalOutput.style.lineHeight = "1.5";
               terminalOutput.style.fontWeight = "normal";
               console.log('Forced Monaco font on terminal output');
             }

             if (terminalInput) {
               terminalInput.style.fontFamily = "'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace";
               terminalInput.style.fontSize = "14px";
               terminalInput.style.lineHeight = "1.5";
               terminalInput.style.fontWeight = "normal";
               console.log('Forced Monaco font on terminal input');
             }
           }, 2000);

           // Final backup notes initialization on window load
           window.addEventListener('load', function() {
             setTimeout(function() {
               const notesTextarea = document.getElementById('notesTextarea');
               if (notesTextarea) {
                 const savedNotes = localStorage.getItem('sequoia-notes');
                 if (savedNotes && !notesTextarea.value) {
                   notesTextarea.value = savedNotes;
                   console.log('Notes loaded on window load (backup):', savedNotes.length, 'characters');
                 }
               }
             }, 100);
           });

            // Show any persisted modal error from previous redirect (robust)
            (function(){
              function tryShow(msg){
                if (typeof showModalMessage === 'function') {
                  showModalMessage('Error', msg);
                  try { localStorage.removeItem('workbench-pending-modal-error'); } catch(e) {}
                } else {
                  setTimeout(function(){ tryShow(msg); }, 150);
                }
              }
              try {
                const pendingErr = localStorage.getItem('workbench-pending-modal-error');
                if (pendingErr) {
                  tryShow(pendingErr);
                }
              } catch (e) {}
              // Also support error passed via URL query (?error=...)
              try {
                const params = new URLSearchParams(window.location.search);
                const urlErr = params.get('error');
                if (urlErr) {
                  tryShow(urlErr);
                }
              } catch (e) {}
            })();

         });

         // Define dismissLoader function globally
         function dismissLoader(event) {
           const loader = document.getElementById('loader');
           if (loader && loader.classList.contains('download-mode')) {
             loader.style.display = 'none';
             loader.classList.remove('download-mode');
           }
         }

         // Safety: hide any stuck loader on page load
         window.addEventListener('load', function() {
           setTimeout(() => {
             const loader = document.getElementById('loader');
             if (loader && loader.style.display !== 'none') {
               loader.style.display = 'none';
             }
           }, 500);
         });

         // Module change handler
         function updateModule(module) {
           console.log('Setting module to:', module);
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
               // Also update the encryption module selector
               const cryptModuleSelect = document.querySelector('select[name="crypt_module"]');
               if (cryptModuleSelect) {
                 cryptModuleSelect.value = module;
               }
             })
             .catch(error => {
               console.error('Error saving module:', error);
             });
         }

         // Raw edit preference functions
         function saveRawEditPreference(isChecked) {
           try {
             localStorage.setItem('workbench-raw-edit', isChecked ? 'true' : 'false');
             console.log('Raw edit preference saved:', isChecked);
           } catch (error) {
             console.error('Error saving raw edit preference:', error);
           }
         }

         function loadRawEditPreference() {
           try {
             const saved = localStorage.getItem('workbench-raw-edit');
             return saved === 'true';
           } catch (error) {
             console.error('Error loading raw edit preference:', error);
             return false;
           }
         }

         // Toggle text edit preference
         function toggleTextEdit() {
           const textEditBtn = document.getElementById('textEditToggleBtn');
           if (textEditBtn) {
             const isCurrentlyEnabled = textEditBtn.classList.contains('selected');
             const newState = !isCurrentlyEnabled;

             if (newState) {
               textEditBtn.classList.add('selected');
             } else {
               textEditBtn.classList.remove('selected');
             }

             saveRawEditPreference(newState);
           }
         }

         // Update hidden field before form submission
         function updateRawEditHiddenField() {
           const rawEditInput = document.getElementById('raw_edit_input');
           const textEditBtn = document.getElementById('textEditToggleBtn');
           if (rawEditInput && textEditBtn) {
             const isEnabled = textEditBtn.classList.contains('selected');
             rawEditInput.value = isEnabled ? 'true' : 'false';
             console.log('Raw edit hidden field updated:', rawEditInput.value);
           } else {
             console.warn('Raw edit elements not found:', {rawEditInput: !!rawEditInput, textEditBtn: !!textEditBtn});
           }
         }
      </script>
      <!-- Loading overlay -->
      <div class="loader-overlay" id="loader" style="display: none;">
         <div class="loader-container" onclick="event.stopPropagation()">
            <div class="loader-text" id="loader-text" style="margin-bottom: 30px;">LOADING</div>
            <div class="loader"></div>
            <div class="loader-percentage" id="loader-percentage">0%</div>
         </div>
      </div>
      <div class="w-full min-h-screen main-container theme-transition p-8">
         <div class="flex items-center justify-between mb-12">
            <div class="flex items-center">
               <img src="{{ logo }}" class="h-16 w-auto mr-1" alt="Logo" />
               <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
            </div>
            <!-- Right side: Big Time Display, Environment, and Theme Toggle -->
            <div class="flex items-center space-x-4">
               <div class="text-right">
                  <div class="big-time-display" style="margin-top: 0px;">
                     <div class="time-section" style="align-items: flex-end !important; justify-content: flex-end !important;">
                        <div class="big-time" style="font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important;">{{ big_time_display.big_time }}</div>
                        <div class="big-day-date" style="font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important;">{{ big_time_display.day_date }}</div>
                     </div>
                  </div>
               </div>
               <div class="flex items-center space-x-2">
                  <select id="env-select" class="border px-4 py-2 text-base theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="setEnvironment(this.value)">
                  <option value="dev" {{ 'selected' if env == 'dev' else '' }}>Dev</option>
                  <option value="stage" {{ 'selected' if env == 'stage' else '' }}>Stage</option>
                  <option value="production" {{ 'selected' if env == 'production' else '' }}>Production</option>
                  </select>
                  <select id="theme-select" class="border px-4 py-2 text-base theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="setTheme(this.value)">
                     <option value="dark">🌃   Dark</option>
                     <option value="white">🔆  White</option>
                     <option value="pink">🌸  Pink</option>
                  </select>
               </div>
            </div>
         </div>
         <!-- Main form -->
         <form action="{{ url_for('home') }}"
            method="post"
            enctype="multipart/form-data"
            class="space-y-4"
            id="main-form">
            <!-- Row 1: S3 Path -->
            <div class="flex items-center space-x-2">
               <!-- Paste button -->
               <button
                  type="button"
                  id="pasteBtn"
                  class="btn btn-ghost btn-icon"
                  title="Paste S3 path"
                  >📋</button>
               <!-- S3 browse button -->
               <button
                  type="button"
                  id="s3BrowseBtn"
                  class="btn btn-ghost btn-icon"
                  title="Browse S3"
                  >🪣️</button>
               <!-- Edit S3 button - moved right before S3 input -->
               <button
                  type="submit"
                  id="editS3Btn"
                  name="action"
                  value="edit"
                  class="btn btn-ghost btn-icon"
                  title="Edit S3 file"
                  disabled
                  >✏️</button>
               <!-- S3 path input -->
               <input
                  type="text"
                  id="s3_path"
                  name="s3_path"
                  class="flex-grow border px-4 py-2 text-base theme-transition"
                  placeholder="s3://bucket/path/to/file.ext"
                  value="{{ last_path }}"
                  style="height: 46px;"
                  autocomplete="off"
                  />
               <button id="downloadAllBtn"
                  type="button"
                  class="btn btn-success"
                  style="height: 46px;"
                  disabled>
               Extract
               </button>
               <select
                  name="module"
                  class="border px-4 py-2 text-base theme-transition"
                  style="font-weight: 500 !important; min-width: 120px; height: 46px;"
                  onchange="updateModule(this.value)"
                  >
               <option value="dxp" {{ 'selected' if module == 'dxp' else '' }}>dxp</option>
               <option value="dap" {{ 'selected' if module == 'dap' else '' }}>dap</option>
               <option value="pa" {{ 'selected' if module == 'pa' else '' }}>pa</option>
               </select>
            </div>
            <!-- Row 2: Local File -->
            <div class="flex items-center space-x-2">
               <!-- Refresh token button -->
               <button
                  type="button"
                  onclick="window.location.href='{{ url_for('refreshtoken') }}'"
                  class="btn btn-ghost btn-icon"
                  title="Refresh AWS SSO">🔄</button>
               <!-- Local browse button -->
               <button
                  type="button"
                  id="browseBtn"
                  class="btn btn-ghost btn-icon"
                  title="Select local file"
                  >📁</button>
               <!-- Hidden file input -->
               <input
                  type="file"
                  id="upload_file"
                  name="upload_file"
                  accept="*"
                  class="hidden"
                  />
               <!-- Edit local button - moved right before local input -->
               <button
                  type="submit"
                  id="editLocalBtn"
                  name="action"
                  value="edit"
                  class="btn btn-ghost btn-icon"
                  title="Edit local file"
                  disabled
                  >✏️</button>
               <!-- Local file display -->
               <input
                  type="text"
                  id="local_path"
                  class="flex-grow border px-4 py-2 text-base theme-transition"
                  placeholder="No file selected"
                  readonly
                  style="height: 46px;"
                  />
            </div>
            <!-- Hidden mirror for Download -->
            <input type="hidden" name="path" id="path_input" value="" />
            <input type="hidden" name="download_count" id="limit_input" value="All" />
            <input type="hidden" name="delim" id="delim_input" value="" />
            <input type="hidden" name="records_per_page" id="records_per_page_input" value="40" />
            <!-- Hidden field to ensure S3 path is always submitted even when editing local files -->
            <input type="hidden" name="orig_s3_path" id="orig_s3_path" value="" />
            <!-- Hidden field for raw edit preference -->
            <input type="hidden" name="raw_edit" id="raw_edit_input" value="" />
            <!-- Row 3: Action buttons -->
            <div class="flex items-center justify-between">
               <!-- Left side: Download, All records, Upload -->
               <div class="flex items-center space-x-2">
                  <button id="downloadBtn"
                     type="button"
                     class="btn btn-success"
                     disabled>
                  Download
                  </button>
                  <div class="flex items-center space-x-2">
                     <span id="downloadLabel"
                        contenteditable="true"
                        class="px-3 py-2 border border-gray-300 focus:outline-none focus:border-blue-500 inline-block min-w-[60px] text-center theme-transition"
                        title="Enter a number to download specific records, or keep 'All' to download everything">All</span>
                     <label class="text-sm font-medium text-gray-700">records</label>
                  </div>
                  <button id="plainUploadBtn"
                     type="button"
                     class="btn btn-secondary"
                     disabled>
                  Upload
                  </button>
                  <button id="encryptUploadBtn"
                     type="button"
                     class="btn btn-primary"
                     disabled>
                  Upload - Encrypt
                  </button>
                  <!-- Spacing -->
                  <div class="w-4"></div>
                  <button id="toolsToggleBtn"
                     type="button"
                     class="btn btn-ghost"
                     title="Open Tools"
                     onclick="createAndShowTools(); return false;">
                  🔧 Tools
                  </button>
                  <button id="terminalToggleBtn"
                     type="button"
                     class="btn btn-ghost"
                     title="Open Terminal"
                     onclick="createAndShowTerminal(); return false;">
                  🖥️ Terminal
                  </button>
                  <button id="textEncryptionToggleBtn"
                     type="button"
                     class="btn btn-ghost"
                     title="Open Text Encryption/Decryption"
                     onclick="createAndShowTextEncryption(); return false;">
                  🔐 Text
                  </button>
                  <button id="chatbotToggleBtn"
                     type="button"
                     class="btn btn-ghost"
                     title="Open AI Chat"
                     onclick="createAndShowChatbot(); return false;">
                  💬 Chat
                  </button>
               </div>
               <!-- Right side: Raw edit checkbox, Records per page and Clear button -->
               <div class="flex items-center space-x-2">
                  <!-- Text Edit toggle button -->
                  <button id="textEditToggleBtn"
                     type="button"
                     class="btn btn-ghost"
                     title="Use raw text editor for JSON files instead of structured editor"
                     onclick="toggleTextEdit(); return false;">
                     <span class="vs-icon" aria-hidden="true" style="display:inline-flex;align-items:center;justify-content:center;width:22px;height:22px;min-width:22px;min-height:22px;">
                       <img src="https://upload.wikimedia.org/wikipedia/commons/thumb/9/9a/Visual_Studio_Code_1.35_icon.svg/2048px-Visual_Studio_Code_1.35_icon.svg.png" alt="VS" style="display:block;width:22px;height:22px;object-fit:contain;"/>
                     </span>
                     <span class="vs-emoji" style="display:none;margin-left:6px;">📝</span>
                  </button>
                  <label class="text-sm font-medium text-gray-700">Pagination</label>
                  <span id="recordsPerPage"
                     contenteditable="true"
                     class="px-1 py-2 border border-gray-300 focus:outline-none focus:border-blue-500 inline-block min-w-[60px] text-center theme-transition"
                     title="Number of records to show per page when editing CSV files">20</span>
                  <button id="clearBtn"
                     type="button"
                     class="btn btn-danger">
                  Clear
                  </button>
               </div>
           </div>
        </form>
        <!-- Terminal Section -->
        <div id="terminal-section" class="mt-8 section-card" style="display: none;">
            <div class="flex items-center justify-between mb-4">
               <h2 class="text-xl font-semibold">Terminal 🖥️</h2>
               <button onclick="closeTerminal(); return false;" class="btn btn-ghost" title="Close Terminal">
                 ⛌
               </button>
            </div>
            <div class="terminal-container" style="border: 1px solid #30363d; height: 400px; display: flex; flex-direction: column; overflow: hidden; margin-bottom: 10px;">
               <div id="home-terminal-output" style="flex: 1; color: #ffffff; font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; padding: 15px; overflow-y: auto; white-space: pre-wrap; font-size: 14px; line-height: 1.5; margin-bottom: 0; border-radius: 0;"></div>
               <div style="padding: 0; margin: 0; display: flex; align-items: stretch; border-top: 1px solid #30363d; flex-shrink: 0;">
                  <span style="color: #ffffff; font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 14px; padding-left: 15px; user-select: none; pointer-events: none;">$</span>
                  <input type="text" id="home-terminal-input" style="flex: 1; border: none; color: #ffffff; font-weight: normal; font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; font-size: 14px; outline: none; padding: 15px; padding-left: 5px; caret-color: #ffffff; box-shadow: none; border-radius: 0; text-align: left; -webkit-tap-highlight-color: transparent; -webkit-appearance: none; -moz-appearance: none; appearance: none; resize: none; overflow-y: auto; min-height: 44px;"></input>
               </div>
            </div>
         </div>
         <!-- Tools Section -->
         <div id="tools-section" class="mt-8 section-card" style="display: none;">
            <div class="flex items-center justify-between mb-4">
               <h2 class="text-xl font-semibold">Tools 🔧</h2>
               <button onclick="closeTools(); return false;" class="btn btn-ghost" title="Close Tools">
                 ⛌
               </button>
            </div>
            <div class="flex flex-wrap gap-2">
               <button id="airflowBtn"
                  type="button"
                  class="btn btn-ghost"
                  title="Open Airflow (based on selected environment)">
               🌀 Airflow
               </button>
               <button id="cloudwatchBtn"
                  type="button"
                  class="btn btn-ghost"
                  title="Open CloudWatch (based on selected environment)">
               📈 CloudWatch
               </button>
               <button id="s3Btn"
                  type="button"
                  class="btn btn-ghost"
                  title="Open S3 Console (based on selected environment)">
               🪣 S3
               </button>
               <button id="updateAppBtn"
                  type="button"
                  class="btn btn-ghost"
                  title="Update app from git and restart"
                  onclick="updateApp(); return false;">
               🛋️ Update
               </button>
            </div>
         </div>
         <!-- Notes Section (Default) -->
         <div id="notes-section" class="mt-8 section-card">
            <div class="flex items-center justify-between mb-4">
               <h2 class="text-xl font-semibold">Notes 📝</h2>
               <button onclick="saveNotesToFile(); return false;" class="btn btn-ghost" title="Save notes to file">
               💾 Save
               </button>
            </div>
            <div class="terminal-container" style="border: 1px solid #30363d; height: 400px; display: flex; flex-direction: column; overflow: hidden; margin-bottom: 10px;">
               <textarea 
                  id="notesTextarea" 
                  style="flex: 1; width: 100%; height: 100%; font-family: 'Monaco', 'Menlo', 'Ubuntu Mono', 'Consolas', 'Liberation Mono', 'Courier New', monospace !important; padding: 20px; overflow-y: auto; white-space: pre-wrap; font-size: 15px; line-height: 1.6; margin: 0; border-radius: 0; border: none; outline: none; resize: none; background: transparent; color: #ffffff;"
                  onload="if(typeof initializeNotes === 'function') initializeNotes();"
                  ></textarea>
            </div>
         </div>
         <!-- Immediate Notes Initialization -->
         <script>
            // Immediate notes initialization
            (function() {
              function initNotes() {
                const notesTextarea = document.getElementById('notesTextarea');
                if (notesTextarea) {
                  console.log('Initializing notes...');
                  // Load saved notes
                  const savedNotes = localStorage.getItem('sequoia-notes');
                  if (savedNotes) {
                    console.log('Loading saved notes:', savedNotes.substring(0, 50) + '...');
                    notesTextarea.value = savedNotes;
                  } else {
                    console.log('No saved notes found');
                  }
                  // Set up auto-save
                  notesTextarea.addEventListener('input', function() {
                    localStorage.setItem('sequoia-notes', this.value);
                    console.log('Notes auto-saved:', this.value.length, 'characters');
                  });
                  console.log('Initializing notes completed');
                } else {
                  console.log('Notes textarea not found, will retry...');
                  // Retry after a short delay
                  setTimeout(initNotes, 100);
                }
              }
              // Start immediately
              initNotes();
            })();
         </script>
         <!-- Text Encryption/Decryption Section -->
         <div id="text-encryption-section" class="mt-8 section-card" style="display: none;">
               <div class="flex items-center justify-between mb-4">
                  <h3 class="text-lg font-semibold">Text 🔐</h3>
                  <button onclick="closeTextEncryption(); return false;" class="btn btn-ghost" title="Close Text Encryption">
                    ⛌
                  </button>
               </div>
               <div class="space-y-3">
                  <div class="flex flex-col space-y-3">
                     <div>
                        <div class="flex items-center justify-between mb-2">
                           <label class="block text-sm font-semibold text-gray-900 theme-text modern-label">INPUT</label>
                           <button id="pasteInputBtn" class="copy-icon-btn" title="Paste from clipboard">
                              <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                                 <rect x="8" y="2" width="8" height="4" rx="1" ry="1"></rect>
                                 <path d="M16 4h2a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V6a2 2 0 0 1 2-2h2"></path>
                              </svg>
                           </button>
                        </div>
                        <textarea id="cryptText" class="w-full border-2 px-3 py-2 h-24 modern-textarea"></textarea>
                     </div>
                     <div>
                        <div class="flex items-center justify-between mb-2">
                           <label class="block text-sm font-semibold text-gray-900 theme-text modern-label">RESULT</label>
                           <button id="copyResultBtn" class="copy-icon-btn" title="Copy to clipboard">
                              <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                                 <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
                                 <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path>
                              </svg>
                           </button>
                        </div>
                        <textarea id="cryptResult" class="w-full border-2 px-3 py-2 h-24 modern-textarea" readonly></textarea>
                     </div>
                  </div>
                  <div class="flex space-x-2">
                     <button id="encryptBtn" class="btn btn-primary">
                     Encrypt
                     </button>
                     <button id="decryptBtn" class="btn btn-secondary">
                     Decrypt
                     </button>
                     <select name="crypt_module" class="border px-4 py-2 text-base theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;">
                     <option value="dxp" {{ 'selected' if module == 'dxp' else '' }}>dxp</option>
                     <option value="dap" {{ 'selected' if module == 'dap' else '' }}>dap</option>
                     <option value="pa" {{ 'selected' if module == 'pa' else '' }}>pa</option>
                     </select>
                  </div>
               </div>
         </div>
         <!-- Chatbot Section -->
         <div id="chatbot-section" class="mt-8 section-card" style="display: none;">
            <div class="flex items-center justify-between mb-4">
              <h2 class="text-xl font-semibold">Chat 💬</h2>
              <div class="flex items-center gap-2">
                <select id="chatbot-model" class="btn btn-ghost" title="Model">
                  <option value="llama3.2:1b" selected>LLaMA 3.1 (1B)</option>
                  <option value="qwen2.5:1.5b">Qwen Code 2.5 (0.5B)</option>
                  <option value="llama3.1:8b">LLaMA 3.1 (8B)</option>
                  <option value="qwen2.5:7b">Qwen Code 2.5 (7B)</option>   
                  <option value="qwen2.5-coder:14b">Qwen Code 2.5 (14B)</option>   
                </select>
                <button onclick="toggleChatFullscreen(); return false;" class="btn btn-ghost" title="Fullscreen">⛶</button>
                <button onclick="closeChatbot(); return false;" class="btn btn-ghost" title="Close Chat">⛌</button>
              </div>
            </div>
            <div class="terminal-container" style="border: 1px solid #30363d; height: 400px; display: flex; flex-direction: column; overflow: hidden; margin-bottom: 10px;">
              <div id="chatbot-output" class="chat-output"></div>
              <div style="padding: 0; margin: 0; display: flex; align-items: stretch; border-top: 1px solid #30363d; flex-shrink: 0;">
                <textarea id="chatbot-input" rows="1" placeholder="" style="flex: 1; border: none; font-weight: normal; font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif !important; font-size: 14px; outline: none; padding: 14px 16px; caret-color: currentColor; box-shadow: none; border-radius: 0; text-align: left; -webkit-tap-highlight-color: transparent; -webkit-appearance: none; -moz-appearance: none; appearance: none; resize: none; overflow-y: auto; min-height: 44px;"></textarea>
              </div>
            </div>
         </div>
         <!-- Separate form for downloads -->
         <form id="download-form" action="{{ url_for('download') }}" method="post" style="display: none;">
            <input type="hidden" name="path" id="download_path" />
            <input type="hidden" name="module" id="download_module" />
            <input type="hidden" name="download_count" id="download_limit" />
            <input type="hidden" name="action" value="download" />
         </form>
         <!-- Separate form for encrypt and upload -->
         <form id="encrypt-form" action="{{ url_for('encrypt_upload') }}" method="post" style="display: none;" enctype="multipart/form-data">
            <input type="hidden" name="s3_path" id="encrypt_s3_path" />
            <input type="hidden" name="module" id="encrypt_module" />
            <input type="file" name="upload_file" id="encrypt_upload_file" style="display: none;" />
         </form>
         <!-- Separate form for plain upload -->
         <form id="plain-upload-form" action="{{ url_for('plain_upload') }}" method="post" style="display: none;" enctype="multipart/form-data">
            <input type="hidden" name="s3_path" id="plain_s3_path" />
            <input type="hidden" name="module" id="plain_module" />
            <input type="file" name="upload_file" id="plain_upload_file" style="display: none;" />
         </form>
      </div>
      <!-- S3 Browser Modal -->
      <div id="s3Modal" class="modal">
         <div class="modal-content">
            <div class="modal-header">
               <strong>
                  <h2 style="margin: 0;">Amazon S3</h2>
               </strong>
               <span class="close">&times;</span>
            </div>
            <div style="margin-bottom: 20px; display: flex; align-items: center; gap: 10px;">
               <select id="bucketSelect" class="border px-4 py-2 theme-transition" style="flex: 1; height: 46px;">
                  <option value="">Select a bucket...</option>
                  {% if env == 'dev' %}
                  <!-- DEV BUCKETS - Add your dev bucket list here -->
                  <option value="pp-sequoiacloud-ods-us-west-2-dev">pp-sequoiacloud-ods-us-west-2-dev</option>
                  <option value="pp-sequoiacloud-ads-us-west-2-dev">pp-sequoiacloud-ads-us-west-2-dev</option>
                  <option value="pp-sequoiacloud-dwd-us-west-2-dev">pp-sequoiacloud-dwd-us-west-2-dev</option>
                  <option value="pp-data-us-west-2-dev">pp-data-us-west-2-dev</option>
                  <option value="aws-glue-scripts-512094374371-us-west-2">aws-glue-scripts-512094374371-us-west-2</option>
                  <!-- Add more dev buckets here -->
                  {% elif env == 'stage' %}
                  <!-- STAGE BUCKETS - Add your stage bucket list here -->
                  <option value="pp-sequoiacloud-ods-us-west-2-stage">pp-sequoiacloud-ods-us-west-2-stage</option>
                  <option value="pp-sequoiacloud-ads-us-west-2-stage">pp-sequoiacloud-ads-us-west-2-stage</option>
                  <option value="pp-sequoiacloud-dwd-us-west-2-stage">pp-sequoiacloud-dwd-us-west-2-stage</option>
                  <option value="pp-sequoiacloud-public-us-west-2-stage">pp-sequoiacloud-public-us-west-2-stage</option>
                  <option value="pp-data-us-west-2-stage">pp-data-us-west-2-stage</option>
                  <option value="aws-glue-scripts-749518382711-us-west-2">aws-glue-scripts-749518382711-us-west-2</option>
                  <!-- Add more stage buckets here -->
                  {% elif env == 'production' %}
                  <!-- PRODUCTION BUCKETS - Add your production bucket list here -->
                  <option value="pp-sequoiacloud-ods-us-west-2-production">pp-sequoiacloud-ods-us-west-2-production</option>
                  <option value="pp-sequoiacloud-ads-us-west-2-production">pp-sequoiacloud-ads-us-west-2-production</option>
                  <option value="pp-sequoiacloud-dwd-us-west-2-production">pp-sequoiacloud-dwd-us-west-2-production</option>
                  <option value="pp-data-us-west-2-production">pp-data-us-west-2-production</option>
                  <!-- Add more production buckets here -->
                  {% endif %}
               </select>
               <button id="refreshBucketBtn" class="btn btn-ghost" title="Refresh current folder" style="height: 46px;">
               Refresh
               </button>
            </div>
            <div class="breadcrumb" id="breadcrumb"></div>
            <input type="text" class="browser-search" id="browserSearch" placeholder="Search files and folders..." style="height: 46px;">
            <div class="browser-content" id="browserContent">
               <div class="loading-spinner">Select a bucket to start browsing...</div>
            </div>
            <div style="margin-top: 15px; display: flex; justify-content: space-between; align-items: center;">
               <div style="font-size: 0.85em; color: #666;">
                  <span>💡 Tip: Press Refresh to get latest file</span>
               </div>
               <div>
                  <button id="selectFileBtn" class="btn btn-primary ml-2" disabled>
                  Select File
                  </button>
                  <button id="useFolderBtn" class="btn btn-secondary ml-2" disabled>
                  Select Folder
                  </button>
                  <button id="cancelBrowseBtn" class="btn btn-secondary ml-2">
                  Cancel
                  </button>
               </div>
            </div>
         </div>
      </div>
      <script>
         // Initialize notes auto-save
         window.initializeNotes = function() {
           console.log('Initializing notes...');
           const notesTextarea = document.getElementById('notesTextarea');

           if (!notesTextarea) {
             console.error('Notes textarea not found! Will retry...');
             // Retry after a short delay
             setTimeout(() => {
               console.log('Retrying notes initialization...');
               initializeNotes();
             }, 500);
             return;
           }

           console.log('Notes textarea found, setting up auto-save...');

           // Load saved notes from localStorage
           const savedNotes = localStorage.getItem('sequoia-notes');
           if (savedNotes) {
             console.log('Loading saved notes:', savedNotes.substring(0, 50) + '...');
             notesTextarea.value = savedNotes;
           } else {
             console.log('No saved notes found');
           }

           // Auto-save on input
           notesTextarea.addEventListener('input', function() {
             console.log('Saving notes to localStorage...');
             localStorage.setItem('sequoia-notes', this.value);
             console.log('Notes saved successfully, length:', this.value.length);
           });

           console.log('Notes auto-save initialized successfully');
         };

         // Manual save function for notes
         window.saveNotes = function() {
           const notesTextarea = document.getElementById('notesTextarea');
           if (notesTextarea) {
             localStorage.setItem('sequoia-notes', notesTextarea.value);
             console.log('Notes manually saved, length:', notesTextarea.value.length);
           }
         };

         // Check notes status
         window.checkNotesStatus = function() {
           const savedNotes = localStorage.getItem('sequoia-notes');
           const notesTextarea = document.getElementById('notesTextarea');
           console.log('Notes status check:');
           console.log('- localStorage has notes:', !!savedNotes);
           console.log('- Notes length in localStorage:', savedNotes ? savedNotes.length : 0);
           console.log('- Textarea has content:', notesTextarea ? !!notesTextarea.value : 'textarea not found');
           console.log('- Textarea content length:', notesTextarea ? notesTextarea.value.length : 0);
         };

         // Force restore all content from localStorage
         window.forceRestoreContent = function() {
           console.log('Force restoring content from localStorage...');

           // Restore notes
           const savedNotes = localStorage.getItem('sequoia-notes');
           const notesTextarea = document.getElementById('notesTextarea');
           if (savedNotes && notesTextarea) {
             notesTextarea.value = savedNotes;
             console.log('Notes restored:', savedNotes.length, 'characters');
           }

           // Restore text encryption input
           const savedText = localStorage.getItem('secure-crypt-text');
           const cryptTextarea = document.getElementById('cryptText');
           if (savedText && cryptTextarea) {
             cryptTextarea.value = savedText;
             console.log('Text encryption input restored:', savedText.length, 'characters');
           }

           // Note: Text encryption result is not restored from localStorage for security reasons
           console.log('Text encryption result not restored (security)');

           console.log('Force restore completed');
         };

         // Initialize text encryption auto-save
         window.initializeTextEncryption = function() {
           console.log('Initializing text encryption...');
           const cryptTextarea = document.getElementById('cryptText');
           const cryptResultTextarea = document.getElementById('cryptResult');

           if (!cryptTextarea) {
             console.error('Text encryption textarea not found! Will retry...');
             // Retry after a short delay
             setTimeout(() => {
               console.log('Retrying text encryption initialization...');
               initializeTextEncryption();
             }, 500);
             return;
           }

           if (!cryptResultTextarea) {
             console.error('Text encryption result textarea not found! Will retry...');
             // Retry after a short delay
             setTimeout(() => {
               console.log('Retrying text encryption initialization...');
               initializeTextEncryption();
             }, 500);
             return;
           }

           console.log('Text encryption textareas found, setting up auto-save...');

           // Load saved input text from localStorage
           const savedText = localStorage.getItem('secure-crypt-text');
           if (savedText) {
             console.log('Loading saved input text:', savedText.substring(0, 50) + '...');
             cryptTextarea.value = savedText;
           } else {
             console.log('No saved input text found');
           }

           // Note: Result text is not saved to localStorage for security reasons
           console.log('Text encryption result not loaded from localStorage (security)');

           // Auto-save input on input
           cryptTextarea.addEventListener('input', function() {
             console.log('Saving input text to localStorage...');
             localStorage.setItem('secure-crypt-text', this.value);
           });

           // Note: Result text is not auto-saved to localStorage for security reasons
           console.log('Text encryption result auto-save disabled (security)');

           console.log('Text encryption auto-save initialized successfully');
         };

         // Manual save function for text encryption
         window.saveTextEncryption = function() {
           const cryptTextarea = document.getElementById('cryptText');
           const cryptResultTextarea = document.getElementById('cryptResult');

           if (cryptTextarea) {
             localStorage.setItem('secure-crypt-text', cryptTextarea.value);
             console.log('Text encryption input manually saved');
           }

           // Note: Result text is not manually saved to localStorage for security reasons
           console.log('Text encryption result manual save disabled (security)');
         };

         // Function to manage notes visibility
         window.updateNotesVisibility = function() {
           var terminalSection = document.getElementById('terminal-section');
           var textSection = document.getElementById('text-encryption-section');
           var toolsSection = document.getElementById('tools-section');
           var chatbotSection = document.getElementById('chatbot-section');
           var notesSection = document.getElementById('notes-section');

           var terminalOpen = terminalSection && terminalSection.style.display !== 'none';
           var textOpen = textSection && textSection.style.display !== 'none';
           var toolsOpen = toolsSection && toolsSection.style.display !== 'none';
           var chatbotOpen = chatbotSection && chatbotSection.style.display !== 'none';

           // Show notes only if NO other sections are open
           if (notesSection) {
             if (terminalOpen || textOpen || toolsOpen || chatbotOpen) {
               notesSection.style.display = 'none';
             } else {
               notesSection.style.display = 'block';
             }
           }
         };

         // Terminal functions - defined early to ensure availability
         window.createAndShowTerminal = function(showImmediately = true) {
           console.log('createAndShowTerminal called');

           var terminalSection = document.getElementById('terminal-section');
           var terminalBtn = document.getElementById('terminalToggleBtn');
           var textSection = document.getElementById('text-encryption-section');
           var textBtn = document.getElementById('textEncryptionToggleBtn');

           // Toggle terminal visibility
           if (terminalSection.style.display === 'none' || !terminalSection.style.display) {
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

             // Save state - allow multiple sections
             var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
             console.log('Current openSections before saving terminal:', openSections);
             if (!openSections.includes('terminal')) {
               openSections.push('terminal');
               localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
               console.log('Saved terminal state:', openSections);
               console.log('localStorage after saving:', localStorage.getItem('workbench-open-sections'));

               // Update notes visibility
               updateNotesVisibility();
             } else {
               console.log('Terminal already in openSections');
             }
           } else {
             // Close terminal
             window.closeTerminal();
           }

           return false;
         };

         window.executeTerminalCommand = function(command) {
           var output = document.getElementById('home-terminal-output');
           if (!output) return;

           // Handle built-in commands
           if (command.toLowerCase() === 'clear' || command.toLowerCase() === 'cls') {
             output.innerHTML = '';

             // Restore welcome message after clearing (same as clear button)
             const theme = document.body.className.includes('white-theme') ? 'white' : 
                          document.body.className.includes('pink-theme') ? 'pink' : 'dark';

             const welcomeColor = theme === 'dark' ? '#00ff00' : 
                                 theme === 'white' ? '#4b5563' : '#831843';
             const helpColor = theme === 'dark' ? '#00ff00' : 
                              theme === 'white' ? '#6b7280' : '#be185d';

             output.innerHTML = '<span style="color: ' + welcomeColor + ';">Welcome to Sequoia WorkBench Terminal</span><br><span style="color: ' + helpColor + ';">Type some command e.g. pip install pandas</span><br><br>';
             return;
           }

           // Show command being executed with theme-aware colors
           var theme = document.body.className.includes('white-theme') ? 'white' : 
                      document.body.className.includes('pink-theme') ? 'pink' : 'dark';

           var promptColor = theme === 'dark' ? '#74c0fc' : 
                            theme === 'white' ? '#059669' : '#be185d';
           var commandColor = theme === 'dark' ? '#ffffff' : 
                             theme === 'white' ? '#4b5563' : '#831843';

           output.innerHTML += `<br><span style="color: ${promptColor};">$</span> <span style="color: ${commandColor};">${command}</span><br>`;

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

             var outputColor = theme === 'dark' ? '#00ff00' : 
                              theme === 'white' ? '#4b5563' : '#831843';
             var errorColor = theme === 'dark' ? '#ffffff' : 
                             theme === 'white' ? '#dc2626' : '#be185d';

             if (data.error) {
               output.innerHTML += `<span style="color: ${errorColor};">Error: ${data.error}</span><br>`;
             } else {
               // Show output
               if (data.output) {
                 output.innerHTML += `<span style="color: ${outputColor};">${data.output}</span>`;
               }
               // Show error output
               if (data.stderr) {
                 output.innerHTML += `<span style="color: ${errorColor};">${data.stderr}</span>`;
               }
             }
             output.scrollTop = output.scrollHeight;
           })
           .catch(error => {
             // Theme-aware error color
             var theme = document.body.className.includes('white-theme') ? 'white' : 
                        document.body.className.includes('pink-theme') ? 'pink' : 'dark';

             var errorColor = theme === 'dark' ? '#ffffff' : 
                             theme === 'white' ? '#dc2626' : '#be185d';

             output.innerHTML += `<span style="color: ${errorColor};">Error: ${error.message}</span><br>`;
             output.scrollTop = output.scrollHeight;
           });
         };

         // Text Encryption/Decryption toggle function
         window.createAndShowTextEncryption = function(showImmediately = true) {
           console.log('createAndShowTextEncryption called');

           var textSection = document.getElementById('text-encryption-section');
           var textBtn = document.getElementById('textEncryptionToggleBtn');

           if (textSection) {
             // Toggle visibility
             if (textSection.style.display === 'none') {
               // Open text section
               textSection.style.display = 'block';
               if (textBtn) {
                 textBtn.classList.add('selected');
               }

               // Scroll into view only if showImmediately is true
               if (showImmediately) {
                 setTimeout(function() {
                   textSection.scrollIntoView({behavior: 'smooth'});
                 }, 100);
               }

               // Save state - allow multiple sections
               var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
               console.log('Current openSections before saving text:', openSections);
               if (!openSections.includes('text')) {
                 openSections.push('text');
                 localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
                 console.log('Saved text state:', openSections);
                 console.log('localStorage after saving text:', localStorage.getItem('workbench-open-sections'));

                 // Update notes visibility
                 updateNotesVisibility();
               } else {
                 console.log('Text already in openSections');
               }
             } else {
               // Close text section
               textSection.style.display = 'none';
               if (textBtn) {
                 textBtn.classList.remove('selected');
               }

               // Remove from state
               var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
               openSections = openSections.filter(section => section !== 'text');
               localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
               console.log('Removed text from state:', openSections);

               // Update notes visibility
               updateNotesVisibility();
             }
           }

           return false;
         };

         // Close functions
         window.closeTerminal = function() {
           var terminalSection = document.getElementById('terminal-section');
           var terminalBtn = document.getElementById('terminalToggleBtn');
           if (terminalSection) {
             terminalSection.style.display = 'none';
             if (terminalBtn) {
               terminalBtn.classList.remove('selected');
             }

             // Remove from state
             var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
             openSections = openSections.filter(section => section !== 'terminal');
             localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
             console.log('Removed terminal from state:', openSections);

             // Update notes visibility
             updateNotesVisibility();
           }
           return false;
         };

         window.createAndShowTools = function(showImmediately = true) {
           console.log('createAndShowTools called');

           var toolsSection = document.getElementById('tools-section');
           var toolsBtn = document.getElementById('toolsToggleBtn');

           // Toggle tools visibility
           if (toolsSection.style.display === 'none' || !toolsSection.style.display) {
             // Show the tools and update button state
             toolsSection.style.display = 'block';
             if (toolsBtn) {
               toolsBtn.classList.add('selected');
             }

             // Scroll to view if showImmediately is true
             if (showImmediately) {
               setTimeout(function() {
                 toolsSection.scrollIntoView({behavior: 'smooth'});
               }, 100);
             }

             // Save state - allow multiple sections
             var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
             console.log('Current openSections before saving tools:', openSections);
             if (!openSections.includes('tools')) {
               openSections.push('tools');
               localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
               console.log('Saved tools state:', openSections);

               // Update notes visibility
               updateNotesVisibility();
             } else {
               console.log('Tools already in openSections');
             }
           } else {
             window.closeTools();
           }
         };

         window.closeTools = function() {
           var toolsSection = document.getElementById('tools-section');
           var toolsBtn = document.getElementById('toolsToggleBtn');
           if (toolsSection) {
             toolsSection.style.display = 'none';
             if (toolsBtn) {
               toolsBtn.classList.remove('selected');
             }

             // Remove from state
             var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
             openSections = openSections.filter(section => section !== 'tools');
             localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
             console.log('Removed tools from state:', openSections);

             // Update notes visibility
             updateNotesVisibility();
           }
           return false;
         };

         window.closeTextEncryption = function() {
           var textSection = document.getElementById('text-encryption-section');
           var textBtn = document.getElementById('textEncryptionToggleBtn');
           if (textSection) {
             textSection.style.display = 'none';
             if (textBtn) {
               textBtn.classList.remove('selected');
             }

             // Remove from state
             var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
             openSections = openSections.filter(section => section !== 'text');
             localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
             console.log('Removed text from state:', openSections);

             // Update notes visibility
             updateNotesVisibility();
           }
           return false;
         };

         // Chatbot functions
         window.createAndShowChatbot = function(showImmediately = true) {
           console.log('createAndShowChatbot called');

           var chatbotSection = document.getElementById('chatbot-section');
           var chatbotBtn = document.getElementById('chatbotToggleBtn');
           var terminalSection = document.getElementById('terminal-section');
           var terminalBtn = document.getElementById('terminalToggleBtn');
           var textSection = document.getElementById('text-encryption-section');
           var textBtn = document.getElementById('textEncryptionToggleBtn');

           // Toggle chatbot visibility
           if (chatbotSection.style.display === 'none' || !chatbotSection.style.display) {
             // Close other sections first
             if (terminalSection) {
               terminalSection.style.display = 'none';
               if (terminalBtn) terminalBtn.classList.remove('selected');
             }
             if (textSection) {
               textSection.style.display = 'none';
               if (textBtn) textBtn.classList.remove('selected');
             }

             // Show the chatbot and update button state
             chatbotSection.style.display = 'block';
             if (chatbotBtn) {
               chatbotBtn.classList.add('selected');
             }

             // Focus and scroll only if showImmediately is true
             if (showImmediately) {
               setTimeout(function() {
                 var input = document.getElementById('chatbot-input');
                 if (input) input.focus();
                 chatbotSection.scrollIntoView({behavior: 'smooth'});
               }, 100);
             }

             // Save state
             var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
             if (!openSections.includes('chatbot')) {
               openSections.push('chatbot');
               localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
               updateNotesVisibility();
             }
           } else {
             window.closeChatbot();
           }

           return false;
         };

window.executeChatbotQuery = function(query) {
 const output = document.getElementById('chatbot-output');
 if (!output) return false;

 // Append user text as a normal right-aligned line (no bubble);
 // preserve code formatting if multiline or fenced
 const userLine = document.createElement('div');
 userLine.className = 'chat-user-line';
 const isCodeLike = query.includes('\n') || /```/.test(query);
 if (isCodeLike) {
   // strip outer code fences if present
   let raw = query.replace(/^```[a-zA-Z0-9]*\n?/, '').replace(/\n```\s*$/, '');
   const pre = document.createElement('pre');
   pre.textContent = raw;
   userLine.appendChild(pre);
 } else {
   userLine.textContent = query;
 }
  output.appendChild(userLine);
  output.scrollTop = output.scrollHeight;
  requestAnimationFrame(() => { try { output.scrollTop = output.scrollHeight; } catch(e) {} });

 // Show typing indicator (no bubble) until stream starts
 let typingRow = document.createElement('div');
 typingRow.className = 'typing-row';
 const typing = document.createElement('div');
 typing.className = 'typing-indicator';
 typing.innerHTML = '<span class="dot"></span><span class="dot"></span><span class="dot"></span>';
 typingRow.appendChild(typing);
 output.appendChild(typingRow);
 output.scrollTop = output.scrollHeight;
 requestAnimationFrame(() => { try { output.scrollTop = output.scrollHeight; } catch(e) {} });

 // Lazy-create assistant bubble only when stream produces content
 let asstMsg = null;
  const ensureAssistant = () => {
    if (asstMsg) return;
    const row = document.createElement('div');
    row.className = 'chat-row';
    asstMsg = document.createElement('div');
    asstMsg.className = 'chat-msg assistant';
    asstMsg.innerHTML = '';
    row.appendChild(asstMsg);
    output.appendChild(row);
    output.scrollTop = output.scrollHeight;
  };

  // Remove typing indicator once tokens start
  const removeTypingIfAny = () => { if (typingRow && typingRow.parentNode) { typingRow.remove(); typingRow = null; } };
  let hasFirstToken = false;

  const isNearBottom = () => (output.scrollHeight - output.scrollTop - output.clientHeight) < 80;
  const scrollToBottomIfNeeded = (stick) => { if (stick) output.scrollTop = output.scrollHeight; };

let mdBuffer = '';
const compactMarkdown = (md) => {
  const lines = md.split('\n');
  let out = [];
  let inFence = false;
  let emptyCount = 0;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trim();
    if (trimmed.startsWith('```')) { inFence = !inFence; emptyCount = 0; out.push(line); continue; }
    if (!inFence) {
      if (trimmed === '') {
        emptyCount++;
        if (emptyCount <= 1) out.push('');
      } else {
        emptyCount = 0;
        out.push(line);
      }
    } else {
      out.push(line);
    }
  }
  return out.join('\n');
};
let renderScheduled = false;
const render = () => {
  renderScheduled = false;
  try {
    ensureAssistant();
    const mdForRender = compactMarkdown(mdBuffer);
    const html = DOMPurify.sanitize(marked.parse(mdForRender));
    asstMsg.innerHTML = html;
    asstMsg.querySelectorAll('pre code').forEach((block) => { try { hljs.highlightElement(block); } catch (e) {} });
  } catch (e) { /* no-op */ }
};
const scheduleRender = () => { if (!renderScheduled) { renderScheduled = true; requestAnimationFrame(render); } };

// Pick model based on dropdown (use model id directly from value)
const modelSelect = document.getElementById('chatbot-model');
const selectedModel = (modelSelect && modelSelect.value) ? modelSelect.value : 'llama3.2:1b';

fetch('/chatbot-query', {
  method: 'POST',
  headers: { 'Content-Type': 'application/json' },
  body: JSON.stringify({ question: query, model: selectedModel })
}).then((response) => {
  if (!response.ok) throw new Error('HTTP ' + response.status + ': ' + response.statusText);
  const reader = response.body.getReader();
  const decoder = new TextDecoder('utf-8');
  let sseBuffer = '';

  const processBuffer = () => {
    sseBuffer = sseBuffer.replace(/\r/g, '');
    let idx;
    while ((idx = sseBuffer.indexOf('\n\n')) !== -1) {
      const eventStr = sseBuffer.slice(0, idx);
      sseBuffer = sseBuffer.slice(idx + 2);
      const lines = eventStr.split('\n');
      for (const line of lines) {
        if (!line || line.startsWith(':')) continue;
        if (line.startsWith('data: ')) {
          try {
            const data = JSON.parse(line.slice(6));
            if (data.error) throw new Error(data.error);
            // Model download progress from backend
            if (typeof data.download_progress === 'number') {
              let termOut = document.getElementById('home-terminal-output');
              if (!termOut && typeof window.createAndShowTerminal === 'function') {
                try { window.createAndShowTerminal(false); } catch (e) {}
                termOut = document.getElementById('home-terminal-output');
              }
              if (termOut) {
                const barId = 'ollama-model-pull';
                let lineEl = termOut.querySelector(`#${barId}`);
                const pct = Math.max(0, Math.min(100, Math.floor(data.download_progress)));
                const bar = '[' + '#'.repeat(Math.floor(pct/5)) + '-'.repeat(20 - Math.floor(pct/5)) + ']';
                if (!lineEl) {
                  lineEl = document.createElement('div');
                  lineEl.id = barId;
                  termOut.appendChild(lineEl);
                }
                lineEl.textContent = `Downloading model ${selectedModel}: ${bar} ${pct}%`;
                termOut.scrollTop = termOut.scrollHeight;
              }
            }
            // Support multiple provider shapes
            if (typeof data.token === 'string') { if (!hasFirstToken) { hasFirstToken = true; removeTypingIfAny(); } mdBuffer += data.token; scheduleRender(); }
            else if (typeof data.delta === 'string') { if (!hasFirstToken) { hasFirstToken = true; removeTypingIfAny(); } mdBuffer += data.delta; scheduleRender(); }
            else if (typeof data.content === 'string') { if (!hasFirstToken) { hasFirstToken = true; removeTypingIfAny(); } mdBuffer += data.content; scheduleRender(); }
            else if (data.choices && data.choices[0]) {
              const ch = data.choices[0];
              if (ch.delta && typeof ch.delta.content === 'string') { if (!hasFirstToken) { hasFirstToken = true; removeTypingIfAny(); } mdBuffer += ch.delta.content; scheduleRender(); }
              else if (typeof ch.text === 'string') { if (!hasFirstToken) { hasFirstToken = true; removeTypingIfAny(); } mdBuffer += ch.text; scheduleRender(); }
              if (ch.finish_reason) { scheduleRender(); }
            }
            if (data.done === true) { removeTypingIfAny(); scheduleRender(); }
          } catch (e) { console.warn('Failed to parse SSE data:', line, e); }
        }
      }
    }
  };

  const pump = () => reader.read().then(({ value, done }) => {
    const stick = isNearBottom();
    if (done) {
      const remainder = decoder.decode();
      if (remainder) sseBuffer += remainder;
      processBuffer();
      scrollToBottomIfNeeded(stick);
      return;
    }
    const text = decoder.decode(value, { stream: true });
    sseBuffer += text;
    processBuffer();
    scrollToBottomIfNeeded(stick);
    return pump();
  });

  return pump();
}).catch((error) => {
  // Remove typing indicator if present
  try { removeTypingIfAny(); } catch(e) {}
  const errRow = document.createElement('div');
  errRow.className = 'chat-row';
  const errMsg = document.createElement('div');
  errMsg.className = 'chat-msg assistant';
  errMsg.textContent = 'Error: ' + error.message;
  errRow.appendChild(errMsg);
  output.appendChild(errRow);
  output.scrollTop = output.scrollHeight;
});

return false;
};

// Toggle chat fullscreen and ESC to exit
window.toggleChatFullscreen = function() {
  const section = document.getElementById('chatbot-section');
  if (!section) return false;
  const entering = !section.classList.contains('chat-fullscreen');
  section.classList.toggle('chat-fullscreen');
  const escHandler = function(e) {
    if (e.key === 'Escape') {
      section.classList.remove('chat-fullscreen');
      document.removeEventListener('keydown', escHandler);
      document.body.style.overflow = document.body.dataset.prevOverflow || '';
      document.documentElement.style.overflow = document.documentElement.dataset.prevOverflow || '';
    }
  };
  if (entering) {
    document.body.dataset.prevOverflow = document.body.style.overflow || '';
    document.body.style.overflow = 'hidden';
    document.documentElement.dataset.prevOverflow = document.documentElement.style.overflow || '';
    document.documentElement.style.overflow = 'hidden';
    document.addEventListener('keydown', escHandler);
    section._escHandler = escHandler;
  } else {
    if (section._escHandler) document.removeEventListener('keydown', section._escHandler);
    document.body.style.overflow = document.body.dataset.prevOverflow || '';
    document.documentElement.style.overflow = document.documentElement.dataset.prevOverflow || '';
    section._escHandler = null;
  }
  // After layout change, ensure chat scrolls to bottom
  const out = document.getElementById('chatbot-output');
  if (out) {
    out.scrollTop = out.scrollHeight;
    requestAnimationFrame(() => { out.scrollTop = out.scrollHeight; });
    setTimeout(() => { try { out.scrollTop = out.scrollHeight; } catch(e) {} }, 150);
  }
  return false;
};

window.closeChatbot = function() {
  var chatbotSection = document.getElementById('chatbot-section');
  var chatbotBtn = document.getElementById('chatbotToggleBtn');
  if (chatbotSection) {
    chatbotSection.style.display = 'none';
    if (chatbotBtn) {
      chatbotBtn.classList.remove('selected');
    }

    var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
    openSections = openSections.filter(function(section) { return section !== 'chatbot'; });
    localStorage.setItem('workbench-open-sections', JSON.stringify(openSections));
    updateNotesVisibility();
  }
  return false;
};

         // Update app function
         window.updateApp = function() {
           // Show loading overlay
           const loader = document.getElementById('loader');
           const loaderText = document.getElementById('loader-text');
           const loaderPercentage = document.getElementById('loader-percentage');
           const loaderBar = document.querySelector('.loader');

           if (loader && loaderText) {
             loaderText.textContent = 'PATCHING CODE FILES FROM GIT';
             loader.style.display = 'flex';

             // Start progress animation
             let progress = 0;
             const progressInterval = setInterval(() => {
               progress += 2;
               if (progress <= 100) {
                 if (loaderPercentage) {
                   loaderPercentage.textContent = progress + '%';
                 }
                 if (loaderBar) {
                   loaderBar.style.setProperty('--progress', progress + '%');
                 }
               } else {
                 clearInterval(progressInterval);
               }
             }, 100);
           }

           // Call the update endpoint
           fetch('/update')
             .then(response => {
               if (response.ok) {
                 return response.text();
               }
               throw new Error('Update failed');
             })
             .then(message => {
               // Set progress to 100% and show success
               if (loaderPercentage) {
                 loaderPercentage.textContent = '100%';
               }
               if (loaderBar) {
                 loaderBar.style.setProperty('--progress', '100%');
               }

               if (loaderText) {
                 loaderText.textContent = 'UPDATED SUCCESSFULLY';
               }

               // Wait a few seconds then redirect to show the update is complete
               setTimeout(() => {
                 if (loaderText) {
                   loaderText.textContent = 'RELOADING APP';
                 }
                 setTimeout(() => {
                   if (loaderText) {
                     loaderText.textContent = 'RELOAD COMPLETE';
                   }
                   setTimeout(() => {
                     window.location.reload();
                   }, 1000);
                 }, 1000);
               }, 1000);
             })
             .catch(error => {
               console.error('Update error:', error);
               if (loaderText) {
                 loaderText.textContent = 'UPDATE FAILED: ' + error.message;
               }
               // Hide loader after showing error
               setTimeout(() => {
                 if (loader) {
                   loader.style.display = 'none';
                 }
               }, 3000);
             });
         };





         // Restore state on page load
         window.restoreOpenSection = function() {
           try {
             var openSections = JSON.parse(localStorage.getItem('workbench-open-sections') || '[]');
             var terminalBtn = document.getElementById('terminalToggleBtn');
             var textBtn = document.getElementById('textEncryptionToggleBtn');
             var chatbotBtn = document.getElementById('chatbotToggleBtn');

             console.log('Restoring sections:', openSections);
             console.log('Terminal button found:', !!terminalBtn);
             console.log('Text button found:', !!textBtn);
             console.log('Chatbot button found:', !!chatbotBtn);

             // Restore terminal if it was open
             if (openSections.includes('terminal')) {
               console.log('Terminal should be open');
               var terminalSection = document.getElementById('terminal-section');
               if (terminalSection) {
                 console.log('Terminal section exists, showing it');
                 terminalSection.style.display = 'block';
                 if (terminalBtn) {
                   terminalBtn.classList.add('selected');
                   console.log('Terminal button marked as selected');
                 }
               } else {
                 console.log('Terminal section does not exist, creating it');
                 // Create terminal if it doesn't exist
                 createAndShowTerminal(false);
               }
             } else {
               console.log('Terminal should be closed');
               // Ensure terminal is closed and button is not selected
               var terminalSection = document.getElementById('terminal-section');
               if (terminalSection) {
                 terminalSection.style.display = 'none';
               }
               if (terminalBtn) {
                 terminalBtn.classList.remove('selected');
               }
             }

             // Restore text encryption if it was open
             if (openSections.includes('text')) {
               console.log('Text encryption should be open');
               var textSection = document.getElementById('text-encryption-section');
               if (textSection) {
                 console.log('Text section exists, showing it');
                 textSection.style.display = 'block';
                 if (textBtn) {
                   textBtn.classList.add('selected');
                   console.log('Text button marked as selected');
                 }
               } else {
                 console.log('Text section does not exist, creating it');
                 // Create text section if it doesn't exist
                 createAndShowTextEncryption(false);
               }
             } else {
               console.log('Text encryption should be closed');
               // Ensure text section is closed and button is not selected
               var textSection = document.getElementById('text-encryption-section');
               if (textSection) {
                 textSection.style.display = 'none';
               }
               if (textBtn) {
                 textBtn.classList.remove('selected');
               }
             }

             // Restore tools if it was open
             if (openSections.includes('tools')) {
               console.log('Tools should be open');
               var toolsSection = document.getElementById('tools-section');
               var toolsBtn = document.getElementById('toolsToggleBtn');
               if (toolsSection) {
                 console.log('Tools section exists, showing it');
                 toolsSection.style.display = 'block';
                 if (toolsBtn) {
                   toolsBtn.classList.add('selected');
                   console.log('Tools button marked as selected');
                 }
               } else {
                 console.log('Tools section does not exist, creating it');
                 createAndShowTools(false);
               }
             } else {
               console.log('Tools should be closed');
               var toolsSection = document.getElementById('tools-section');
               var toolsBtn = document.getElementById('toolsToggleBtn');
               if (toolsSection) {
                 toolsSection.style.display = 'none';
               }
               if (toolsBtn) {
                 toolsBtn.classList.remove('selected');
               }
             }




             // Restore chatbot if it was open
             if (openSections.includes('chatbot')) {
               console.log('Chatbot should be open');
               var chatbotSection = document.getElementById('chatbot-section');
               if (chatbotSection) {
                 console.log('Chatbot section exists, showing it');
                 chatbotSection.style.display = 'block';
                 if (chatbotBtn) {
                   chatbotBtn.classList.add('selected');
                   console.log('Chatbot button marked as selected');
                 }
               } else {
                 console.log('Chatbot section does not exist, creating it');
                 createAndShowChatbot(false);
               }
             }

           } catch (error) {
             console.error('Error restoring sections:', error);
           }

           // Update notes visibility after restoring
           updateNotesVisibility();
         };

         // Reusable modal for errors/info
         function showModalMessage(title, message) {
           let modal = document.getElementById('global-modal');
           if (!modal) {
             modal = document.createElement('div');
             modal.id = 'global-modal';
             document.body.appendChild(modal);
           }
           // Always (re)build inner structure so elements exist after prior close
                      modal.innerHTML = `
              <div id="global-modal-backdrop" style="position:fixed;inset:0;background:rgba(0,0,0,0.35);backdrop-filter:blur(6px);-webkit-backdrop-filter:blur(6px);display:flex;align-items:center;justify-content:center;z-index:99999;">
                <div id="global-modal-card" class="theme-transition" style="width:600px;max-width:90vw;background:#fff;border:1px solid #e5e7eb;box-shadow:0 10px 25px rgba(0,0,0,0.15);">
                  <div id="global-modal-header" class="theme-transition" style="display:flex;align-items:center;justify-content:space-between;padding:14px 16px;border-bottom:1px solid #e5e7eb;background:#f8fafc;">
                    <div id="global-modal-title" style="font-weight:600;flex:1;text-align:center"></div>
                    <button id="global-modal-close" style="background:none;border:none;font-size:18px;line-height:1;cursor:pointer">×</button>
                  </div>
                  <div id="global-modal-body" style="padding:16px;white-space:pre-wrap;color:#111827;text-align:center"></div>
                </div>
              </div>`;
           // Wire up close handlers
           document.getElementById('global-modal-close').addEventListener('click', () => {
             const bd = document.getElementById('global-modal-backdrop'); if (bd) bd.remove();
           });
           document.getElementById('global-modal-backdrop').addEventListener('click', (e) => {
             if (e.target && e.target.id === 'global-modal-backdrop') {
               e.currentTarget.remove();
             }
           });

           // Set content
           document.getElementById('global-modal-title').textContent = title || 'Notice';
                      const __modalBody = document.getElementById('global-modal-body');
            // Split long technical sub-parts (like URLs) onto a smaller line
            const msgStr = String(message || '');
            // If HTML content is provided, render it as HTML (used for extract summary lists)
            const looksLikeHtml = /<\s*([a-z][\s\S]*?)>/i.test(msgStr);
            if (looksLikeHtml) {
              // Render provided HTML directly
              __modalBody.innerHTML = msgStr;
              __modalBody.style.maxHeight = '70vh';
              __modalBody.style.overflowY = 'auto';
              __modalBody.style.wordBreak = 'break-word';
            } else {
              let mainMsg = msgStr;
              let subMsg = '';
              // Heuristic: if there is a quoted URL or credentials link, treat that as sub-message
              const urlPattern = /\"?(https?:\/\/[^\s\"]+)\"?/i;
              const urlMatch = msgStr.match(urlPattern);
              if (urlMatch) {
                const full = urlMatch[0];
                const urlOnly = urlMatch[1] || urlMatch[0];
                // Remove the URL (and any surrounding quotes) from the main message
                mainMsg = msgStr.replace(full, '')
                                .replace(/\s*\"\"\s*/g, ' ') // remove leftover empty quotes
                                .replace(/\s{2,}/g, ' ')
                                .trim();
                // Show clean URL (no quotes) as sub-message
                subMsg = urlOnly;
              }
              __modalBody.innerHTML = '';
              const mainEl = document.createElement('div');
              mainEl.textContent = mainMsg;
              mainEl.style.fontSize = '1rem';
              const subEl = document.createElement('div');
              if (subMsg) {
                subEl.textContent = subMsg;
                subEl.style.fontSize = '0.85rem';
                subEl.style.marginTop = '8px';
                subEl.style.opacity = '0.9';
                subEl.style.wordBreak = 'break-all';
              }
              __modalBody.appendChild(mainEl);
              if (subMsg) __modalBody.appendChild(subEl);
              __modalBody.style.maxHeight = '70vh';
              __modalBody.style.overflowY = 'auto';
              __modalBody.style.wordBreak = 'break-word';
            }
            // If the message indicates an expired/invalid token, offer a Refresh Token action
           try {
             const msgLc = String(message || '').toLowerCase();
             const tokenIssue = msgLc.includes('token') && (msgLc.includes('expired') || msgLc.includes('invalid') || msgLc.includes('refresh'));
             if (tokenIssue) {
               const actions = document.createElement('div');
               actions.style.marginTop = '16px'; actions.style.display='flex'; actions.style.justifyContent='center';
               actions.innerHTML = `<button id="modal-refresh-token" class="btn btn-primary" style="border-radius:0">\u21bb Refresh AWS Token</button>`;
               __modalBody.appendChild(actions);
               const btn = document.getElementById('modal-refresh-token');
               if (btn) btn.addEventListener('click', function(){ window.location = '/refreshtoken'; });
             }
           } catch(e) {}

           // Theme-aware styling
           (function(){
             const bd = document.getElementById('global-modal-backdrop');
             const card = document.getElementById('global-modal-card');
             const header = document.getElementById('global-modal-header');
             const bodyEl = document.getElementById('global-modal-body');
             const bodyCls = document.body.className || '';
             let bg = '#ffffff', text = '#111827', border = '#e5e7eb', headerBg = '#f8fafc';
             if (bodyCls.includes('dark-theme')) { bg = '#1e293b'; text = '#e2e8f0'; border = '#334155'; headerBg = '#0f172a'; }
             else if (bodyCls.includes('white-theme')) { bg = '#f8fafc'; text = '#1e293b'; border = '#e2e8f0'; headerBg = '#f1f5f9'; }
             else if (bodyCls.includes('pink-theme')) { bg = '#fdf2f8'; text = '#831843'; border = '#f9a8d4'; headerBg = '#fce7f3'; }
             if (card) { card.style.background = bg; card.style.borderColor = border; }
             if (header) { header.style.background = headerBg; header.style.borderBottomColor = border; }
             if (bodyEl) { bodyEl.style.color = text; }
             // Adjust summary list styles for theme
             try {
               const scroll = bd.querySelector('.workbench-scroll');
               const items = bd.querySelectorAll('.workbench-list-item');
               if (scroll) { scroll.style.borderColor = border; }
               items.forEach(li => { li.style.borderBottomColor = border; });
             } catch(e) {}
           })();
         }

          const s3Input       = document.getElementById('s3_path');
          const localInput    = document.getElementById('local_path');
          const pathInput     = document.getElementById('path_input');
          const fileInput     = document.getElementById('upload_file');
          const editS3Btn     = document.getElementById('editS3Btn');
          const editLocalBtn  = document.getElementById('editLocalBtn');
          const downloadBtn   = document.getElementById('downloadBtn');
          const clearBtn      = document.getElementById('clearBtn');
          console.log('Clear button element:', clearBtn);
          const downloadLabel = document.getElementById('downloadLabel');
          const limitInput    = document.getElementById('limit_input');
          const recordsPerPage = document.getElementById('recordsPerPage');
          const recordsPerPageInput = document.getElementById('records_per_page_input');

          function hasValidPath(val) {
            // For download purposes, accept any file with an extension OR allow no extension for code
            const v = val.trim();
            return /\.[a-zA-Z0-9]+$/i.test(v) || /\/[^/]+$/i.test(v); // allow no-extension filename
          }

          function toggleButtons() {
            const s3Valid = hasValidPath(s3Input.value) && s3Input.value.trim().toLowerCase().startsWith('s3://');
                          // Enable Extract when s3 path starts with s3:// and ends with '/'
              const rawPath = (s3Input.value || '').trim();
              const s3IsFolder = /^s3:\/\//i.test(rawPath) && /\/$/.test(rawPath);
              const downloadAllBtn = document.getElementById('downloadAllBtn');
              if (downloadAllBtn) downloadAllBtn.disabled = !s3IsFolder;
            const localValid = fileInput.files.length > 0;

            // Edit buttons - enable for editable file types, including code
            const s3Raw = s3Input.value.trim();
            const s3Val = s3Raw.toLowerCase();
            const s3PrefixOk = s3Val.startsWith('s3://');
            const localName = (fileInput.files[0]?.name || '').toLowerCase();
            const isCsvJson = /\.(csv|json|jsonl|gz)$/i;
            const isCode = /\.(py|html?|js|go|md|xml|css|sql|sh|bash|yaml|yml|toml|ini|conf|cfg|txt|properties|dockerfile)$/i;
            const s3HasNoExt = s3Valid && !/\.[a-z0-9]+$/i.test(s3Val);
            const localHasNoExt = localValid && !/\.[a-z0-9]+$/i.test(localName);
            const isEditableS3File = s3Valid && s3PrefixOk && (isCsvJson.test(s3Val) || isCode.test(s3Val) || s3HasNoExt);
            const isEditableLocalFile = localValid && (isCsvJson.test(localName) || isCode.test(localName) || localHasNoExt);
            editS3Btn.disabled     = !isEditableS3File;
            editLocalBtn.disabled  = !isEditableLocalFile;

                      // Download button - enable ONLY for S3 files, not local files
           // For download from S3, require s3:// prefix and valid path
           downloadBtn.disabled   = !(s3Valid && s3PrefixOk);

                        // Upload buttons - only enable for local files
             const encryptUploadBtn = document.getElementById('encryptUploadBtn');
             const plainUploadBtn = document.getElementById('plainUploadBtn');
             if (encryptUploadBtn) encryptUploadBtn.disabled = !localValid;
             if (plainUploadBtn) plainUploadBtn.disabled = !localValid;

            console.log(`Button states - S3 Valid: ${s3Valid}, Local Valid: ${localValid}, Editable S3: ${isEditableS3File}, Editable Local: ${isEditableLocalFile}`);
            console.log(`Buttons - Edit S3: ${!editS3Btn.disabled}, Edit Local: ${!editLocalBtn.disabled}, Download: ${!downloadBtn.disabled}, Encrypt: ${encryptUploadBtn ? !encryptUploadBtn.disabled : 'N/A'}`);

            // Button class toggling is handled by the btn classes
          }

          // Local file browse
          document.getElementById('browseBtn').addEventListener('click', () => fileInput.click());
          fileInput.addEventListener('change', () => {
            if (fileInput.files.length > 0) {
              const fileName = fileInput.files[0].name;
              const fileSize = fileInput.files[0].size;
              localInput.value = fileName;
              console.log(`File selected: ${fileName}, Size: ${fileSize} bytes`);
              // DO NOT clear S3 path - user wants to save back to same location
            } else {
              localInput.value = '';
              console.log('No file selected');
            }
            toggleButtons();
            // Do not automatically reload the page when selecting a file
          });

          // Paste button
          document.getElementById('pasteBtn').addEventListener('click', async () => {
            try {
              s3Input.value = await navigator.clipboard.readText();
              // DO NOT clear local file - user might want to edit local and save to this S3 path
            } catch {
              showModalMessage('Clipboard', 'Clipboard paste failed');
            }
            toggleButtons();
          });

          // S3 input change
          s3Input.addEventListener('input', () => {
            // DO NOT clear local file - user might be updating where to save
            toggleButtons();
          });

          // Keep limit in sync
          function updateLimit() {
            let v = downloadLabel.innerText.trim();
            if (v && !/^\d+$/.test(v)) v = 'All';
            downloadLabel.innerText = v;
            limitInput.value = v;
          }
          downloadLabel.addEventListener('blur', updateLimit);

                     // Download All (outside modal)
            const downloadAllBtn = document.getElementById('downloadAllBtn');
            if (downloadAllBtn) {
              downloadAllBtn.addEventListener('click', async (e) => {
                try {
                  e.preventDefault();
                  // Require a folder path
                               const raw = (s3Input.value || '').trim();
              if (!/^s3:\/\//i.test(raw) || !/\/$/.test(raw)) {
                showModalMessage('Extract', 'Please select an S3 folder path that ends with / (e.g., s3://bucket/path/)');
                return;
              }
              // Ensure trailing slash
              let folderPath = raw.replace(/^s3:\/\//i, '');
              if (!/\/$/.test(folderPath)) folderPath += '/';
              const full = 's3://' + folderPath;
                  const moduleVal = document.querySelector('select[name="module"]').value;
                  const resp = await fetch('/download-all', {
                    method: 'POST', headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ path: full, module: moduleVal })
                  });
                  const data = await resp.json();
                  if (!resp.ok || data.status !== 'started') {
                    showModalMessage('Extract', data && data.message ? data.message : 'Failed to start extraction');
                    return;
                  }
                  showBatchDownloadLoader(data.job_id);
                } catch(err) {
                  console.error('Extract error:', err);
                  showModalMessage('Extract', String(err));
                }
              });
            }

            // Download button
            downloadBtn.addEventListener('click', async (e) => {
             try {
               e.preventDefault();
               updateLimit();

               // Determine which path to use for download
               let downloadPath = '';
            if (hasValidPath(s3Input.value)) {
              downloadPath = s3Input.value.trim();
            } else if (fileInput.files.length > 0) {
              downloadPath = fileInput.files[0].name;
            }

            // Set up download form values
            const downloadForm = document.getElementById('download-form');
            document.getElementById('download_path').value = downloadPath;
            document.getElementById('download_module').value = document.querySelector('select[name="module"]').value;
            document.getElementById('download_limit').value = limitInput.value;

            // Show loader
            const loader = document.getElementById('loader');
            const loaderText = document.getElementById('loader-text');
            showDownloadLoader();

            // Mark loader as download mode and make it dismissible
            loader.classList.add('download-mode');
            loader.onclick = function(event) {
              if (loader.classList.contains('download-mode')) {
                loader.style.display = 'none';
                loader.classList.remove('download-mode');
                loader.onclick = null;
              }
            };

            // Submit download form
            downloadForm.submit();

            // Auto-hide loader after 3 seconds
            setTimeout(() => {
              if (loader.style.display !== 'none') {
                loader.style.display = 'none';
                loader.classList.remove('download-mode');
                loader.onclick = null;
              }
            }, 3000);

            // Show click to dismiss message after 2 seconds
            setTimeout(() => {
              if (loader.style.display !== 'none') {
                loaderText.innerHTML = 'DOWNLOAD STARTING';
              }
                       }, 2000);
          } catch (err) {
            console.error('Download click handler error:', err);
            showModalMessage('Download Error', String(err && err.message ? err.message : err));
          }
          });

          // Upload buttons
           const encryptUploadBtn = document.getElementById('encryptUploadBtn');
           const plainUploadBtn = document.getElementById('plainUploadBtn');
           if (encryptUploadBtn) {
             encryptUploadBtn.addEventListener('click', (e) => {
              e.preventDefault();

              console.log('Upload button clicked');

              // Check if S3 path is provided
              if (!s3Input.value.trim() || !s3Input.value.trim().toLowerCase().startsWith('s3://')) {
                console.log('Invalid S3 path provided');
                showModalMessage('Upload', 'Please provide a valid S3 path (starting with s3://) for upload');
                return;
              }

                           const s3Path = s3Input.value.trim();
              const module = document.querySelector('select[name="module"]').value;

              // Check if a local file is selected
              const mainFileInput = document.getElementById('upload_file');
              if (mainFileInput.files.length === 0) {
                console.log('No file selected for upload');
                showModalMessage('Upload', 'Please select a local file to upload');
                return;
              }
              const localFile = mainFileInput.files[0];
              console.log(`\n\n=== UPLOAD START ===\nLocal file: ${localFile ? localFile.name : '(none)'}\nS3 path: ${s3Path}\nModule: ${module}\nMode: Upload - Encrypt\n===\n\n`);
              console.log('Detail: preparing upload-encrypt form and copying File object...');

              // Validate extension compatibility (exact core match or non-gz -> gz)
               const localName = localFile.name.toLowerCase();
               const tgt = s3Path.toLowerCase();
               function core(name){
                 if (name.endsWith('.csv.gz')) return ['csv', true];
                 if (name.endsWith('.jsonl.gz')) return ['jsonl', true];
                 if (name.endsWith('.json.gz')) return ['json', true];
                 if (name.endsWith('.csv')) return ['csv', false];
                 if (name.endsWith('.jsonl')) return ['jsonl', false];
                 if (name.endsWith('.json')) return ['json', false];
                 if (name.endsWith('.xlsx')) return ['xlsx', false];
                 if (name.endsWith('.xls')) return ['xls', false];
                 const m = name.match(/\.([a-z0-9]+)$/i); return [m?m[1]:'', false];
               }
               const [lc, lgz] = core(localName);
               const [tc, tgz] = core(tgt);
               const ok = (lc===tc && lgz===tgz) || (lc===tc && !lgz && tgz);
               if (!ok) {
                 showModalMessage('Upload', `File type mismatch.\n\nSelected: ${localFile.name}\nTarget: ${s3Path}\n\nAllowed: same type or upgrade to .gz target (e.g., .csv -> .csv.gz, .json -> .json.gz, .jsonl -> .jsonl.gz).`);
                 return;
               }

              // Set up encrypt form values
              const encryptForm = document.getElementById('encrypt-form');
              document.getElementById('encrypt_s3_path').value = s3Path;
              document.getElementById('encrypt_module').value = module;

              // Copy file from main file input to encrypt form
              const encryptFileInput = document.getElementById('encrypt_upload_file');

              // Create a new FileList-like object
              const dataTransfer = new DataTransfer();
              dataTransfer.items.add(localFile);
              encryptFileInput.files = dataTransfer.files;
              console.log('File copied to encrypt form');

              // Show encrypt upload loader with progress
              showEncryptUploadLoader();
                          console.log('Upload-encrypt loader started');

             console.log('Submitting upload-encrypt form');
             // Submit encrypt form
             encryptForm.submit();
           });
         }

         if (plainUploadBtn) {
           plainUploadBtn.addEventListener('click', (e) => {
             e.preventDefault();
             if (!s3Input.value.trim() || !s3Input.value.trim().toLowerCase().startsWith('s3://')) {
               showModalMessage('Upload', 'Please provide a valid S3 path (starting with s3://) for upload');
               return;
             }
             const s3Path = s3Input.value.trim();
             const module = document.querySelector('select[name="module"]').value;
             const mainFileInput = document.getElementById('upload_file');
             if (mainFileInput.files.length === 0) { showModalMessage('Upload', 'Please select a local file to upload'); return; }
             const localFile = mainFileInput.files[0];
             console.log(`\n\n=== UPLOAD START ===\nLocal file: ${localFile ? localFile.name : '(none)'}\nS3 path: ${s3Path}\nModule: ${module}\nMode: Upload (no encryption)\n===\n\n`);
             console.log('Detail: preparing plain-upload form and copying File object...');

             // Validate extension compatibility (exact core match or non-gz -> gz)
             const localName = localFile.name.toLowerCase();
             const tgt = s3Path.toLowerCase();
             function core2(name){
               if (name.endsWith('.csv.gz')) return ['csv', true];
               if (name.endsWith('.jsonl.gz')) return ['jsonl', true];
               if (name.endsWith('.json.gz')) return ['json', true];
               if (name.endsWith('.csv')) return ['csv', false];
               if (name.endsWith('.jsonl')) return ['jsonl', false];
               if (name.endsWith('.json')) return ['json', false];
               if (name.endsWith('.xlsx')) return ['xlsx', false];
               if (name.endsWith('.xls')) return ['xls', false];
               const m = name.match(/\.([a-z0-9]+)$/i); return [m?m[1]: '', false];
             }
             const [lc2, lgz2] = core2(localName);
             const [tc2, tgz2] = core2(tgt);
             const ok2 = (lc2===tc2 && lgz2===tgz2) || (lc2===tc2 && !lgz2 && tgz2);
             if (!ok2) {
               showModalMessage('Upload', `File type mismatch.\n\nSelected: ${localFile.name}\nTarget: ${s3Path}\n\nAllowed: same type or upgrade to .gz target (e.g., .csv -> .csv.gz, .json -> .json.gz, .jsonl -> .jsonl.gz).`);
               return;
             }

             const plainForm = document.getElementById('plain-upload-form');
             document.getElementById('plain_s3_path').value = s3Path;
             document.getElementById('plain_module').value = module;
             const plainFileInput = document.getElementById('plain_upload_file');
             const dt = new DataTransfer(); dt.items.add(localFile); plainFileInput.files = dt.files;

             // Reuse encrypt loader styling for consistency
             showEncryptUploadLoader();
             plainForm.submit();
           });
                 }

         // Airflow button
         const airflowBtn = document.getElementById('airflowBtn');
         if (airflowBtn) {
           airflowBtn.addEventListener('click', async (e) => {
             e.preventDefault();
             try {
               airflowBtn.disabled = true;
               const res = await fetch('/open-airflow', { method: 'POST' });
               let data = null;
               try { data = await res.json(); } catch {}
               if (res.ok && data && data.url) {
                 window.open(data.url, '_blank');
               } else {
                 let msg = 'Failed to open Airflow';
                 if (data && data.message) msg = `${msg}: ${data.message}`;
                 if (data && data.stderr) msg += `\n\nDetails:\n${data.stderr}`;
                 if (res.status === 401) {
                   msg += `\n\nClick the refresh button to log in, then try again.`;
                 }
                 showModalMessage('Airflow', msg);
               }
             } catch (err) {
               console.error('Airflow open failed:', err);
               showModalMessage('Airflow', 'Failed to open Airflow. Check logs.');
             } finally {
               airflowBtn.disabled = false;
             }
           });
         }

         // CloudWatch button
         const cloudwatchBtn = document.getElementById('cloudwatchBtn');
         if (cloudwatchBtn) {
           cloudwatchBtn.addEventListener('click', async (e) => {
             e.preventDefault();
             try {
               cloudwatchBtn.disabled = true;
               const res = await fetch('/open-cloudwatch', { method: 'POST' });
               let data = null;
               try { data = await res.json(); } catch {}
               if (res.ok && data && data.url) {
                 window.open(data.url, '_blank');
               } else {
                 let msg = 'Failed to open CloudWatch';
                 if (data && data.message) msg = `${msg}: ${data.message}`;
                 if (res.status === 401) msg += `\n\nClick the refresh button to log in, then try again.`;
                 showModalMessage('CloudWatch', msg);
               }
             } catch (err) {
               console.error('CloudWatch open failed:', err);
               showModalMessage('CloudWatch', 'Failed to open CloudWatch. Check logs.');
             } finally {
               cloudwatchBtn.disabled = false;
             }
           });
         }

         // S3 button
         const s3Btn = document.getElementById('s3Btn');
         if (s3Btn) {
           s3Btn.addEventListener('click', async (e) => {
             e.preventDefault();
             try {
               s3Btn.disabled = true;
               const res = await fetch('/open-s3', { method: 'POST' });
               let data = null;
               try { data = await res.json(); } catch {}
               if (res.ok && data && data.url) {
                 window.open(data.url, '_blank');
               } else {
                 let msg = 'Failed to open S3';
                 if (data && data.message) msg = `${msg}: ${data.message}`;
                 if (res.status === 401) msg += `\n\nClick the refresh button to log in, then try again.`;
                 showModalMessage('S3', msg);
               }
             } catch (err) {
               console.error('S3 open failed:', err);
               showModalMessage('S3', 'Failed to open S3. Check logs.');
             } finally {
               s3Btn.disabled = false;
             }
           });
         }

          // Edit buttons
          editS3Btn.addEventListener('click', (e) => {
            try {
              if (e && e.preventDefault) e.preventDefault();
              updateRecordsPerPage();
              updateRawEditHiddenField(); // Add raw edit preference to form
              const mainForm = document.getElementById('main-form');
              // Ensure action=edit is present explicitly
              let act = mainForm.querySelector('input[name="action"][value="edit"]');
              if (!act) {
                act = document.createElement('input');
                act.type = 'hidden';
                act.name = 'action';
                act.value = 'edit';
                mainForm.appendChild(act);
              }
              showLoader();
              mainForm.submit();
            } catch(err) {
              console.error('Edit click handler error:', err);
            }
          });

                    editLocalBtn.addEventListener('click', (e) => {
             try {
               if (e && e.preventDefault) e.preventDefault();
               updateRecordsPerPage();
               updateRawEditHiddenField(); // Add raw edit preference to form
               // Ensure the current S3 path is preserved when editing local files
               document.getElementById('orig_s3_path').value = s3Input.value;
               showLoader();
               const mainForm = document.getElementById('main-form');
               // Ensure action=edit is present explicitly
               let act = mainForm.querySelector('input[name="action"][value="edit"]');
               if (!act) {
                 act = document.createElement('input');
                 act.type = 'hidden';
                 act.name = 'action';
                 act.value = 'edit';
                 mainForm.appendChild(act);
               }
               mainForm.submit();
             } catch(err) {
               console.error('Edit local click handler error:', err);
             }
           });

          // Clear button
          console.log('Adding event listener to clear button...');
          clearBtn.addEventListener('click', () => {
            console.log('Clear button clicked!');
            // Clear file input fields
            s3Input.value = '';
            fileInput.value = '';
            localInput.value = '';
            downloadLabel.innerText = 'All';
            limitInput.value = 'All';

            // Clear additional input fields
            const recordsPerPageInput = document.getElementById('records_per_page_input');
            if (recordsPerPageInput) {
              recordsPerPageInput.value = '';
            }

            // Clear encryption/decryption fields
            cryptText.value = '';
            cryptResult.value = '';

            // Reset module selectors to default
            const cryptModuleSelect = document.querySelector('select[name="crypt_module"]');
            if (cryptModuleSelect) {
              cryptModuleSelect.value = 'dxp'; // Reset to default
            }

            const mainModuleSelect = document.querySelector('select[name="module"]');
            if (mainModuleSelect) {
              mainModuleSelect.value = 'dxp'; // Reset to default
            }

            // Clear saved crypt text from localStorage (both old and new keys)
            localStorage.removeItem('secure-crypt-text');
            localStorage.removeItem('cryptText');
            // Note: No need to clear result since it's not saved to localStorage

            // Preserve notes - don't clear notes textarea or localStorage
            // const notesTextarea = document.getElementById('notesTextarea');
            // if (notesTextarea) {
            //   notesTextarea.value = '';
            // }

            // Clear terminal outputs
            console.log('Attempting to clear terminal outputs...');
            const homeTerminalOutput = document.getElementById('home-terminal-output');
            console.log('Home terminal output element:', homeTerminalOutput);
            if (homeTerminalOutput) {
              console.log('Clearing home terminal output...');
              homeTerminalOutput.innerHTML = '';
              console.log('Cleared home terminal output');

              // Restore welcome message after clearing
              const theme = document.body.className.includes('white-theme') ? 'white' : 
                           document.body.className.includes('pink-theme') ? 'pink' : 'dark';

              const welcomeColor = theme === 'dark' ? '#00ff00' : 
                                  theme === 'white' ? '#4b5563' : '#831843';
              const helpColor = theme === 'dark' ? '#00ff00' : 
                               theme === 'white' ? '#6b7280' : '#be185d';

              homeTerminalOutput.innerHTML = '<span style="color: ' + welcomeColor + ';">Welcome to Sequoia WorkBench Terminal</span><br><span style="color: ' + helpColor + ';">Type some command e.g. pip install pandas</span><br><br>';
              console.log('Welcome message restored');
            } else {
              console.log('Home terminal output element not found');
            }

            const terminalOutput = document.getElementById('terminal-output');
            if (terminalOutput) {
              terminalOutput.innerHTML = '';
              console.log('Cleared modal terminal output');
            } else {
              console.log('Modal terminal output element not found');
            }

            // Clear chatbot output and input
            const chatOutput = document.getElementById('chatbot-output');
            const chatInput = document.getElementById('chatbot-input');
            if (chatOutput) {
              chatOutput.innerHTML = '';
              chatOutput.scrollTop = 0;
            }
            if (chatInput) {
              chatInput.value = '';
              try { chatInput.style.height = 'auto'; chatInput.style.height = '44px'; } catch(e) {}
            }

            // Clear any error messages
            const errorMsgs = document.querySelectorAll('.text-red-600');
            errorMsgs.forEach(msg => msg.remove());

            // Disable encrypt upload button
            const encryptUploadBtn = document.getElementById('encryptUploadBtn');
            if (encryptUploadBtn) {
              encryptUploadBtn.disabled = true;
            }

            toggleButtons();
          });

          // Encryption/Decryption functionality
          const cryptText = document.getElementById('cryptText');
          const cryptResult = document.getElementById('cryptResult');
          const encryptBtn = document.getElementById('encryptBtn');
          const decryptBtn = document.getElementById('decryptBtn');

          // Backup: Load saved crypt text from localStorage (legacy support)
          const savedCryptText = localStorage.getItem('cryptText') || localStorage.getItem('secure-crypt-text') || '';
          if (savedCryptText && cryptText) {
            cryptText.value = savedCryptText;
          }

          // Backup: Save crypt text to localStorage on input (legacy support)
          if (cryptText) {
            cryptText.addEventListener('input', () => {
              localStorage.setItem('secure-crypt-text', cryptText.value);
              // Keep legacy key for backward compatibility
              localStorage.setItem('cryptText', cryptText.value);
            });
          }

          function showCryptLoader(action) {
            const loader = document.getElementById('loader');
            const loaderText = document.getElementById('loader-text');
            const loaderPercentage = document.getElementById('loader-percentage');
            const loaderBar = document.querySelector('.loader::before') || document.querySelector('.loader');

            loader.style.display = 'flex';
            loaderText.textContent = action === 'encrypt' ? 'ENCRYPTING' : 'DECRYPTING';

            // Animate percentage
            let progress = 0;
            const interval = setInterval(() => {
              progress += Math.random() * 15;
              if (progress > 90) progress = 90;
              loaderPercentage.textContent = Math.round(progress) + '%';
              if (loaderBar) {
                loaderBar.style.setProperty('--progress', progress + '%');
              }
            }, 100);

            // Store interval for cleanup
            loader.dataset.interval = interval;
          }

          function hideCryptLoader() {
            const loader = document.getElementById('loader');
            const loaderPercentage = document.getElementById('loader-percentage');
            const loaderBar = document.querySelector('.loader::before') || document.querySelector('.loader');

            // Complete the progress
            loaderPercentage.textContent = '100%';
            if (loaderBar) {
              loaderBar.style.setProperty('--progress', '100%');
            }

            // Clear interval
            if (loader.dataset.interval) {
              clearInterval(loader.dataset.interval);
            }

            setTimeout(() => {
              loader.style.display = 'none';
              loaderPercentage.textContent = '0%';
              if (loaderBar) {
                loaderBar.style.setProperty('--progress', '0%');
              }
            }, 500);
          }

          async function performCryptOperation(action) {
            const text = cryptText.value.trim();
            if (!text) {
              showModalMessage('Crypto', 'Please enter text to ' + action);
              return;
            }

            const module = document.querySelector('select[name="crypt_module"]').value;
            const formData = new FormData();
            formData.append('text', text);
            formData.append('action', action);
            formData.append('module', module);

            try {
              showCryptLoader(action);
              const response = await fetch('/crypt', {
                method: 'POST',
                body: formData
              });

              if (!response.ok) {
                const errorText = await response.text();
                throw new Error(errorText || 'Operation failed');
              }

              const result = await response.text();
              cryptText.value = text; // Keep original text in input
              cryptResult.value = result; // Show result in result box

              // Note: Not saving result to localStorage for security reasons
              console.log('Encryption/decryption completed (result not saved to localStorage)');


            } catch (err) {
              // Show error in UI
              const errorMsg = document.createElement('div');
              errorMsg.className = 'text-sm text-red-600 mt-2';
              errorMsg.textContent = err.message;
              cryptText.parentNode.appendChild(errorMsg);
              setTimeout(() => errorMsg.remove(), 5000);

              // Clear result area
              cryptResult.value = '';
            } finally {
              hideCryptLoader();
            }
          }

          // Copy result to clipboard (new icon button)
          document.getElementById('copyResultBtn').addEventListener('click', async () => {
            try {
              await navigator.clipboard.writeText(cryptResult.value);
            } catch (err) {
              showModalMessage('Clipboard', 'Failed to copy: ' + err.message);
            }
          });

          // Paste into input (new icon button)
          document.getElementById('pasteInputBtn').addEventListener('click', async () => {
            try {
              const text = await navigator.clipboard.readText();
              cryptText.value = text;
            } catch (err) {
              showModalMessage('Clipboard', 'Failed to paste: ' + err.message);
            }
          });



          encryptBtn.addEventListener('click', () => performCryptOperation('encrypt'));
          decryptBtn.addEventListener('click', () => performCryptOperation('decrypt'));

          // Show/hide loader functions
          function showLoader() {
            const loader = document.getElementById('loader');
            const loaderText = document.getElementById('loader-text');
            const loaderPercentage = document.getElementById('loader-percentage');

            loader.style.display = 'flex';
            loader.classList.remove('download-mode');
            loader.onclick = null;

                      // Build neutral, context-aware steps (no artificial slowdowns)
           const pathLc = (s3Input.value || '').toLowerCase();
           const steps = [];
           steps.push({ text: 'READING FILE', progress: 35 });
           if (pathLc.endsWith('.gz')) steps.push({ text: 'DECOMPRESSING', progress: 65 });
           if (/\.(csv|json|jsonl)$/i.test(pathLc)) steps.push({ text: 'PARSING CONTENT', progress: 85 });
           steps.push({ text: 'OPENING EDITOR', progress: 100 });

            let step = 0;
            let currentProgress = 0;

            const interval = setInterval(() => {
              if (step < steps.length) {
                loaderText.textContent = steps[step].text;

                // Animate progress to target
                const targetProgress = steps[step].progress;
                const progressInterval = setInterval(() => {
                  currentProgress += 2;
                  if (currentProgress >= targetProgress) {
                    currentProgress = targetProgress;
                    clearInterval(progressInterval);
                  }
                  loaderPercentage.textContent = currentProgress + '%';
                  document.querySelector('.loader').style.setProperty('--progress', currentProgress + '%');
                }, 50);

                step++;
              }
            }, 800);
          }

          function showDownloadLoader() {
            const loader = document.getElementById('loader');
            const loaderText = document.getElementById('loader-text');
            const loaderPercentage = document.getElementById('loader-percentage');

            loader.style.display = 'flex';

                      // Download steps: neutral and fast
           const pathLc = (s3Input.value || '').toLowerCase();
           const steps = [];
           steps.push({ text: 'READING FILE', progress: 40 });
           if (pathLc.endsWith('.gz')) steps.push({ text: 'DECOMPRESSING', progress: 70 });
           steps.push({ text: 'PREPARING DOWNLOAD', progress: 90 });
           steps.push({ text: 'SENDING FILE', progress: 100 });

            let step = 0;
            let currentProgress = 0;

            const interval = setInterval(() => {
              if (step < steps.length) {
                loaderText.textContent = steps[step].text;

                // Animate progress to target
                const targetProgress = steps[step].progress;
                            const start = currentProgress;
             const delta = targetProgress - start;
             const duration = 250; // ~0.25s per step
             const startTime = performance.now();
             function tick(now){
               const t = Math.min(1, (now - startTime) / duration);
               currentProgress = Math.round(start + delta * t);
               loaderPercentage.textContent = currentProgress + '%';
               document.querySelector('.loader').style.setProperty('--progress', currentProgress + '%');
               if (t < 1) requestAnimationFrame(tick);
             }
             requestAnimationFrame(tick);

                step++;

                // If this is the last step (COMPLETED), hide loader after delay
                if (step === steps.length) {
                  setTimeout(() => {
                    loader.style.display = 'none';
                    loaderPercentage.textContent = '0%';
                    document.querySelector('.loader').style.setProperty('--progress', '0%');
                  }, 1500);
                }
              }
            }, 600);
          }

          function showSaveLoader() {
            const loader = document.getElementById('loader');
            const loaderText = document.getElementById('loader-text');
            const loaderPercentage = document.getElementById('loader-percentage');

            loader.style.display = 'flex';

            // Save loading steps with percentage
            const steps = [
              { text: 'PREPARING DATA', progress: 20 },
              { text: 'VALIDATING CHANGES', progress: 40 },
              { text: 'ENCRYPTING', progress: 60 },
              { text: 'UPLOADING TO S3', progress: 80 },
              { text: 'SAVED', progress: 100 }
            ];

            let step = 0;
            let currentProgress = 0;

            const interval = setInterval(() => {
              if (step < steps.length) {
                loaderText.textContent = steps[step].text;

                // Animate progress to target
                const targetProgress = steps[step].progress;
                const progressInterval = setInterval(() => {
                  currentProgress += 2;
                  if (currentProgress >= targetProgress) {
                    currentProgress = targetProgress;
                    clearInterval(progressInterval);
                  }
                  loaderPercentage.textContent = currentProgress + '%';
                  document.querySelector('.loader').style.setProperty('--progress', currentProgress + '%');
                }, 50);

                step++;

                // If this is the last step (SAVED), hide loader after delay
                if (step === steps.length) {
                  setTimeout(() => {
                    loader.style.display = 'none';
                    loaderPercentage.textContent = '0%';
                    document.querySelector('.loader').style.setProperty('--progress', '0%');
                  }, 1500);
                }
              }
            }, 700);
          }

          function showEncryptUploadLoader() {
            const loader = document.getElementById('loader');
            const loaderText = document.getElementById('loader-text');
            const loaderPercentage = document.getElementById('loader-percentage');

            loader.style.display = 'flex';

            // Encrypt upload loading steps with percentage
            const steps = [
              { text: 'READING FILE', progress: 20 },
              { text: 'DETECTING FORMAT', progress: 40 },
              { text: 'ENCRYPTING CONTENT', progress: 60 },
              { text: 'UPLOADING TO S3', progress: 80 },
              { text: 'COMPLETED', progress: 100 }
            ];

            let step = 0;
            let currentProgress = 0;

            const interval = setInterval(() => {
              if (step < steps.length) {
                loaderText.textContent = steps[step].text;

                // Animate progress to target
                const targetProgress = steps[step].progress;
                            const start = currentProgress;
             const delta = targetProgress - start;
             const duration = 200; // fast animation per step
             const startTime = performance.now();
             function tick(now){
               const t = Math.min(1, (now - startTime) / duration);
               currentProgress = Math.round(start + delta * t);
               loaderPercentage.textContent = currentProgress + '%';
               document.querySelector('.loader').style.setProperty('--progress', currentProgress + '%');
               if (t < 1) requestAnimationFrame(tick);
             }
             requestAnimationFrame(tick);

                step++;

                // If this is the last step (COMPLETED), hide loader after delay
                if (step === steps.length) {
                  setTimeout(() => {
                    loader.style.display = 'none';
                    loaderPercentage.textContent = '0%';
                    document.querySelector('.loader').style.setProperty('--progress', '0%');
                  }, 1500);
                }
              }
            }, 700);
          }

          // Records per page functionality
          function updateRecordsPerPage() {
            let v = recordsPerPage.innerText.trim();
            if (!/^\d+$/.test(v) || parseInt(v) < 1) {
              v = '20';
            }
            recordsPerPage.innerText = v;
            recordsPerPageInput.value = v;  // Sync with hidden input
            localStorage.setItem('recordsPerPage', v);
          }

          // Load saved records per page
          const savedRecordsPerPage = localStorage.getItem('recordsPerPage') || '20';
          recordsPerPage.innerText = savedRecordsPerPage;
          recordsPerPageInput.value = savedRecordsPerPage;  // Sync with hidden input

          recordsPerPage.addEventListener('blur', updateRecordsPerPage);
          recordsPerPage.addEventListener('keydown', function(e) {
            if (e.key === 'Enter') {
              e.preventDefault();
              this.blur();
            }
          });

          // Update hidden input when edit buttons are clicked
          editS3Btn.addEventListener('click', updateRecordsPerPage);
          editLocalBtn.addEventListener('click', updateRecordsPerPage);

          // Initialize
          toggleButtons();
          updateLimit();

          // Restore form state from session if coming from encrypt-upload
          function restoreFormState() {
            // This will be called after page load to restore any preserved state
            console.log('Restoring form state...');

            // The S3 path should already be restored by the server via last_path
            // But we can add additional restoration logic here if needed

            // Update button states
            toggleButtons();
          }

          // Call restore function after page load
          document.addEventListener('DOMContentLoaded', restoreFormState);

          // Ensure orig_s3_path is always synced with s3_path
          s3Input.addEventListener('input', () => {
            document.getElementById('orig_s3_path').value = s3Input.value;
          });

          // S3 Browser functionality with Per-Bucket Path Memory
          const modal = document.getElementById('s3Modal');
          const s3BrowseBtns = document.querySelectorAll('.s3BrowseBtn, #s3BrowseBtn');
          const closeBtn = document.getElementsByClassName('close')[0];
          const cancelBtn = document.getElementById('cancelBrowseBtn');
          const selectBtn = document.getElementById('selectFileBtn');
          const bucketSelect = document.getElementById('bucketSelect');
          const browserContent = document.getElementById('browserContent');
          const breadcrumb = document.getElementById('breadcrumb');
          const browserSearch = document.getElementById('browserSearch');
          const useFolderBtn = document.getElementById('useFolderBtn');
          const getAllBtn = document.getElementById('getAllBtn');

          let currentPath = '';
          let selectedFile = null;
          let allItems = [];
          let isLoading = false;
          let prefetchQueue = [];
          let cacheStatus = {};
          let activeS3Input = null;

          // Per-bucket path memory
          const BUCKET_PATHS_KEY = 's3BrowserBucketPaths';

          // Get saved paths for all buckets
          function getSavedBucketPaths() {
             const saved = localStorage.getItem(BUCKET_PATHS_KEY);
             return saved ? JSON.parse(saved) : {};
          }

          // Save path for a specific bucket
          function saveBucketPath(bucket, path) {
             const paths = getSavedBucketPaths();
             paths[bucket] = path;
             localStorage.setItem(BUCKET_PATHS_KEY, JSON.stringify(paths));
          }

          // Get last path for a specific bucket
          function getLastPathForBucket(bucket) {
             const paths = getSavedBucketPaths();
             return paths[bucket] || bucket;
          }

          // Open modal handler for all S3 browse buttons
          s3BrowseBtns.forEach(btn => {
             btn.addEventListener('click', function() {
                // Find the closest s3_path input to this button
                const container = this.closest('.flex-1');
                if (container) {
                   activeS3Input = container.querySelector('#s3_path');
                } else {
                   // Fallback to the main s3_path input
                   activeS3Input = document.getElementById('s3_path');
                }

                modal.style.display = 'flex';

                // Check if we have a last used bucket
                const lastBucket = localStorage.getItem('lastS3Bucket');
                if (lastBucket && bucketSelect.querySelector(`option[value="${lastBucket}"]`)) {
                   bucketSelect.value = lastBucket;
                   bucketSelect.dispatchEvent(new Event('change'));
                }
             });
          });

          // Close handlers
          closeBtn.onclick = function() {
             modal.style.display = 'none';
          }

          cancelBtn.onclick = function() {
             modal.style.display = 'none';
          }

          window.onclick = function(event) {
             if (event.target == modal) {
                modal.style.display = 'none';
             }
          }

          // Bucket selection handler
          bucketSelect.onchange = function() {
             if (this.value) {
                const bucket = this.value;

                // Save last used bucket
                localStorage.setItem('lastS3Bucket', bucket);

                // Get last path for this specific bucket
                const lastPath = getLastPathForBucket(bucket);
                currentPath = lastPath;

                // Start smart caching for this bucket
                startSmartCaching(bucket);

                // Navigate to the saved path for this bucket
                navigateToPath(lastPath);
             }
          }

          // Smart refresh button handler
          document.getElementById('refreshBucketBtn').onclick = function() {
             if (!currentPath) {
                return;
             }

             const refreshBtn = this;
             const originalContent = refreshBtn.innerHTML;

             // Show loading state
             refreshBtn.disabled = true;
             refreshBtn.innerHTML = '⏳ Refreshing...';

             // Refresh only the current path
             refreshCurrentPath()
                .then(() => {
                   // Show success briefly
                   refreshBtn.innerHTML = '✅ Updated!';
                   setTimeout(() => {
                      refreshBtn.innerHTML = originalContent;
                      refreshBtn.disabled = false;
                   }, 1500);
                })
                .catch(error => {
                   console.error('Refresh error:', error);
                   refreshBtn.innerHTML = '❌ Error';
                   setTimeout(() => {
                      refreshBtn.innerHTML = originalContent;
                      refreshBtn.disabled = false;
                   }, 1500);
                });
          }

                    // Debounce browse for typing/navigations
           function debounce(fn, ms){ let t; return (...args)=>{ clearTimeout(t); t=setTimeout(()=>fn.apply(null,args), ms); }; }
           const debouncedLoad = debounce((p)=>{ browseSeq++; loadS3Content(p, browseSeq); }, 200);

           // Navigate to a path
           function navigateToPath(path) {
             currentPath = path.replace(/\/+$/, '');

             // Save the path for the current bucket
             const currentBucket = currentPath.split('/')[0];
             saveBucketPath(currentBucket, currentPath);

             updateBreadcrumb();
             debouncedLoad(currentPath);
           }

          // Track latest browse request to avoid stale renders
           let browseSeq = 0;
           let browseController = null;

           // Load S3 content for a path (seq guards rendering)
           function loadS3Content(path, seq, forceRefresh = false) {
             // do not early-return; allow newer requests to supersede older ones
             isLoading = true;
             browserContent.innerHTML = '<div class="loading-spinner">Loading...</div>';
             selectedFile = null;
             selectBtn.disabled = true;

                                     // Abort any in-flight browse
            try { if (browseController) browseController.abort(); } catch(e) {}
            browseController = new AbortController();
            return fetch('/browse-s3', {
               method: 'POST',
               headers: {
                  'Content-Type': 'application/json',
               },
               body: JSON.stringify({
                  path: path,
                  module: document.querySelector('select[name="module"]').value,
                  force_refresh: forceRefresh
               }),
               signal: browseController.signal
            })
             .then(response => response.json())
             .then(data => {
                // Ignore stale response if a newer request was fired
                if (seq !== browseSeq) { return Promise.reject('Stale browse response'); }
                isLoading = false;

                if (data.error) {
                   browserContent.innerHTML = '<div style="color: red; padding: 20px;">Error: ' + data.error + '</div>';
                   return Promise.reject(data.error);
                }

                // Display items
                displayItems(data.items);

                // Show cache indicator
                if (data.cached) {
                   showCacheIndicator(data.cache_age);
                }

                // Prefetch subfolders and likely siblings in background
                try { prefetchSubfolders(path, data.items || []); } catch(e) {}

                return data;
             })
             .catch(error => {
                // Ignore aborts from cancelled browses
                if (String(error).includes('AbortError') || String(error).includes('aborted')) { return; }
                isLoading = false;
                browserContent.innerHTML = '<div style="color: red; padding: 20px;">Error loading content: ' + error + '</div>';

                // If loading fails, try parent directory
                const lastSlash = path.lastIndexOf('/');
                if (lastSlash > 0) {
                   const parentPath = path.substring(0, lastSlash);
                   console.log('Failed to load path, trying parent:', parentPath);

                   // Update saved path to parent
                   const bucket = path.split('/')[0];
                   saveBucketPath(bucket, parentPath);

                   // Try loading parent
                   setTimeout(() => {
                      if (!isLoading) {
                         navigateToPath(parentPath);
                      }
                   }, 500);
                }

                throw error;
             });
          }

          // Refresh only the current path
          function refreshCurrentPath() {
             return fetch('/refresh-s3-path', {
                method: 'POST',
                headers: {
                   'Content-Type': 'application/json',
                },
                body: JSON.stringify({
                   path: currentPath,
                   module: document.querySelector('select[name="module"]').value
                })
             })
             .then(response => response.json())
             .then(data => {
                if (data.error) {
                   throw new Error(data.error);
                }

                // Display refreshed items
                displayItems(data.items);

                // Flash effect to show update
                browserContent.style.opacity = '0.5';
                setTimeout(() => {
                   browserContent.style.opacity = '1';
                }, 200);

                return data;
             });
          }

          // Display items in the browser
          function displayItems(items) {
             browserContent.innerHTML = '';
             allItems = items || [];

             // Sort: folders first, then files
             allItems.sort((a, b) => {
                if (a.type === 'folder' && b.type === 'file') return -1;
                if (a.type === 'file' && b.type === 'folder') return 1;
                return a.name.localeCompare(b.name);
             });

              // Enable folder actions when a bucket is selected
              const canUseFolder = !!currentPath && currentPath.split('/').length >= 1;
              if (useFolderBtn) useFolderBtn.disabled = !canUseFolder;
              if (getAllBtn) getAllBtn.disabled = !canUseFolder;

              allItems.forEach(item => {
                 const div = document.createElement('div');
                 div.className = 'browser-item';

                // Add modified time for files
                let extraInfo = '';
                if (item.size) {
                   extraInfo = `<span style="color: #999; margin-left: auto;">${item.size}</span>`;
                }
                if (item.modified) {
                   const modDate = new Date(item.modified);
                   const timeAgo = getTimeAgo(modDate);
                   extraInfo += `<span style="color: #999; margin-left: 10px; font-size: 0.85em;">${timeAgo}</span>`;
                }

                const canDelete = item.type === 'file';
                const rightHtml = `${extraInfo}${canDelete ? ' <button class="file-del" title="Delete" aria-label="Delete" style="background:none;border:none;cursor:pointer;font-size:16px;">🗑️</button>' : ''}`;
                div.innerHTML = `
                   <span>${item.type === 'folder' ? '📁' : '📄'}</span>
                   <span>${item.name}</span>
                   ${rightHtml}
                `;

                div.onclick = function(e) {
                   if (e && e.target && e.target.classList && e.target.classList.contains('file-del')) return;
                   if (item.type === 'folder') {
                      // Clear search when navigating to a new folder
                      browserSearch.value = '';
                      navigateToPath((currentPath.replace(/\/+$/, '')) + '/' + item.name);
                   } else {
                      // Select file
                      document.querySelectorAll('.browser-item').forEach(el => {
                         el.classList.remove('selected');
                      });
                      div.classList.add('selected');
                      selectedFile = currentPath + '/' + item.name;
                      selectBtn.disabled = false;
                   }
                };

                // Hook delete icon (no confirmation, delete then refresh)
                if (canDelete) {
                   const delBtn = div.querySelector('.file-del');
                   if (delBtn) {
                      delBtn.addEventListener('click', function(ev) {
                         ev.stopPropagation();
                         const full = currentPath + '/' + item.name;
                         const bucket = full.split('/')[0];
                         const key = full.substring(bucket.length + 1);
                         fetch('/delete-s3', {
                           method: 'POST',
                           headers: { 'Content-Type': 'application/json' },
                           body: JSON.stringify({ bucket, key })
                         }).then(r => r.json()).then(data => {
                           if (data && data.success) {
                             loadS3Content(currentPath, true);
                           }
                         }).catch(() => {});
                      });
                   }
                }
              browserContent.appendChild(div);
            });

            if (allItems.length === 0) {
               browserContent.innerHTML = '<div style="padding: 20px; color: #666;">No files or folders found</div>';
            }

             // Update search
             updateSearch();
          }

          // Update breadcrumb navigation
          function updateBreadcrumb() {
             breadcrumb.innerHTML = '';
             const parts = currentPath.split('/');

             parts.forEach((part, index) => {
                if (part) {
                   const span = document.createElement('span');
                   span.className = 'breadcrumb-item';
                   span.textContent = part;
                   span.onclick = function() {
                      const newPath = parts.slice(0, index + 1).join('/').replace(/\/+$/, '');
                      navigateToPath(newPath);
                   };

                   breadcrumb.appendChild(span);

                                        if (index < parts.length - 1) {
                       const chevron = document.createElement('span');
                       chevron.innerHTML = '&#x276F;'; // Unicode right-pointing chevron
                       chevron.style.cssText = 'margin: 0 3px; color: #666; font-size: 12px; font-weight: bold;';
                       breadcrumb.appendChild(chevron);
                     }
                }
             });
          }

          // Show cache indicator
          function showCacheIndicator(cacheAge) {
             const indicator = document.createElement('span');
             indicator.style.cssText = 'position: absolute; top: 10px; right: 10px; font-size: 1.2em; color: #666;';
             indicator.textContent = '';

             browserContent.style.position = 'relative';
             browserContent.appendChild(indicator);

             setTimeout(() => {
                if (indicator.parentNode) {
                   indicator.remove();
                }
             }, 3000);
          }

          // Prefetch subfolders
          function prefetchSubfolders(currentPath, items) {
             const folders = items.filter(item => item.type === 'folder').slice(0, 5);
             const paths = folders.map(folder => currentPath + '/' + folder.name);

             if (paths.length === 0) return;

             // Add parent path too
             const parentPath = currentPath.substring(0, currentPath.lastIndexOf('/'));
             if (parentPath) {
                paths.unshift(parentPath);
             }

             fetch('/prefetch-s3-paths', {
                method: 'POST',
                headers: {
                   'Content-Type': 'application/json',
                },
                body: JSON.stringify({
                   paths: paths,
                   module: document.querySelector('select[name="module"]').value
                })
             })
             .then(response => response.json())
             .then(data => {
                console.log('Prefetched paths:', data);
             })
             .catch(error => {
                console.error('Prefetch error:', error);
             });
          }

          // Start smart caching
          function startSmartCaching(bucket) {
             if (cacheStatus[bucket] === 'caching') return;

             cacheStatus[bucket] = 'caching';

             // Get the last path for this bucket to use as initial path
             const lastPath = getLastPathForBucket(bucket);

             fetch('/cache-s3-bucket-smart', {
                method: 'POST',
                headers: {
                   'Content-Type': 'application/json',
                },
                body: JSON.stringify({
                   bucket: bucket,
                   initial_path: lastPath,
                   module: document.querySelector('select[name="module"]').value
                })
             })
             .then(response => response.json())
             .then(data => {
                console.log('Smart caching started for bucket:', bucket);
             })
             .catch(error => {
                console.error('Cache error:', error);
                cacheStatus[bucket] = 'error';
             });
          }

          // Search functionality with debouncing
          let searchTimeout;

          browserSearch.oninput = function() {
             console.log('Search input detected:', browserSearch.value);
             // Hide content while typing
             browserContent.style.display = 'none';

             // Clear any existing timeout
             if (searchTimeout) {
                clearTimeout(searchTimeout);
             }
             // Wait 500ms after last keystroke before showing filtered content
             searchTimeout = setTimeout(function() {
                console.log('Showing filtered content for:', browserSearch.value);
                browserContent.style.display = 'block';
                updateSearch();
             }, 500);
          }

          function updateSearch() {
             const searchTerm = browserSearch.value.toLowerCase().trim();
             const items = document.querySelectorAll('.browser-item');
             console.log('Search term:', searchTerm, 'Items found:', items.length);

             if (!searchTerm) {
                items.forEach(item => {
                   item.style.display = 'flex';
                });
                console.log('Cleared search - showing all items');
                return;
             }

             let visibleCount = 0;
             items.forEach(item => {
                const nameSpan = item.querySelector('span:nth-child(2)');
                const fileName = nameSpan ? nameSpan.textContent.toLowerCase() : '';

                // Search in filename first, then in all text
                if (fileName.includes(searchTerm) || item.textContent.toLowerCase().includes(searchTerm)) {
                   item.style.display = 'flex';
                   visibleCount++;
                } else {
                   item.style.display = 'none';
                }
             });
             console.log('Search completed - visible items:', visibleCount, 'for term:', searchTerm);
          }

           // Select file handler
           selectBtn.onclick = function() {
              if (selectedFile) {
                 // Use the active S3 input that opened the modal
                 if (activeS3Input) {
                    activeS3Input.value = 's3://' + selectedFile;
                    // Trigger change event to update any dependent elements
                    activeS3Input.dispatchEvent(new Event('change'));
                 } else {
                    // Fallback to main s3_path
                    const mainS3Input = document.getElementById('s3_path');
                    if (mainS3Input) {
                       mainS3Input.value = 's3://' + selectedFile;
                       mainS3Input.dispatchEvent(new Event('change'));
                    }
                 }
                 modal.style.display = 'none';

                 // If we're on the home page with toggleButtons function
                 if (typeof toggleButtons === 'function') {
                    toggleButtons();
                 }

                 // Save path to session if the function exists
                 if (typeof savePathToSession === 'function' && activeS3Input) {
                    savePathToSession(activeS3Input.value);
                 }
              }
           }

           // Use This Folder handler (ensures trailing slash)
           if (useFolderBtn) {
             useFolderBtn.onclick = function() {
               if (!currentPath) return;
               let folderPath = currentPath;
               if (!/\/$/.test(folderPath)) folderPath += '/';

               // Use the active S3 input that opened the modal
               if (activeS3Input) {
                  activeS3Input.value = 's3://' + folderPath;
                  // Trigger change event to update any dependent elements
                  activeS3Input.dispatchEvent(new Event('change'));
               } else {
                  // Fallback to main s3_path
                  const mainS3Input = document.getElementById('s3_path');
                  if (mainS3Input) {
                     mainS3Input.value = 's3://' + folderPath;
                     mainS3Input.dispatchEvent(new Event('change'));
                  }
               }
               modal.style.display = 'none';

               // If we're on the home page with toggleButtons function
               if (typeof toggleButtons === 'function') {
                  toggleButtons();
               }

               // Save path to session if the function exists
               if (typeof savePathToSession === 'function' && activeS3Input) {
                  savePathToSession(activeS3Input.value);
               }
             }
           }

           // Start Extract
           async function startGetAll() {
             if (!currentPath) return;
             let folderPath = currentPath;
             if (!/\/$/.test(folderPath)) folderPath += '/';
             const moduleVal = document.querySelector('select[name="module"]').value;
             const resp = await fetch('/download-all', {
               method: 'POST',
               headers: { 'Content-Type': 'application/json' },
               body: JSON.stringify({ path: 's3://' + folderPath, module: moduleVal })
             });
             const data = await resp.json();
             if (!resp.ok || data.status !== 'started') {
               showModalMessage('Get All', data && data.message ? data.message : 'Failed to start download');
               return;
             }
                          const jobId = data.job_id;
              // Init extracted files list for final modal
              window.__extractedFiles = [];
                          showBatchDownloadLoader(jobId);
             // Ensure consistent loader sizing
             const bar = document.querySelector('.loader'); if (bar) { bar.style.height = '5px'; }
             document.getElementById('loader-text').textContent = 'EXTRACTING';
           }

              if (getAllBtn) {
              // Remove in-modal Get All per request
              try { getAllBtn.remove(); } catch(e) { getAllBtn.style.display = 'none'; getAllBtn.disabled = true; }
            }

           // Loader and polling for batch download
           function showBatchDownloadLoader(jobId) {
             const loader = document.getElementById('loader');
             const loaderText = document.getElementById('loader-text');
             const loaderPercentage = document.getElementById('loader-percentage');
             loader.style.display = 'flex';
             loader.classList.add('download-mode');
             loader.onclick = null;

             function updateUI(status) {
               const total = status.total || 0;
               const done = status.done || 0;
               const saved = status.saved || 0;
               const current = status.current_key || '';
               // Two-line label with smaller key line
               const line1 = `DOWNLOADING ${saved} of ${total}`;
               const line2 = current ? `<div style="font-size: 0.8em; opacity: 0.9; margin-top: 2px;">${current}</div>` : '';
               loaderText.innerHTML = `${line1}${line2 ? '<br/>' + line2 : ''}`;
               loaderPercentage.textContent = `${status.percent || 0}%`;
               document.querySelector('.loader').style.setProperty('--progress', (status.percent || 0) + '%');
             }

             let stopped = false;
             async function poll() {
               if (stopped) return;
               try {
                 const res = await fetch('/download-all-status', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ job_id: jobId })});
                 const data = await res.json();
                 if (!res.ok) throw new Error(data && data.message ? data.message : 'Status error');
                 updateUI(data);
                 // Accumulate saved files as we go (best-effort: push last_saved if increased)
                 if (data.last_saved && Array.isArray(window.__extractedFiles)) {
                   const arr = window.__extractedFiles;
                   if (arr.length === 0 || arr[arr.length - 1] !== data.last_saved) {
                     arr.push(data.last_saved);
                   }
                 }
                 if (data.status === 'completed' || data.status === 'error') {
                   stopped = true;
                   setTimeout(() => { loader.style.display = 'none'; }, 800);
                   const errors = data.error_count || (data.errors ? data.errors.length : 0) || 0;
                   const summaryTitle = 'Extract Summary';
                   // Build a pretty scrollable list of all saved files
                   const files = Array.isArray(data.saved_files) && data.saved_files.length ? data.saved_files : (window.__extractedFiles || []);
                   const listItems = files.map(k => `<li class=\"workbench-list-item\" style=\"padding:6px 8px;border-bottom:1px solid #e5e7eb;\">${k}</li>`).join('');
                   const listHtml = `<div class=\"workbench-summary\" style=\"text-align:left\">Downloaded ${data.folder_count || 0} folders, ${data.saved || 0} files Total<br/>${errors} error${errors===1?'':'s'}<br/><div class=\"workbench-scroll\" style=\"margin-top:10px;border:1px solid #e5e7eb;max-height:50vh;overflow:auto;border-radius:0\"><ul style=\"list-style:none;margin:0;padding:0\">${listItems}</ul></div></div>`;
                   showModalMessage(summaryTitle, listHtml);
                   return;
                 } else {
                   // update message with current saving file
                   const cur = data.current_key ? data.current_key : '';
                   const line1 = `DOWNLOADING ${data.saved || 0} of ${data.total || 0}`;
                   const line2 = cur ? `<div style="font-size: 0.8em; opacity: 0.9; margin-top: 2px;">${cur}</div>` : '';
                   loaderText.innerHTML = `${line1}${line2 ? '<br/>' + line2 : ''}`;
                 }
               } catch (e) {
                 console.error('Poll error', e);
               }
               setTimeout(poll, 800);
             }
             poll();
           }

          // Utility function to get relative time
          function getTimeAgo(date) {
             const seconds = Math.floor((new Date() - date) / 1000);

             if (seconds < 60) return 'just now';
             if (seconds < 3600) return Math.floor(seconds / 60) + 'm ago';
             if (seconds < 86400) return Math.floor(seconds / 3600) + 'h ago';
             if (seconds < 604800) return Math.floor(seconds / 86400) + 'd ago';

             return date.toLocaleDateString();
          }

          // Save path to session
          function savePathToSession(path) {
             if (path.toLowerCase().startsWith('s3://')) {
                fetch('/set-path', {
                   method: 'POST',
                   headers: {
                      'Content-Type': 'application/json',
                   },
                   body: JSON.stringify({path: path})
                });
             }
          }

          // Keyboard shortcuts
          document.addEventListener('keydown', function(e) {
             if (modal.style.display === 'flex') {
                if (e.key === 'Escape') {
                   modal.style.display = 'none';
                } else if (e.key === 'F5' || (e.ctrlKey && e.key === 'r')) {
                   e.preventDefault();
                   document.getElementById('refreshBucketBtn').click();
                }
             }
          });

          // Auto-save last module selection
          const moduleSelect = document.querySelector('select[name="module"]');
          if (moduleSelect) {
             // Load saved module
             const savedModule = localStorage.getItem('lastS3Module');
             if (savedModule) {
                moduleSelect.value = savedModule;
             }

             // Save on change
             moduleSelect.addEventListener('change', function() {
                localStorage.setItem('lastS3Module', this.value);
             });
          }

          // Debug: Show saved paths
          console.log('Saved bucket paths:', getSavedBucketPaths());
      </script>
      {{ s3_browser_styles|safe }}
      {{ s3_browser_modal|safe }}
      {{ s3_browser_script|safe }}
   </body>
</html>
"""

CSV_EDIT_HTML = r"""
<!doctype html>
<html>
   <head>
      <title>Sequoia WorkBench</title>
      <link rel="icon" href="https://www.sequoia.com/wp-content/uploads/2020/03/sequoia-symbol.png" />
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

         // Module change function
         function updateModule(module) {
         console.log(`Module changed to: ${module}`);

         // Update the hidden form field
         const moduleField = document.querySelector('input[name="module"]');
         if (moduleField) {
         moduleField.value = module;
         }

         // Save to session
         fetch('/set-module', {
         method: 'POST',
         headers: {
           'Content-Type': 'application/json',
         },
         body: JSON.stringify({module: module})
         });
         }
      </script>
      <!-- Add padding container -->
      <div class="w-full min-h-screen main-container theme-transition p-8 csv-edit-page">
         <!-- CSV EDIT PAGE HEADER -->
         <!-- Header: only logo is clickable -->
         <div class="flex items-center justify-between mb-6">
            <div class="flex items-center space-x-3">
               <a href="{{ url_for('home') }}">
                  <div class="flex items-center">
                     <img src="{{ logo }}" class="h-16 w-auto mr-1" alt="Logo" />
                     <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
                  </div>
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
                     <option value="pink">🌸  Pink</option>
                  </select>
               </div>
            </div>
         </div>
         <form
            id="save-form"
            method="post"
            action="{{ url_for('save') }}"
            onsubmit="return submitData(this)"
            class="space-y-4 w-full"
            >
            <!-- S3 Path & Controls -->
            <div class="flex items-center space-x-2 mb-4">
               <div class="flex-1 flex items-center space-x-2">
                  <button
                     type="button"
                     class="s3BrowseBtn btn btn-ghost btn-icon"
                     style="width:46px;height:46px;padding:0;font-size:18px;line-height:46px;display:inline-flex;align-items:center;justify-content:center;"
                     title="Browse S3"
                     >🪣️</button>
                  <input
                     type="text"
                     id="s3_path"
                     name="s3_path"
                     value="{{ s3_path }}"
                     class="flex-grow border px-4 py-2 text-base theme-transition"
                     style="height: 46px;"
                     onchange="savePathToSession(this.value)"
                     autocomplete="off"
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
               {% if decryption_module %}
               <div class="flex items-center space-x-2">
                  <span class="px-3 py-1 text-sm font-medium theme-transition module-badge">{{ decryption_module }}</span>
               </div>
               {% else %}
               <select id="module-select" name="module" class="border px-4 py-2 text-sm theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="updateModule(this.value)">
               <option value="dxp" {{ 'selected' if module == 'dxp' else '' }}>dxp</option>
               <option value="dap" {{ 'selected' if module == 'dap' else '' }}>dap</option>
               <option value="pa" {{ 'selected' if module == 'pa' else '' }}>pa</option>
               </select>
               {% endif %}
               <button id="csvDontEncryptToggleBtn"
                  type="button"
                  class="btn btn-ghost btn-icon"
                  title="Disable encryption for this save"
                  onclick="toggleCsvDontEncrypt(); return false;"
                  style="height: 46px; width: 46px;">
               🔓
               </button>
               <button
                  type="submit"
                  form="save-form"
                  class="btn btn-ghost"
                  title="Save changes"
                  style="height: 46px;">
               💾 Save
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
               <input type="hidden" name="orig_s3_path"      value="{{ s3_path }}" />
               <input type="hidden" name="detected_delimiter" value="{{ escaped_delimiter }}" />
            </div>
            <!-- Hidden state -->
            <input type="hidden" name="module"     value="{{ module }}" />
            <input type="hidden" name="decryption_module" value="{{ decryption_module or module }}" />
            <input type="hidden" name="file_type"  value="{{ file_type }}" />
            <input type="hidden" name="gzipped"    value="{{ gzipped }}" />
            <input type="hidden" name="page"       value="{{ page }}" />
            <input type="hidden" name="table_data" id="table_data" />
            <input type="hidden" name="all_edits" id="all_edits" />
            <input type="hidden" name="cache_key" value="{{ cache_key }}" />
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
                  <form method="post" action="{{ url_for('home') }}" class="inline-block" onsubmit="return true;">
                     <input type="hidden" name="action"            value="edit" />
                     <input type="hidden" name="s3_path"           value="{{ s3_path }}" />
                     <input type="hidden" name="orig_s3_path"      value="{{ s3_path }}" />
                     <input type="hidden" name="module"            value="{{ module }}" />
                     <input type="hidden" name="file_type"         value="{{ file_type }}" />
                     <input type="hidden" name="gzipped"           value="{{ gzipped }}" />
                     <input type="hidden" name="detected_delimiter" value="{{ escaped_delimiter }}" />
                     <input type="hidden" name="page"              value="{{ page - 1 }}" />
                     <input type="hidden" name="records_per_page"  value="{{ per_page }}" />
                     <input type="hidden" name="cache_key"         value="{{ cache_key }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">‹</button>
                  </form>
                  {% endif %}
                  {# First page if not in window #}
                  {% if start_page > 1 %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block" onsubmit="return true;">
                     <input type="hidden" name="action"            value="edit" />
                     <input type="hidden" name="s3_path"           value="{{ s3_path }}" />
                     <input type="hidden" name="orig_s3_path"      value="{{ s3_path }}" />
                     <input type="hidden" name="module"            value="{{ module }}" />
                     <input type="hidden" name="file_type"         value="{{ file_type }}" />
                     <input type="hidden" name="gzipped"           value="{{ gzipped }}" />
                     <input type="hidden" name="detected_delimiter" value="{{ escaped_delimiter }}" />
                     <input type="hidden" name="page"              value="1" />
                     <input type="hidden" name="records_per_page"  value="{{ per_page }}" />
                     <input type="hidden" name="cache_key"         value="{{ cache_key }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">1</button>
                  </form>
                  {% if start_page > 2 %}
                  <span class="px-2 text-gray-500 flex items-center" style="height: 46px;">…</span>
                  {% endif %}
                  {% endif %}
                  {# Page numbers in window #}
                  {% for p in range(start_page, end_page + 1) %}
                  {% if p == page %}
                  <span class="btn btn-ghost page-btn active" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center;">{{ p }}</span>
                  {% else %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block" onsubmit="return true;">
                     <input type="hidden" name="action"            value="edit" />
                     <input type="hidden" name="s3_path"           value="{{ s3_path }}" />
                     <input type="hidden" name="orig_s3_path"      value="{{ s3_path }}" />
                     <input type="hidden" name="module"            value="{{ module }}" />
                     <input type="hidden" name="file_type"         value="{{ file_type }}" />
                     <input type="hidden" name="gzipped"           value="{{ gzipped }}" />
                     <input type="hidden" name="detected_delimiter" value="{{ escaped_delimiter }}" />
                     <input type="hidden" name="page"              value="{{ p }}" />
                     <input type="hidden" name="records_per_page"  value="{{ per_page }}" />
                     <input type="hidden" name="cache_key"         value="{{ cache_key }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">{{ p }}</button>
                  </form>
                  {% endif %}
                  {% endfor %}
                  {# Last page if not in window #}
                  {% if end_page < page_count %}
                  {% if end_page < page_count - 1 %}
                  <span class="px-2 text-gray-500 flex items-center" style="height: 46px;">…</span>
                  {% endif %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block" onsubmit="return true;">
                     <input type="hidden" name="action"            value="edit" />
                     <input type="hidden" name="s3_path"           value="{{ s3_path }}" />
                     <input type="hidden" name="orig_s3_path"      value="{{ s3_path }}" />
                     <input type="hidden" name="module"            value="{{ module }}" />
                     <input type="hidden" name="file_type"         value="{{ file_type }}" />
                     <input type="hidden" name="gzipped"           value="{{ gzipped }}" />
                     <input type="hidden" name="detected_delimiter" value="{{ escaped_delimiter }}" />
                     <input type="hidden" name="page"              value="{{ page_count }}" />
                     <input type="hidden" name="records_per_page"  value="{{ per_page }}" />
                     <input type="hidden" name="cache_key"         value="{{ cache_key }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">{{ page_count }}</button>
                  </form>
                  {% endif %}
                  {# Next page #}
                  {% if page < page_count %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block" onsubmit="return true;">
                     <input type="hidden" name="action"            value="edit" />
                     <input type="hidden" name="s3_path"           value="{{ s3_path }}" />
                     <input type="hidden" name="orig_s3_path"      value="{{ s3_path }}" />
                     <input type="hidden" name="module"            value="{{ module }}" />
                     <input type="hidden" name="file_type"         value="{{ file_type }}" />
                     <input type="hidden" name="gzipped"           value="{{ gzipped }}" />
                     <input type="hidden" name="detected_delimiter" value="{{ escaped_delimiter }}" />
                     <input type="hidden" name="page"              value="{{ page + 1 }}" />
                     <input type="hidden" name="records_per_page"  value="{{ per_page }}" />
                     <input type="hidden" name="cache_key"         value="{{ cache_key }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">›</button>
                  </form>
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
      </div>
      <script>
         // Cache key for this file
         const cacheKey = "{{ cache_key }}";

         // Load existing edits from server-provided data
         const existingEdits = {{ edits_json | safe }};

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
                 // Shift+Enter moves up
                 if (rowIndex > 0) {
                   rows[rowIndex - 1].cells[cellIndex].focus();
                 }
               } else {
                 // Enter moves down
                 if (rowIndex < rows.length - 1) {
                   rows[rowIndex + 1].cells[cellIndex].focus();
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

         // Track cell edits
         document.getElementById('tableBody').addEventListener('input', function(e) {
           if (e.target.tagName === 'TD') {
             const row = e.target.parentElement.dataset.row;
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

         // Initialize edit count
         updateEditCount();

         // Save path to session when it changes (only for S3 paths)
         function savePathToSession(path) {
           if (path.toLowerCase().startsWith('s3://')) {
             fetch('/set-path', {
               method: 'POST',
               headers: {
                 'Content-Type': 'application/json',
               },
               body: JSON.stringify({path: path})
             });
           }
         }

         // Gather the edits into the hidden fields before saving
                  function showSaveLoaderAndRedirect() {
           // Prevent multiple loaders
           if (document.getElementById('csv-save-loader')) {
             return;
           }

           const currentTheme = document.body.className;
           let progressColor = '#6366f1'; // Primary indigo
           let backgroundColor = '#334155'; // Dark gray

           if (currentTheme.includes('pink-theme')) {
             progressColor = '#ec4899'; // Pink primary
             backgroundColor = '#fbcfe8'; // Light pink
           } else if (currentTheme.includes('white-theme')) {
             progressColor = '#6366f1'; // Primary indigo
             backgroundColor = '#e2e8f0'; // Light gray
           }

           const loader = document.createElement('div');
           loader.id = 'csv-save-loader';
           loader.style.cssText = `
         position: fixed;
         top: 0;
         left: 0;
         width: 100%;
         height: 100%;
         background: rgba(0, 0, 0, 0.3);
         backdrop-filter: blur(8px);
         -webkit-backdrop-filter: blur(8px);
         display: flex;
         justify-content: center;
         align-items: center;
         z-index: 9999;
         font-family: 'Inter', sans-serif;
           `;

           loader.innerHTML = `
             <div style="text-align: center;">
               <div id="save-loader-text" style="color: white; font-size: 18px; font-weight: 600; margin-bottom: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">PREPARING DATA</div>
               <div style="width: 800px; height: 5px; background-color: ${backgroundColor}; border-radius: 0px; overflow: hidden; position: relative; margin: 0 auto;">
                 <div id="save-progress-bar" style="position: absolute; top: 0; left: 0; width: 0%; height: 100%; background-color: ${progressColor}; transition: width 0.3s ease; border-radius: 0px;"></div>
               </div>
               <div style="font-size: 24px; font-weight: 800; color: white; margin-top: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;" id="save-progress-text">0%</div>
             </div>
           `;

           document.body.appendChild(loader);

           // Animate progress
           let progress = 0;
           const steps = [
             { text: 'PREPARING DATA', target: 20 },
             { text: 'VALIDATING CHANGES', target: 40 },
             { text: 'ENCRYPTING', target: 60 },
             { text: 'UPLOADING TO S3', target: 80 },
             { text: 'SAVED', target: 100 }
           ];

           let stepIndex = 0;
           const stepInterval = setInterval(() => {
             if (stepIndex < steps.length) {
               const step = steps[stepIndex];
               document.getElementById('save-loader-text').textContent = step.text;

               const progressInterval = setInterval(() => {
                 progress += 2;
                 if (progress >= step.target) {
                   progress = step.target;
                   clearInterval(progressInterval);
                 }
                 document.getElementById('save-progress-bar').style.width = progress + '%';
                 document.getElementById('save-progress-text').textContent = progress + '%';
               }, 50);

               stepIndex++;

               // If this is the last step (SAVED), redirect to home after delay
               if (stepIndex === steps.length) {
                 setTimeout(() => {
                   window.location.href = '/';
                 }, 1500);
               }
             }
           }, 700);
         }

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

           // Show save loader with redirect to home
           showSaveLoaderAndRedirect();

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
      </script>
      {{ s3_browser_styles|safe }}
      {{ s3_browser_modal|safe }}
      {{ s3_browser_script|safe }}
   </body>
</html>
"""

JSON_EDIT_HTML = r"""
<!doctype html>
<html>
   <head>
      <title>Sequoia WorkBench</title>
      <link rel="icon" href="https://www.sequoia.com/wp-content/uploads/2020/03/sequoia-symbol.png" />
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
      <link rel="preconnect" href="https://fonts.googleapis.com">
      <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
      <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&display=swap" rel="stylesheet">
      <link href="https://fonts.googleapis.com/css2?family=Ubuntu+Mono:wght@400;700&display=swap" rel="stylesheet">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/fira-code@5.0.18/400.css">
      <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fontsource/cascadia-code@5.0.7/400.css">
      <style>
         /* ==================== BASE STYLES ==================== */
         * { font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif !important; }
         /* ==================== DARK THEME ==================== */
         body.dark-theme { background-color: #1e293b !important; color: #e2e8f0 !important; }
         body.dark-theme input, body.dark-theme select, .dark-theme input, .dark-theme select { background-color: #334155 !important; color: #e2e8f0 !important; border-color: #475569 !important; }
         body.dark-theme input:focus, body.dark-theme select:focus, .dark-theme input:focus, .dark-theme select:focus { outline: none !important; border-color: #475569 !important; box-shadow: none !important; }
         .dark-theme #editor { border-color: #334155; }
         .dark-theme .btn-ghost { background-color: transparent !important; color: #94a3b8 !important; border-color: #475569 !important; }
         .dark-theme .btn-ghost:hover:not(:disabled) { background-color: #334155 !important; border-color: #64748b !important; }
         .dark-theme .module-badge { background-color: #374151 !important; color: #e0e7ff !important; border-color: #4b5563 !important; }
         .dark-theme .greeting-text { color: #94a3b8 !important; }
         .dark-theme .witty-message { color: #cbd5e1 !important; }
         .dark-theme #rawDontEncryptToggleBtn.selected { background-color: rgba(255, 255, 255, 0.1) !important; border-color: rgba(255, 255, 255, 0.2) !important; }
         .dark-theme #jsonDontEncryptToggleBtn.selected { background-color: rgba(255, 255, 255, 0.1) !important; border-color: rgba(255, 255, 255, 0.2) !important; }
         /* Dark theme JSON highlighting */
         .dark-theme .json-container { background-color: #1e293b; color: #e2e8f0; border: 1px solid #334155; border-radius: 0; padding: 1.5rem; box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1); }
         .dark-theme .json-key { color: #9cdcfe !important; font-weight: 500 !important; }
         .dark-theme .json-string { color: #ce9178 !important; font-weight: 500 !important; }
         .dark-theme .json-number { color: #b5cea8 !important; font-weight: 500 !important; }
         .dark-theme .json-boolean { color: #569cd6 !important; font-weight: 600 !important; }
         .dark-theme .json-null { color: #569cd6 !important; font-style: italic !important; font-weight: 500 !important; }
         .dark-theme .toggle { cursor: pointer; user-select: none; color: #e2e8f0 !important; font-weight: 500 !important; }
         .dark-theme .json-value { outline: none; padding: 2px 4px; border-radius: 0; }
         .dark-theme .json-value:hover { background-color: #334155; }
         .dark-theme .json-value:focus { background-color: #334155; border: 1px solid #6366f1; }
         .dark-theme .bracket { color: #ffd700 !important; font-weight: 600 !important; }
         .dark-theme .comma { color: #e2e8f0 !important; font-weight: 500 !important; }
         /* ==================== WHITE THEME ==================== */
         body.white-theme { background-color: #f1f5f9 !important; color: #1e293b !important; }
         body.white-theme input, body.white-theme select, .white-theme input, .white-theme select { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
         body.white-theme input:focus, body.white-theme select:focus, .white-theme input:focus, .white-theme select:focus { outline: none !important; border-color: #e2e8f0 !important; box-shadow: none !important; }
         .white-theme #editor { border-color: #e2e8f0; }
         .white-theme .btn-ghost { border-color: #e2e8f0 !important; color: #64748b !important; }
         .white-theme .btn-ghost:hover:not(:disabled) { background-color: #f1f5f9 !important; border-color: #cbd5e1 !important; }
         .white-theme .module-badge { background-color: #ffffff !important; color: #1e40af !important; border-color: #d1d5db !important; }
         .white-theme .greeting-text { color: #64748b !important; }
         .white-theme .witty-message { color: #64748b !important; }
         .white-theme .main-container { background-color: #f8fafc !important; color: #1e293b !important; border-radius: 0; }
         .white-theme #rawDontEncryptToggleBtn.selected { background-color: rgba(0, 0, 0, 0.05) !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         .white-theme #jsonDontEncryptToggleBtn.selected { background-color: rgba(0, 0, 0, 0.05) !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         /* White theme JSON highlighting */
         .white-theme .json-container { background-color: #f8fafc; color: #1e293b; border: 1px solid #e2e8f0; border-radius: 0; padding: 1.5rem; box-shadow: 0 1px 3px 0 rgba(0, 0, 0, 0.1); }
         .white-theme .json-key { color: #0066cc; font-weight: 500; }
         .white-theme .json-string { color: #22863a; font-weight: 500; }
         .white-theme .json-number { color: #e36209; font-weight: 500; }
         .white-theme .json-boolean { color: #6f42c1; font-weight: 600; }
         .white-theme .json-null { color: #6a737d; font-style: italic; font-weight: 500; }
         .white-theme .toggle { cursor: pointer; user-select: none; color: #1e293b; font-weight: 500; }
         .white-theme .json-value { outline: none; padding: 2px 4px; border-radius: 0; }
         .white-theme .json-value:hover { background-color: #f0f9ff; }
         .white-theme .json-value:focus { background-color: #f0f9ff; border: 1px solid #6366f1; }
         .white-theme .bracket { color: #d73a49; font-weight: 600; }
         .white-theme .comma { color: #1e293b; font-weight: 500; }
         /* ==================== PINK THEME ==================== */
         body.pink-theme { background-color: #fdf2f8 !important; color: #831843 !important; }
         body.pink-theme input, body.pink-theme select, .pink-theme input, .pink-theme select { background-color: #fce7f3 !important; color: #831843 !important; border-color: #fbcfe8 !important; }
         body.pink-theme input:focus, body.pink-theme select:focus, .pink-theme input:focus, .pink-theme select:focus { outline: none !important; border-color: #fbcfe8 !important; box-shadow: none !important; }
         .pink-theme #editor { border-color: #f9a8d4; }
         .pink-theme .btn-primary { background-color: #ec4899 !important; }
         .pink-theme .btn-primary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-success { background-color: #db2777 !important; }
         .pink-theme .btn-success:hover:not(:disabled) { background-color: #be185d !important; }
         .pink-theme .btn-secondary { background-color: #ec4899 !important; color: #ffffff !important; }
         .pink-theme .btn-secondary:hover:not(:disabled) { background-color: #db2777 !important; }
         .pink-theme .btn-ghost { color: #be185d !important; border-color: #fbcfe8 !important; }
         .pink-theme .btn-ghost:hover:not(:disabled) { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
         .pink-theme .module-badge { background-color: #fdf2f8 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         .pink-theme .greeting-text { color: #be185d !important; }
         .pink-theme .witty-message { color: #db2777 !important; }
         .pink-theme #rawDontEncryptToggleBtn.selected { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
         /* Big Time Display Styling */
         .big-time-display { display: flex !important; flex-direction: row !important; justify-content: flex-end !important; align-items: center !important; margin-bottom: 0.5rem !important; }
         .time-section { text-align: right; height: 46px !important; display: flex !important; flex-direction: column !important; justify-content: center !important; align-items: flex-end !important; } }
         .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; margin-bottom: 0.125rem !important; }
         .big-day-date { font-size: 0.875rem !important; font-weight: 500 !important; color: #94a3b8 !important; line-height: 1.2 !important; }
         .dark-theme .big-greeting { color: #94a3b8 !important; }
         .dark-theme .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; }
         .dark-theme .big-day-date { color: #94a3b8 !important; font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }
         .white-theme .big-greeting { color: #64748b !important; }
         .white-theme .big-time { color: #1e293b !important; font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
         .white-theme .big-day-date { color: #64748b !important; font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }
         .pink-theme .big-greeting { color: #be185d !important; }
         .pink-theme .big-time { color: #831843 !important; font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; }
         .pink-theme .big-day-date { color: #be185d !important; font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important; }
         /* CSV Edit specific time display fixes */
         .csv-edit-page .big-time-display { display: flex !important; flex-direction: row !important; justify-content: flex-end !important; align-items: center !important; margin-bottom: 0.5rem !important; }
         .csv-edit-page .time-section { text-align: right; height: 46px !important; display: flex !important; flex-direction: column !important; justify-content: center !important; align-items: flex-end !important; } }
         .csv-edit-page .big-time { font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important; color: #e2e8f0 !important; margin-bottom: 0.125rem !important; }
         .csv-edit-page .big-day-date { font-size: 0.875rem !important; font-weight: 500 !important; color: #94a3b8 !important; line-height: 1.2 !important; }
         .pink-theme #jsonDontEncryptToggleBtn.selected { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
         /* Pink theme JSON highlighting */
         .pink-theme .json-container { background-color: #fdf2f8; color: #831843; border: 1px solid #fbcfe8; border-radius: 0; padding: 1.5rem; box-shadow: 0 1px 3px 0 rgba(236, 72, 153, 0.1); }
         .pink-theme .json-key { color: #be185d; font-weight: 500; }
         .pink-theme .json-string { color: #059669; font-weight: 500; }
         .pink-theme .json-number { color: #d97706; font-weight: 500; }
         .pink-theme .json-boolean { color: #7c3aed; font-weight: 600; }
         .pink-theme .json-null { color: #9d174d; font-style: italic; font-weight: 500; }
         .pink-theme .toggle { cursor: pointer; user-select: none; color: #831843; font-weight: 500; }
         .pink-theme .json-value { outline: none; padding: 2px 4px; border-radius: 0; }
         .pink-theme .json-value:hover { background-color: #fbcfe8; }
         .pink-theme .json-value:focus { background-color: #fbcfe8; border: 1px solid #ec4899; }
         .pink-theme .bracket { color: #db2777; font-weight: 600; }
         .pink-theme .comma { color: #831843; font-weight: 500; }
         /* ==================== RECORD INFO STYLES ==================== */
         .record-info { color: #6b7280; }
         .record-info span { color: #1f2937; font-weight: 700; }
         .dark-theme .record-info { color: #cbd5e1; }
         .dark-theme .record-info span { color: #e2e8f0; }
         .white-theme .record-info { color: #6b7280; }
         .white-theme .record-info span { color: #1f2937; }
         .pink-theme .record-info { color: #be185d; }
         .pink-theme .record-info span { color: #831843; font-weight: 700; }
         /* ==================== PAGINATION BUTTON STYLES ==================== */
         .page-btn { background-color: transparent; color: #64748b; border: 1px solid #e2e8f0; }
         .page-btn:hover { background-color: #f8fafc; color: #64748b; border-color: #cbd5e1; }
         .page-btn.active { background-color: rgba(0, 0, 0, 0.05); color: #64748b; border-color: rgba(0, 0, 0, 0.1); }
         .dark-theme .page-btn { background-color: transparent !important; color: #94a3b8 !important; border: 1px solid #475569 !important; }
         .dark-theme .page-btn:hover { background-color: #334155 !important; color: #94a3b8 !important; border-color: #64748b !important; }
         .dark-theme .page-btn.active { background-color: #334155 !important; color: #94a3b8 !important; border-color: #64748b !important; }
         .white-theme .page-btn { background-color: transparent !important; color: #64748b !important; border: 1px solid #e2e8f0 !important; }
         .white-theme .page-btn:hover { background-color: #f1f5f9 !important; color: #64748b !important; border-color: #cbd5e1 !important; }
         .white-theme .page-btn.active { background-color: rgba(0, 0, 0, 0.05) !important; color: #64748b !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         .pink-theme .page-btn { background-color: transparent !important; color: #be185d !important; border: 1px solid #fbcfe8 !important; }
         .pink-theme .page-btn:hover { background-color: #fce7f3 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         .pink-theme .page-btn.active { background-color: #fce7f3 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         /* Force ghost button styling for pagination - higher specificity */
         .csv-edit-page .page-btn.active,
         .csv-edit-page .page-btn.active:hover,
         .csv-edit-page .page-btn.active:focus { background-color: rgba(0, 0, 0, 0.05) !important; color: #64748b !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         .csv-edit-page.dark-theme .page-btn.active,
         .csv-edit-page.dark-theme .page-btn.active:hover,
         .csv-edit-page.dark-theme .page-btn.active:focus { background-color: #334155 !important; color: #94a3b8 !important; border-color: #64748b !important; }
         .csv-edit-page.white-theme .page-btn.active,
         .csv-edit-page.white-theme .page-btn.active:hover,
         .csv-edit-page.white-theme .page-btn.active:focus { background-color: rgba(0, 0, 0, 0.05) !important; color: #64748b !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         .csv-edit-page.pink-theme .page-btn.active,
         .csv-edit-page.pink-theme .page-btn.active:hover,
         .csv-edit-page.pink-theme .page-btn.active:focus { background-color: #fce7f3 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         /* Ultra-specific pagination button overrides */
         .csv-edit-page .btn.btn-ghost.page-btn.active,
         .csv-edit-page .btn.btn-ghost.page-btn.active:hover,
         .csv-edit-page .btn.btn-ghost.page-btn.active:focus { background-color: rgba(0, 0, 0, 0.05) !important; color: #64748b !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         .csv-edit-page.dark-theme .btn.btn-ghost.page-btn.active,
         .csv-edit-page.dark-theme .btn.btn-ghost.page-btn.active:hover,
         .csv-edit-page.dark-theme .btn.btn-ghost.page-btn.active:focus { background-color: #334155 !important; color: #94a3b8 !important; border-color: #64748b !important; }
         .csv-edit-page.white-theme .btn.btn-ghost.page-btn.active,
         .csv-edit-page.white-theme .btn.btn-ghost.page-btn.active:hover,
         .csv-edit-page.white-theme .btn.btn-ghost.page-btn.active:focus { background-color: rgba(0, 0, 0, 0.05) !important; color: #64748b !important; border-color: rgba(0, 0, 0, 0.1) !important; }
         .csv-edit-page.pink-theme .btn.btn-ghost.page-btn.active,
         .csv-edit-page.pink-theme .btn.btn-ghost.page-btn.active:hover,
         .csv-edit-page.pink-theme .btn.btn-ghost.page-btn.active:focus { background-color: #fce7f3 !important; color: #be185d !important; border-color: #f9a8d4 !important; }
         /* Nuclear option - override ALL pagination button styles */
         .csv-edit-page button[class*="page-btn"][class*="active"],
         .csv-edit-page button[class*="page-btn"][class*="active"]:hover,
         .csv-edit-page button[class*="page-btn"][class*="active"]:focus,
         .csv-edit-page button[class*="page-btn"][class*="active"]:active { 
            background-color: rgba(0, 0, 0, 0.05) !important; 
            color: #64748b !important; 
            border-color: rgba(0, 0, 0, 0.1) !important; 
            box-shadow: none !important;
         }
         .csv-edit-page.dark-theme button[class*="page-btn"][class*="active"],
         .csv-edit-page.dark-theme button[class*="page-btn"][class*="active"]:hover,
         .csv-edit-page.dark-theme button[class*="page-btn"][class*="active"]:focus,
         .csv-edit-page.dark-theme button[class*="page-btn"][class*="active"]:active { 
            background-color: #334155 !important; 
            color: #94a3b8 !important; 
            border-color: #64748b !important; 
            box-shadow: none !important;
         }
         .csv-edit-page.white-theme button[class*="page-btn"][class*="active"],
         .csv-edit-page.white-theme button[class*="page-btn"][class*="active"]:hover,
         .csv-edit-page.white-theme button[class*="page-btn"][class*="active"]:focus,
         .csv-edit-page.white-theme button[class*="page-btn"][class*="active"]:active { 
            background-color: rgba(0, 0, 0, 0.05) !important; 
            color: #64748b !important; 
            border-color: rgba(0, 0, 0, 0.1) !important; 
            box-shadow: none !important;
         }
         .csv-edit-page.pink-theme button[class*="page-btn"][class*="active"],
         .csv-edit-page.pink-theme button[class*="page-btn"][class*="active"]:hover,
         .csv-edit-page.pink-theme button[class*="page-btn"][class*="active"]:focus,
         .csv-edit-page.pink-theme button[class*="page-btn"][class*="active"]:active { 
            background-color: #fce7f3 !important; 
            color: #be185d !important; 
            border-color: #f9a8d4 !important; 
            box-shadow: none !important;
         }
         /* Remove ugly blue cell borders */
         .csv-edit-page table,
         .csv-edit-page table *,
         .csv-edit-page th,
         .csv-edit-page td,
         .csv-edit-page tr { border-color: #e2e8f0 !important; }
         .csv-edit-page.dark-theme table,
         .csv-edit-page.dark-theme table *,
         .csv-edit-page.dark-theme th,
         .csv-edit-page.dark-theme td,
         .csv-edit-page.dark-theme tr { border-color: #475569 !important; }
         .csv-edit-page.white-theme table,
         .csv-edit-page.white-theme table *,
         .csv-edit-page.white-theme th,
         .csv-edit-page.white-theme td,
         .csv-edit-page.white-theme tr { border-color: #e2e8f0 !important; }
         .csv-edit-page.pink-theme table,
         .csv-edit-page.pink-theme table *,
         .csv-edit-page.pink-theme th,
         .csv-edit-page.pink-theme td,
         .csv-edit-page.pink-theme tr { border-color: #fbcfe8 !important; }
         /* Nuclear option - remove ALL blue borders from inputs and focus states */
         .csv-edit-page input,
         .csv-edit-page input:focus,
         .csv-edit-page input:active,
         .csv-edit-page input:hover,
         .csv-edit-page textarea,
         .csv-edit-page textarea:focus,
         .csv-edit-page textarea:active,
         .csv-edit-page textarea:hover,
         .csv-edit-page select,
         .csv-edit-page select:focus,
         .csv-edit-page select:active,
         .csv-edit-page select:hover { 
            border-color: #e2e8f0 !important; 
            outline: none !important; 
            box-shadow: none !important; 
         }
         .csv-edit-page.dark-theme input,
         .csv-edit-page.dark-theme input:focus,
         .csv-edit-page.dark-theme input:active,
         .csv-edit-page.dark-theme input:hover,
         .csv-edit-page.dark-theme textarea,
         .csv-edit-page.dark-theme textarea:focus,
         .csv-edit-page.dark-theme textarea:active,
         .csv-edit-page.dark-theme textarea:hover,
         .csv-edit-page.dark-theme select,
         .csv-edit-page.dark-theme select:focus,
         .csv-edit-page.dark-theme select:active,
         .csv-edit-page.dark-theme select:hover { 
            border-color: #475569 !important; 
            outline: none !important; 
            box-shadow: none !important; 
         }
         .csv-edit-page.white-theme input,
         .csv-edit-page.white-theme input:focus,
         .csv-edit-page.white-theme input:active,
         .csv-edit-page.white-theme input:hover,
         .csv-edit-page.white-theme textarea,
         .csv-edit-page.white-theme textarea:focus,
         .csv-edit-page.white-theme textarea:active,
         .csv-edit-page.white-theme textarea:hover,
         .csv-edit-page.white-theme select,
         .csv-edit-page.white-theme select:focus,
         .csv-edit-page.white-theme select:active,
         .csv-edit-page.white-theme select:hover { 
            border-color: #e2e8f0 !important; 
            outline: none !important; 
            box-shadow: none !important; 
         }
         .csv-edit-page.pink-theme input,
         .csv-edit-page.pink-theme input:focus,
         .csv-edit-page.pink-theme input:active,
         .csv-edit-page.pink-theme input:hover,
         .csv-edit-page.pink-theme textarea,
         .csv-edit-page.pink-theme textarea:focus,
         .csv-edit-page.pink-theme textarea:active,
         .csv-edit-page.pink-theme textarea:hover,
         .csv-edit-page.pink-theme select,
         .csv-edit-page.pink-theme select:focus,
         .csv-edit-page.pink-theme select:active,
         .csv-edit-page.pink-theme select:hover { 
            border-color: #fbcfe8 !important; 
            outline: none !important; 
            box-shadow: none !important; 
         }
         /* ==================== EDIT INDICATOR STYLES ==================== */
         .edit-indicator { margin-left: 10px; padding: 2px 8px; background: #f59e0b; color: white; border-radius: 0; font-size: 0.75rem; font-weight: normal; }
         .dark-theme .edit-indicator { background: #3b82f6; }
         .pink-theme .edit-indicator { background: #a855f7; }
         /* ==================== COMMON BUTTON STYLES ==================== */
         .btn { 
         padding: 0.625rem 1.25rem; 
         font-weight: 500; 
         border-radius: 0; 
         transition: all 0.2s ease; 
         border: none; 
         cursor: pointer; 
         display: inline-flex; 
         align-items: center; 
         justify-content: center; 
         gap: 0.5rem; 
         font-size: 0.875rem; 
         box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.05); 
         height: 46px; 
         }
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
         /* Persistent selected state for ghost buttons */
         .btn-ghost.selected,
         .btn-ghost.selected:hover {
         background-color: rgba(255, 255, 255, 0.1) !important;
         border-color: rgba(255, 255, 255, 0.2) !important;
         }
         /* ==================== COMMON INPUT STYLES ==================== */
         input[type="text"], select { 
         border-radius: 0; 
         border: 1px solid #e2e8f0; 
         padding: 0.625rem 1rem; 
         font-size: 0.875rem; 
         transition: all 0.2s ease; 
         height: 46px; 
         background-color: #ffffff; 
         color: #1e293b; 
         }
         input[type="text"]:focus, select:focus { outline: none; border-color: inherit; box-shadow: none; }
         /* ==================== JSON FONT STYLES ==================== */
         .json-container, .json-editor {
         font-family: Menlo, Monaco, 'Courier New', monospace !important;
         font-size: 14px !important;
         line-height: 1.6 !important;
         font-weight: normal !important;
         letter-spacing: 0 !important;
         }
         .json-key, .json-string, .json-number, .json-boolean, .json-null, .bracket, .comma, .toggle { 
         font-family: Menlo, Monaco, 'Courier New', monospace !important; 
         font-size: 14px !important; 
         letter-spacing: 0 !important; 
         }
         /* ==================== COMMON STYLES ==================== */
         .collapsed::before { 
            content: ''; 
            display: inline-block; 
            width: 12px; 
            height: 12px; 
            margin-right: 6px; 
            vertical-align: middle; 
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M4 2l4 4-4 4' stroke='%23e2e8f0' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
            background-size: contain;
            background-repeat: no-repeat;
            background-position: center;
         }
         .expanded::before { 
            content: ''; 
            display: inline-block; 
            width: 12px; 
            height: 12px; 
            margin-right: 6px; 
            vertical-align: middle; 
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M2 4l4 4 4-4' stroke='%23e2e8f0' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
            background-size: contain;
            background-repeat: no-repeat;
            background-position: center;
         }
         /* Theme-specific chevron colors */
         .dark-theme .collapsed::before {
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M4 2l4 4-4 4' stroke='%23e2e8f0' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
         }
         .dark-theme .expanded::before {
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M2 4l4 4 4-4' stroke='%23e2e8f0' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
         }
         .white-theme .collapsed::before {
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M4 2l4 4-4 4' stroke='%231e293b' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
         }
         .white-theme .expanded::before {
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M2 4l4 4 4-4' stroke='%231e293b' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
         }
         .pink-theme .collapsed::before {
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M4 2l4 4-4 4' stroke='%23831843' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
         }
         .pink-theme .expanded::before {
            background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 12'%3E%3Cpath d='M2 4l4 4 4-4' stroke='%23831843' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
         }
         .json-item { margin-left: 20px; }
         .hidden { display: none; }
         .module-badge { border-radius: 0; border: 1px solid; font-weight: 600; font-size: 14px; min-width: 60px; text-align: center; padding: 0.25rem 0.75rem; }
         .greeting-text { font-weight: 500 !important; font-size: 1.25rem !important; }
         .witty-message { font-weight: 400 !important; font-size: 0.875rem !important; margin-top: 0.25rem !important; opacity: 0.8; }
         .hidden-field { display: none !important; }
         /* ==================== EDITOR STYLES ==================== */
         #editor { 
         width: 100%; 
         height: 70vh; 
         min-height: 400px; 
         border: 1px solid #e2e8f0; 
         font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', monospace !important; 
         font-size: 14px !important; 
         line-height: 1.6 !important; 
         position: relative; 
         }
         .monaco-editor, .monaco-editor *:not(.codicon) { 
         font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', monospace !important; 
         font-variant-ligatures: contextual; 
         }
         .monaco-editor .codicon, .codicon { 
         font: normal normal normal 16px/1 codicon !important; 
         -webkit-font-smoothing: antialiased; 
         -moz-osx-font-smoothing: grayscale; 
         }
         /* ==================== DROPDOWN FIX ==================== */
         body.white-theme #theme-select, body.white-theme #module-select { 
           background-color: #f8fafc !important; 
           color: #1e293b !important; 
           border-color: #e2e8f0 !important; 
         }
         body.pink-theme #theme-select, body.pink-theme #module-select { 
           background-color: #fce7f3 !important; 
           color: #831843 !important; 
           border-color: #fbcfe8 !important; 
         }
         body.dark-theme #theme-select, body.dark-theme #module-select { 
           background-color: #334155 !important; 
           color: #e2e8f0 !important; 
           border-color: #475569 !important; 
         }
         /* ==================== VALIDATION WARNING STYLES ==================== */
         .validation-warning { position: fixed; top: 20px; left: 50%; transform: translateX(-50%); background-color: #dc2626; color: white; padding: 12px 24px; font-size: 14px; font-weight: 500; box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06); z-index: 10000; animation: slideDown 0.3s ease-out; max-width: 500px; text-align: center; white-space: pre-line; }
         @keyframes slideDown { from { transform: translateX(-50%) translateY(-100%); opacity: 0; } to { transform: translateX(-50%) translateY(0); opacity: 1; } }
         .validation-warning.hide { animation: slideUp 0.3s ease-out forwards; }
         @keyframes slideUp { from { transform: translateX(-50%) translateY(0); opacity: 1; } to { transform: translateX(-50%) translateY(-100%); opacity: 0; } }
         /* ==================== JSON VALUE EDIT HIGHLIGHTING ==================== */
         .json-value.edited { background-color: #fef3c7 !important; border: 1px solid #f59e0b !important; }
         .dark-theme .json-value.edited { background-color: #1e3a8a !important; border: 1px solid #3b82f6 !important; }
         .pink-theme .json-value.edited { background-color: #f3e8ff !important; border: 1px solid #a855f7 !important; }
         /* ==================== VALIDATION ERROR STYLES ==================== */
         .json-value.error { background-color: #fef2f2 !important; border: 1px solid #dc2626 !important; }
         .dark-theme .json-value.error { background-color: #7f1d1d !important; border: 1px solid #dc2626 !important; }
         .pink-theme .json-value.error { background-color: #fef2f2 !important; border: 1px solid #dc2626 !important; }
      </style>
   </head>
   <body class="min-h-screen">
      <script>
         // Get theme from server and localStorage, prioritize localStorage for persistence - COPIED FROM WORKING CSV EDITOR
              const serverTheme = '{{ theme }}';
         const savedTheme = localStorage.getItem('workbench-theme');
         const currentTheme = savedTheme || serverTheme || 'dark';

         // Apply the theme with proper class structure
         document.body.className = 'min-h-screen ' + currentTheme + '-theme';
         document.documentElement.className = currentTheme + '-theme';
         console.log('Applied theme:', currentTheme + '-theme');
         console.log('Body className:', document.body.className);

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

         // Set theme dropdown value and initialize notes
         document.addEventListener('DOMContentLoaded', function() {
           const themeDropdown = document.getElementById('theme-select');
           if (themeDropdown) {
             themeDropdown.value = currentTheme;
             console.log('Theme dropdown set to:', currentTheme);
           }

                     // Initialize notes functionality
               if (typeof initializeNotes === 'function') {
                 initializeNotes();
               } else {
                 console.error('initializeNotes function not found!');
               }

               // Initialize text encryption functionality
               if (typeof initializeTextEncryption === 'function') {
                 initializeTextEncryption();
               } else {
                 console.error('initializeTextEncryption function not found!');
               }

               // Backup initialization after a short delay
               setTimeout(() => {
                 if (typeof initializeNotes === 'function') {
                   console.log('Backup notes initialization...');
                   initializeNotes();
                 }
                 if (typeof initializeTextEncryption === 'function') {
                   console.log('Backup text encryption initialization...');
                   initializeTextEncryption();
                 }
               }, 1000);

               // Additional backup initialization after longer delay
               setTimeout(() => {
                 if (typeof initializeNotes === 'function') {
                   console.log('Final backup notes initialization...');
                   initializeNotes();
                 }
                 if (typeof initializeTextEncryption === 'function') {
                   console.log('Final backup text encryption initialization...');
                   initializeTextEncryption();
                 }
               }, 3000);
         });

         // Theme change function - COPIED FROM WORKING CSV EDITOR
         window.setTheme = function(theme) {
           // Remove all theme classes first
           document.body.classList.remove('dark-theme', 'white-theme', 'pink-theme');
           document.documentElement.classList.remove('dark-theme', 'white-theme', 'pink-theme');

           // Apply theme immediately
           document.documentElement.className = theme + '-theme';
           document.body.className = 'min-h-screen ' + theme + '-theme';

           // Update or remove preload-theme style
           const preloadStyle = document.getElementById('preload-theme');
           if (preloadStyle) {
             preloadStyle.remove();
           }

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

         // Module change function
         function updateModule(module) {
           // Update the hidden form field
           const moduleField = document.querySelector('input[name="module"]');
           if (moduleField) {
             moduleField.value = module;
           }

           // Save to session
           fetch('/set-module', {
             method: 'POST',
             headers: {
               'Content-Type': 'application/json',
             },
             body: JSON.stringify({module: module})
           });
         }

         // Save loader function - EXACT COPY FROM CSV EDITOR
         function showSaveLoaderAndRedirect() {
           // Prevent multiple loaders
           if (document.getElementById('json-save-loader')) {
             return;
           }

           const currentTheme = document.body.className;
           let progressColor = '#3b82f6'; // Bright blue for dark mode
           let backgroundColor = '#374151'; // Default gray

           if (currentTheme.includes('pink-theme')) {
             progressColor = '#ec4899'; // Bright pink
             backgroundColor = '#fce7f3'; // Light pink
           } else if (currentTheme.includes('white-theme')) {
             progressColor = '#10b981'; // Green
             backgroundColor = '#e5e7eb'; // Light gray
           }

           const loader = document.createElement('div');
           loader.id = 'json-save-loader';
           loader.style.cssText = `
             position: fixed;
             top: 0;
             left: 0;
             width: 100%;
             height: 100%;
             background: rgba(0, 0, 0, 0.3);
             backdrop-filter: blur(8px);
             -webkit-backdrop-filter: blur(8px);
             display: flex;
             justify-content: center;
             align-items: center;
             z-index: 9999;
             font-family: 'Inter', sans-serif;
           `;

           loader.innerHTML = `
             <div style="text-align: center;">
                          <div id="save-loader-text" style="color: white; font-size: 18px; font-weight: 600; margin-bottom: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">PREPARING DATA</div>
                 <div style="width: 800px; height: 5px; background-color: ${backgroundColor}; border-radius: 0px; overflow: hidden; position: relative; margin: 0 auto;">
                   <div id="save-progress-bar" style="position: absolute; top: 0; left: 0; width: 0%; height: 100%; background-color: ${progressColor}; transition: width 0.3s ease; border-radius: 0px;"></div>
                 </div>
                 <div style="font-size: 24px; font-weight: 800; color: white; margin-top: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;" id="save-progress-text">0%</div>
             </div>
           `;

           document.body.appendChild(loader);

           // Animate progress
           let progress = 0;
           const steps = [
             { text: 'PREPARING DATA', target: 20 },
             { text: 'VALIDATING CHANGES', target: 40 },
             { text: 'ENCRYPTING', target: 60 },
             { text: 'UPLOADING TO S3', target: 80 },
             { text: 'SAVED', target: 100 }
           ];

           let stepIndex = 0;
           const stepInterval = setInterval(() => {
             if (stepIndex < steps.length) {
               const step = steps[stepIndex];
               document.getElementById('save-loader-text').textContent = step.text;

               const progressInterval = setInterval(() => {
                 progress += 2;
                 if (progress >= step.target) {
                   progress = step.target;
                   clearInterval(progressInterval);
                 }
                 document.getElementById('save-progress-bar').style.width = progress + '%';
                 document.getElementById('save-progress-text').textContent = progress + '%';
               }, 50);

               stepIndex++;

               // If this is the last step (SAVED), redirect to home after delay
               if (stepIndex === steps.length) {
                 setTimeout(() => {
                   window.location.href = '/';
                 }, 1500);
               }
             }
           }, 700);
         }

         // This handler is now integrated into the main form submission handler below
      </script>
      <!-- Add padding container -->
      <div class="w-full min-h-screen main-container p-8">
         <!-- Header -->
         <div class="flex items-center justify-between mb-6">
            <div class="flex items-center space-x-3">
               <a href="{{ url_for('home') }}">
                  <div class="flex items-center">
                     <img src="{{ logo }}" class="h-16 w-auto mr-1" alt="Logo" />
                     <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
                  </div>
               </a>
               <span id="edit-indicator" class="edit-indicator" style="display: none;"></span>
            </div>
            <!-- Right side: Greeting and Theme Toggle -->
            <div class="flex items-center space-x-4">
               <div class="text-right">
                  <div class="big-time-display" style="margin-top: 0px;">
                     <div class="time-section" style="align-items: flex-end !important; justify-content: flex-end !important;">
                        <div class="big-time" style="font-size: 1.5rem !important; font-weight: 700 !important; line-height: 1.2 !important;">{{ big_time_display.big_time }}</div>
                        <div class="big-day-date" style="font-size: 0.875rem !important; font-weight: 500 !important; line-height: 1.2 !important;">{{ big_time_display.day_date }}</div>
                     </div>
                  </div>
               </div>
               <div class="theme-toggle">
                  <select id="theme-select" class="border px-4 py-2 text-base theme-dropdown" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="setTheme(this.value)">
                     <option value="dark">🌃   Dark</option>
                     <option value="white">🔆  White</option>
                     <option value="pink">🌸  Pink</option>
                  </select>
               </div>
            </div>
         </div>
         <!-- S3 Path & Controls -->
         <form method="post" action="{{ url_for('save_json') }}" id="json-form" class="mb-4">
            <div class="flex items-center space-x-2 mb-4">
               <div class="flex-1 flex items-center space-x-2">
                  <button
                     type="button"
                     class="s3BrowseBtn btn btn-ghost btn-icon"
                     style="width:46px;height:46px;padding:0;font-size:18px;line-height:46px;display:inline-flex;align-items:center;justify-content:center;"
                     title="Browse S3"
                     >🪣️</button>
                  <input
                     type="text"
                     id="s3_path"
                     name="s3_path"
                     value="{{ s3_path }}"
                     class="flex-grow border px-4 py-2 text-base theme-transition"
                     style="height: 46px;"
                     onchange="savePathToSession(this.value)"
                     autocomplete="off"
                     />
               </div>
               {% if decryption_module %}
               <div class="flex items-center space-x-2">
                  <span class="px-3 py-1 text-sm font-medium theme-transition module-badge">{{ decryption_module }}</span>
               </div>
               {% else %}
               <select id="module-select" name="module" class="border px-4 py-2 text-sm theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="updateModule(this.value)">
               <option value="dxp" {{ 'selected' if module == 'dxp' else '' }}>dxp</option>
               <option value="dap" {{ 'selected' if module == 'dap' else '' }}>dap</option>
               <option value="pa" {{ 'selected' if module == 'pa' else '' }}>pa</option>
               </select>
               {% endif %}
               <button id="jsonDontEncryptToggleBtn"
                  type="button"
                  class="btn btn-ghost btn-icon"
                  title="Disable encryption for this save"
                  onclick="toggleJsonDontEncrypt(); return false;"
                  style="height: 46px; width: 46px;">
               🔓
               </button>
               <button
                  type="submit"
                  form="json-form"
                  class="btn btn-ghost"
                  title="Save changes"
                  style="height: 46px;">
               💾 Save
               </button>
               <style>
                  #jsonDontEncryptToggleBtn { height: 46px; width: 46px; }
                  /* Hover grey on white theme (match Home) */
                  .white-theme #jsonDontEncryptToggleBtn:hover:not(:disabled) { background-color: #f1f5f9 !important; border-color: #cbd5e1 !important; }
                  /* Persist selected highlight across themes (match Home) */
                  #jsonDontEncryptToggleBtn.selected,
                  .white-theme #jsonDontEncryptToggleBtn.selected { background-color: rgba(0, 0, 0, 0.05) !important; border-color: rgba(0, 0, 0, 0.1) !important; }
                  .dark-theme #jsonDontEncryptToggleBtn.selected { background-color: #334155 !important; border-color: #64748b !important; }
                  .pink-theme #jsonDontEncryptToggleBtn.selected { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
               </style>
            </div>
            <!-- Hidden fields -->
            <input type="hidden" name="orig_s3_path" value="{{ s3_path }}" />
            <input type="hidden" name="module" value="{{ module }}" />
            <input type="hidden" name="decryption_module" value="{{ decryption_module or module }}" />
            <input type="hidden" name="gzipped" value="{{ gzipped }}" />
            <input type="hidden" name="json_data" id="json_data" />
            <input type="hidden" name="is_jsonl" value="{{ is_jsonl }}" />
            <input type="hidden" name="is_json_object" value="{{ is_json_object }}" />
            <input type="hidden" name="json_type" value="{{ json_type }}" />
            <input type="hidden" name="current_record" value="{{ current_record }}" />
            <input type="hidden" name="total_records" value="{{ total_records }}" />
         </form>
         <!-- Pagination with Save/Back buttons - Always show for JSON editor -->
         <div class="flex items-center justify-between mb-4 space-x-2">
            <!-- Left: Record count -->
            <div class="btn btn-ghost text-lg text-gray-600 record-info whitespace-nowrap flex items-center" style="cursor: default; pointer-events: none;">
               {% if show_pagination %}
               <span class="font-bold text-gray-800">{{ current_record + 1 }}</span>&nbsp;of&nbsp;<span class="font-bold text-gray-800">{{ total_records }}</span>
               {% else %}
               <span class="font-bold text-gray-800">{{ total_records }}</span>&nbsp;of&nbsp;<span class="font-bold text-gray-800">{{ total_records }}</span>
               {% endif %}
            </div>
            <!-- Center: Pagination controls -->
            <div class="flex items-center justify-end flex-1">
               {% if show_pagination and total_records > 1 %}
               {% set max_visible_pages = 7 %}
               {% set window_threshold = 5 %}
               {% set current_page = current_record + 1 %}
               {# Calculate pagination window - STABLE VERSION #}
               {% if total_records <= max_visible_pages %}
               {# Show all pages if they fit #}
               {% set start_page = 1 %}
               {% set end_page = total_records %}
               {% else %}
               {# Stable window logic: only shift when near edges #}
               {% if current_page <= window_threshold %}
               {# Near start: always show pages 1-7 #}
               {% set start_page = 1 %}
               {% set end_page = max_visible_pages %}
               {% elif current_page > total_records - window_threshold %}
               {# Near end: always show last 7 pages #}
               {% set start_page = total_records - max_visible_pages + 1 %}
               {% set end_page = total_records %}
               {% else %}
               {# Middle: center window on current page #}
               {% set start_page = current_page - 3 %}
               {% set end_page = current_page + 3 %}
               {% endif %}
               {% endif %}
               <div class="flex items-center space-x-2">
                  {# Previous page #}
                  {% if current_record > 0 %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block">
                     <input type="hidden" name="action" value="view_json" />
                     <input type="hidden" name="s3_path" value="{{ s3_path }}" />
                     <input type="hidden" name="module" value="{{ module }}" />
                     <input type="hidden" name="record" value="{{ current_record - 1 }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">‹</button>
                  </form>
                  {% endif %}
                  {# First page if not in window #}
                  {% if start_page > 1 %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block">
                     <input type="hidden" name="action" value="view_json" />
                     <input type="hidden" name="s3_path" value="{{ s3_path }}" />
                     <input type="hidden" name="module" value="{{ module }}" />
                     <input type="hidden" name="record" value="0" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">1</button>
                  </form>
                  {% if start_page > 2 %}
                  <span class="px-2 text-gray-500 flex items-center" style="height: 46px;">…</span>
                  {% endif %}
                  {% endif %}
                  {# Page numbers in window #}
                  {% for p in range(start_page, end_page + 1) %}
                  {% if p == current_page %}
                  <span class="btn btn-ghost page-btn active" style="min-width: 40px; height: 46px; display: inline-flex; align-items: center; justify-content: center;">{{ p }}</span>
                  {% else %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block">
                     <input type="hidden" name="action" value="view_json" />
                     <input type="hidden" name="s3_path" value="{{ s3_path }}" />
                     <input type="hidden" name="module" value="{{ module }}" />
                     <input type="hidden" name="record" value="{{ p - 1 }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">{{ p }}</button>
                  </form>
                  {% endif %}
                  {% endfor %}
                  {# Last page if not in window #}
                  {% if end_page < total_records %}
                  {% if end_page < total_records - 1 %}
                  <span class="px-2 text-gray-500 flex items-center" style="height: 46px;">…</span>
                  {% endif %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block">
                     <input type="hidden" name="action" value="view_json" />
                     <input type="hidden" name="s3_path" value="{{ s3_path }}" />
                     <input type="hidden" name="module" value="{{ module }}" />
                     <input type="hidden" name="record" value="{{ total_records - 1 }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">{{ total_records }}</button>
                  </form>
                  {% endif %}
                  {# Next page #}
                  {% if current_record < total_records - 1 %}
                  <form method="post" action="{{ url_for('home') }}" class="inline-block">
                     <input type="hidden" name="action" value="view_json" />
                     <input type="hidden" name="s3_path" value="{{ s3_path }}" />
                     <input type="hidden" name="module" value="{{ module }}" />
                     <input type="hidden" name="record" value="{{ current_record + 1 }}" />
                     <button type="submit" class="btn btn-ghost page-btn" style="min-width: 40px; height: 46px;">›</button>
                  </form>
                  {% endif %}
               </div>
               {% endif %}
            </div>
            <!-- Right: Back button (icon only) - Always show -->
            <div class="flex items-center">
               <a
                  href="{{ url_for('home') }}"
                  class="btn btn-ghost btn-icon"
                  title="Back to home"
                  onclick="return validateBeforeLeaving(event)"
                  style="height: 46px; width: 46px;"
                  >
               ←
               </a>
            </div>
         </div>
         <!-- JSON Editor -->
         <div class="json-container p-4 shadow overflow-x-auto">
            <div id="json-editor" class="font-mono text-sm"></div>
         </div>
      </div>
      <script>
         function showLoader() {
         // Prevent duplicate loaders
         if (document.getElementById('json-loading-overlay')) {
         return;
         }

         // Get current theme colors
         const currentTheme = document.body.className;
         let backgroundColor = '#1e293b'; // Dark default
         let textColor = 'white';
         let spinnerColor = '#6366f1';

         if (currentTheme.includes('white-theme')) {
         backgroundColor = '#ffffff';
         textColor = '#1f2937';
         spinnerColor = '#6366f1';
         } else if (currentTheme.includes('pink-theme')) {
         backgroundColor = '#ffffff';
         textColor = '#831843';
         spinnerColor = '#ec4899';
         }

         const overlay = document.createElement('div');
         overlay.id = 'json-loading-overlay';
         overlay.style.cssText = `
         position: fixed;
         top: 0;
         left: 0;
         width: 100%;
         height: 100%;
         background: rgba(0, 0, 0, 0.3);
         backdrop-filter: blur(8px);
         -webkit-backdrop-filter: blur(8px);
         display: flex;
         justify-content: center;
         align-items: center;
         z-index: 9999;
         `;

         overlay.innerHTML = `
         <div style="text-align: center;">
          <div style="color: white; font-size: 18px; font-weight: 600; margin-bottom: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">LOADING</div>
          <div style="width: 800px; height: 5px; background-color: ${currentTheme.includes('dark-theme') ? '#334155' : currentTheme.includes('pink-theme') ? '#fbcfe8' : '#e2e8f0'}; overflow: hidden; position: relative; margin: 0 auto;">
            <div style="position: absolute; top: 0; left: 0; width: 30%; height: 100%; background-color: ${spinnerColor}; animation: loading-bar 1.5s ease-in-out infinite;"></div>
          </div>
          <div style="font-size: 24px; font-weight: 800; color: white; margin-top: 20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">Loading record...</div>
         </div>
         <style>
          @keyframes loading-bar {
            0% { left: -30%; }
            100% { left: 100%; }
          }
         </style>
         `;

         document.body.appendChild(overlay);

         // Auto-remove after 10 seconds as safety
         setTimeout(() => {
         const loader = document.getElementById('json-loading-overlay');
         if (loader) loader.remove();
         }, 10000);
         }

         // Save path to session when it changes (only for S3 paths)
         function savePathToSession(path) {
         if (path.toLowerCase().startsWith('s3://')) {
         fetch('/set-path', {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
          },
          body: JSON.stringify({path: path})
         });
         }
         }

         // Store the current data
         let jsonData = {{ json_data_str | safe }};

         // Store cache key for tracking changes
         const cacheKey = '{{ cache_key }}';
         let recordIndex = {{ current_record }};
         const totalEdits = {{ total_edits | default(0) }};

         // Track edits locally - initialize with any existing edits for this record
         let jsonEdits = {{ record_edits | tojson | safe }};

         // Track validation errors
         let validationErrors = {};

         // Function to show validation warning
         function showValidationWarning(message) {
         // Remove any existing warning
         const existingWarning = document.querySelector('.validation-warning');
         if (existingWarning) {
         existingWarning.remove();
         }

         // Create new warning
         const warning = document.createElement('div');
         warning.className = 'validation-warning';
         warning.textContent = message;
         document.body.appendChild(warning);

         // Auto-hide after 5 seconds
         setTimeout(() => {
         warning.classList.add('hide');
         setTimeout(() => warning.remove(), 300);
         }, 5000);
         }

             // Function to validate all fields
    function validateAllFields() {
      // Check both validationErrors object and DOM elements with error class
      const hasErrors = Object.keys(validationErrors).length > 0;
      const errorElements = document.querySelectorAll('.json-value.error');

      if (hasErrors || errorElements.length > 0) {
        // Show all errors in one warning
        const errorMessages = Object.values(validationErrors);
        if (errorMessages.length === 0 && errorElements.length > 0) {
          errorMessages.push('Invalid JSON values detected. Please fix the highlighted fields.');
        }
        const warningMessage = `Validation errors found:\n${errorMessages.join('\n')}`;
        showValidationWarning(warningMessage);

        // Highlight all error fields
        Object.keys(validationErrors).forEach(path => {
          const element = document.querySelector(`[data-path="${path}"] .json-value`);
          if (element) {
            element.classList.add('error');
          }
        });

        console.log('Validation failed:', { hasErrors, errorElementsCount: errorElements.length });
        return false;
      }

      console.log('Validation passed');
      return true;
    }

         // Function to validate before leaving the page
         window.validateBeforeLeaving = function(event) {
         if (!validateAllFields()) {
         event.preventDefault();
         return false;
         }
         return true;
         }

         // Function to track JSON changes
         function trackJsonChange(element) {
         const path = getFieldPath(element);
         const value = element.textContent.trim();
         const original = element.dataset.original || '';

         // Remove any previous error state
         element.classList.remove('error');
         delete validationErrors[path];

         // Validate and determine type based on input
         let parsedValue;
         let detectedType;
         let validationError = null;

         // Check for single quotes
         if (value.includes("'")) {
         validationError = "JSON does not support single quotes. Please use double quotes for strings.";
         validationErrors[path] = validationError;
         element.classList.add('error');
         return;
         }

         // Check for unclosed quotes
         const doubleQuoteCount = (value.match(/"/g) || []).length;
         if (doubleQuoteCount % 2 !== 0) {
         validationError = "Please ensure all quotes are properly closed.";
         validationErrors[path] = validationError;
         element.classList.add('error');
         return;
         }

         // Determine type and parse value
         if (value === 'null') {
         parsedValue = null;
         detectedType = 'null';
         } else if (value === 'true' || value === 'false') {
         parsedValue = value === 'true';
         detectedType = 'boolean';
         } else if (value.startsWith('"') && value.endsWith('"') && value.length >= 2) {
         // It's a string - remove the quotes for storage
         parsedValue = value.slice(1, -1);
         detectedType = 'string';
         } else {
         // Try to parse as number
         const numValue = Number(value);
         if (!isNaN(numValue) && value !== '') {
          parsedValue = numValue;
          detectedType = 'number';
         } else {
          // If it's not a valid number and doesn't have quotes, mark as error
          validationError = `Invalid JSON value: "${value}". Use double quotes for strings (e.g., "text") or enter a valid number.`;
          validationErrors[path] = validationError;
          element.classList.add('error');
          return;
         }
         }

         // Update the display based on the detected type
         element.className = `json-${detectedType} json-value`;
         if (element.classList.contains('edited') && value === original) {
         element.classList.remove('edited');
         }

         // Check if value changed
         if (value !== original) {
         jsonEdits[path] = {
          value: parsedValue,
          original: original,
          type: detectedType
         };
         element.classList.add('edited');
         } else {
         delete jsonEdits[path];
         element.classList.remove('edited');
         }

         updateEditCount();

         // Only send to server if valid AND value actually changed
         if (!validationError && value !== original) {
         fetch('/update-json-edit', {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
          },
          body: JSON.stringify({
            cache_key: cacheKey,
            record_index: recordIndex,
            field_path: path,
            value: parsedValue,
            data_type: detectedType
          })
         }).catch(error => {
          console.error('Error tracking JSON change:', error);
         });
         }
         }

         // Update edit count indicator
         function updateEditCount() {
         const currentRecordEdits = Object.keys(jsonEdits).length;
         const indicator = document.getElementById('edit-indicator');

         // Calculate total edits (current record changes + other records)
         const otherRecordsEdits = Math.max(0, totalEdits - Object.keys({{ record_edits | tojson | safe }}).length);
         const totalCount = currentRecordEdits + otherRecordsEdits;

         if (totalCount > 0) {
         indicator.textContent = `${totalCount} edit${totalCount !== 1 ? 's' : ''}`;
         indicator.style.display = 'inline';
         } else {
         indicator.style.display = 'none';
         }
         }

         // Function to get field path from element
         function getFieldPath(element) {
         let path = '';
         let current = element;

         while (current && current.id !== 'json-editor') {
         const container = current.closest('[data-path]');
         if (container && container.dataset.path) {
          path = container.dataset.path;
          break;
         }
         current = current.parentElement;
         }

         return path;
         }

         function createEditor(obj, parent = null, key = null, path = '', isLast = true) {
         const container = document.createElement('div');
         container.dataset.path = path;
         container.style.display = 'inline';

         if (obj === null || obj === undefined) {
         const span = document.createElement('span');
         span.className = 'json-null json-value';
         span.contentEditable = true;
         span.dataset.type = 'null';
         span.dataset.original = 'null';
         span.textContent = 'null';
         // Mark as edited if this field was changed
         if (jsonEdits[path]) {
          span.classList.add('edited');
         }
         container.appendChild(span);
         } else if (typeof obj === 'boolean') {
         const span = document.createElement('span');
         span.className = 'json-boolean json-value';
         span.contentEditable = true;
         span.dataset.type = 'boolean';
         span.dataset.original = obj.toString();
         span.textContent = obj.toString();
         // Mark as edited if this field was changed
         if (jsonEdits[path]) {
          span.classList.add('edited');
         }
         container.appendChild(span);
         } else if (typeof obj === 'number') {
         const span = document.createElement('span');
         span.className = 'json-number json-value';
         span.contentEditable = true;
         span.dataset.type = 'number';
         span.dataset.original = obj.toString();
         span.textContent = obj.toString();
         // Mark as edited if this field was changed
         if (jsonEdits[path]) {
          span.classList.add('edited');
         }
         container.appendChild(span);
         } else if (typeof obj === 'string') {
         const span = document.createElement('span');
         span.className = 'json-string json-value';
         span.contentEditable = true;
         span.dataset.type = 'string';
         span.dataset.original = '"' + obj + '"';
         span.textContent = '"' + obj + '"';
         // Mark as edited if this field was changed
         if (jsonEdits[path]) {
          span.classList.add('edited');
         }
         container.appendChild(span);
         } else if (Array.isArray(obj)) {
         const id = 'array-' + Math.random().toString(36).substr(2, 9);

         // Create toggle span
         const toggleSpan = document.createElement('span');
         toggleSpan.className = 'toggle expanded';
         toggleSpan.setAttribute('data-toggle-id', id);
         toggleSpan.onclick = function() { toggle(id, this); };

         if (key !== null) {
          const keySpan = document.createElement('span');
          keySpan.className = 'json-key';
          keySpan.textContent = '"' + key + '"';
          toggleSpan.appendChild(keySpan);
          toggleSpan.appendChild(document.createTextNode(': '));
         }

         const openBracket = document.createElement('span');
         openBracket.className = 'bracket';
         openBracket.textContent = '[';
         toggleSpan.appendChild(openBracket);

         container.appendChild(toggleSpan);

         // Create items container
         const itemsContainer = document.createElement('div');
         itemsContainer.id = id;
         itemsContainer.className = 'json-item';
         itemsContainer.setAttribute('data-json-type', 'array');

         obj.forEach((item, index) => {
          const itemDiv = document.createElement('div');
          itemDiv.dataset.index = index;
          const childPath = path ? path + '.' + index : String(index);
          const isLastItem = index === obj.length - 1;
          const childEditor = createEditor(item, null, null, childPath, isLastItem);
          itemDiv.appendChild(childEditor);
          if (!isLastItem) {
            const comma = document.createElement('span');
            comma.className = 'comma';
            comma.textContent = ',';
            itemDiv.appendChild(comma);
          }
          itemsContainer.appendChild(itemDiv);
         });

         container.appendChild(itemsContainer);

         const closeBracket = document.createElement('span');
         closeBracket.className = 'bracket';
         closeBracket.textContent = ']';
         container.appendChild(closeBracket);
         } else if (typeof obj === 'object') {
         const id = 'object-' + Math.random().toString(36).substr(2, 9);

         // Create toggle span
         const toggleSpan = document.createElement('span');
         toggleSpan.className = 'toggle expanded';
         toggleSpan.setAttribute('data-toggle-id', id);
         toggleSpan.onclick = function() { toggle(id, this); };

         if (key !== null) {
          const keySpan = document.createElement('span');
          keySpan.className = 'json-key';
          keySpan.textContent = '"' + key + '"';
          toggleSpan.appendChild(keySpan);
          toggleSpan.appendChild(document.createTextNode(': '));
         }

         const openBracket = document.createElement('span');
         openBracket.className = 'bracket';
         openBracket.textContent = '{';
         toggleSpan.appendChild(openBracket);

         container.appendChild(toggleSpan);

         // Create properties container
         const propsContainer = document.createElement('div');
         propsContainer.id = id;
         propsContainer.className = 'json-item';
         propsContainer.setAttribute('data-json-type', 'object');

         const keys = Object.keys(obj);
         keys.forEach((k, index) => {
          const propDiv = document.createElement('div');
          propDiv.dataset.key = k;
          const keySpan = document.createElement('span');
          keySpan.className = 'json-key';
          keySpan.textContent = '"' + k + '"';
          propDiv.appendChild(keySpan);
          propDiv.appendChild(document.createTextNode(': '));

          const childPath = path ? path + '.' + k : k;
          const isLastProp = index === keys.length - 1;
          const valueEditor = createEditor(obj[k], null, null, childPath, isLastProp);
          propDiv.appendChild(valueEditor);

          if (!isLastProp) {
            const comma = document.createElement('span');
            comma.className = 'comma';
            comma.textContent = ',';
            propDiv.appendChild(comma);
          }

          propsContainer.appendChild(propDiv);
         });

         container.appendChild(propsContainer);

         const closeBracket = document.createElement('span');
         closeBracket.className = 'bracket';
         closeBracket.textContent = '}';
         container.appendChild(closeBracket);
         }

         return container;
         }

         function toggle(id, element) {
         const div = document.getElementById(id);
         if (div.classList.contains('hidden')) {
         div.classList.remove('hidden');
         element.classList.remove('collapsed');
         element.classList.add('expanded');
         } else {
         div.classList.add('hidden');
         element.classList.remove('expanded');
         element.classList.add('collapsed');
         }
         }

         function expandAll() {
         document.querySelectorAll('.toggle').forEach(el => {
         el.classList.remove('collapsed');
         el.classList.add('expanded');
         });
         document.querySelectorAll('.json-item').forEach(el => {
         el.classList.remove('hidden');
         });
         }

         function collapseAll() {
         document.querySelectorAll('.toggle').forEach(el => {
         el.classList.remove('expanded');
         el.classList.add('collapsed');
         });
         document.querySelectorAll('.json-item').forEach(el => {
         el.classList.add('hidden');
         });
         }

         function collectData(element) {
         console.log('=== CollectData called ===');
         console.log('Element:', element);
         console.log('Element tagName:', element.tagName);
         console.log('Element className:', element.className);

         // Direct value check
         if (element.classList && element.classList.contains('json-value')) {
         const text = element.textContent.trim();
         console.log('Direct value element with text:', text);

         if (text === 'null') return null;
         if (text === 'true') return true;
         if (text === 'false') return false;
         if (element.classList.contains('json-number')) {
          return parseFloat(text);
         }
         if (element.classList.contains('json-string')) {
          return text.replace(/^"|"$/g, '');
         }
         return text;
         }

         // Check if this is a container div
         if (element.tagName === 'DIV' && element.children.length > 0) {
         // Look for toggle element to determine if it's an array or object
         const firstChild = element.children[0];
         console.log('First child:', firstChild);

         // Check for a toggle span with data-toggle-id
         if (firstChild && firstChild.classList && firstChild.classList.contains('toggle')) {
          const toggleId = firstChild.getAttribute('data-toggle-id');
          console.log('Found toggle with id:', toggleId);

          if (toggleId) {
            const container = document.getElementById(toggleId);
            if (container) {
              const jsonType = container.getAttribute('data-json-type');
              console.log('Container type:', jsonType);

              if (jsonType === 'array') {
                return collectArray(container);
              } else if (jsonType === 'object') {
                return collectObject(container);
              }
            }
          }
         }

         // If no toggle, check for direct json-value
         const valueEl = element.querySelector('.json-value');
         if (valueEl && !element.querySelector('.toggle')) {
          return collectData(valueEl);
         }
         }

         // Check for array/object by looking for specific IDs
         const html = element.innerHTML || '';

         // Array check
         const arrayMatch = html.match(/id="(array-[^"]+)"/);
         if (arrayMatch) {
         const container = document.getElementById(arrayMatch[1]);
         if (container) {
          return collectArray(container);
         }
         }

         // Object check
         const objectMatch = html.match(/id="(object-[^"]+)"/);
         if (objectMatch) {
         const container = document.getElementById(objectMatch[1]);
         if (container) {
          return collectObject(container);
         }
         }

         console.log('No recognized pattern, returning null');
         return null;
         }

         function collectArray(container) {
         console.log('Collecting array from container:', container);
         const items = [];
         const itemDivs = container.querySelectorAll(':scope > div');
         console.log('Array has', itemDivs.length, 'items');

         itemDivs.forEach((itemDiv, index) => {
         console.log(`Processing array item ${index}:`, itemDiv);
         // Look for the first element child that contains the value
         let valueElement = null;
         for (let child of itemDiv.children) {
          if (!child.classList || !child.classList.contains('comma')) {
            valueElement = child;
            break;
          }
         }

         if (valueElement) {
          console.log(`Array item ${index} value element:`, valueElement);
          const itemData = collectData(valueElement);
          items.push(itemData);
         } else {
          console.warn(`No value element found for array item ${index}`);
          items.push(null);
         }
         });

         console.log('Collected array:', items);
         return items;
         }

         function collectObject(container) {
         console.log('Collecting object from container:', container);
         const obj = {};
         const propDivs = container.querySelectorAll(':scope > div');
         console.log('Object has', propDivs.length, 'properties');

         propDivs.forEach((propDiv, index) => {
         console.log(`Processing property ${index}:`, propDiv);
         const keyEl = propDiv.querySelector('.json-key');
         if (!keyEl) {
          console.warn(`No key element found for property ${index}`);
          return;
         }

         // Remove quotes from key
         const key = keyEl.textContent.replace(/^"|"$/g, '');
         console.log(`Property key: "${key}"`);

         // Find the value element - it's after the key and colon
         let valueElement = null;
         let colonFound = false;

         // Iterate through all child nodes (including text nodes)
         for (let i = 0; i < propDiv.childNodes.length; i++) {
          const node = propDiv.childNodes[i];

          // Look for colon in text nodes
          if (node.nodeType === Node.TEXT_NODE && node.textContent.includes(':')) {
            colonFound = true;
            console.log('Found colon');
            continue;
          }

          // After colon, find the value element
          if (colonFound && node.nodeType === Node.ELEMENT_NODE) {
            // Skip comma and bracket elements
            if (node.classList && (node.classList.contains('comma') || node.classList.contains('bracket'))) {
              continue;
            }

            valueElement = node;
            console.log('Found value element:', valueElement);
            break;
          }
         }

         if (valueElement) {
          const value = collectData(valueElement);
          console.log(`Property "${key}" value:`, value);
          obj[key] = value;
         } else {
          console.warn(`No value found for property "${key}"`);
          obj[key] = null;
         }
         });

         console.log('Collected object:', obj);
         return obj;
         }

         // Render the editor
         const editor = createEditor(jsonData);
         document.getElementById('json-editor').appendChild(editor);

         // Store original values when focusing on elements
         document.addEventListener('focus', function(e) {
         if (e.target.classList.contains('json-value')) {
         // Store the original value when focus starts
         if (!e.target.dataset.originalOnFocus) {
          e.target.dataset.originalOnFocus = e.target.textContent.trim();
         }
         }
         });

         // Add event listeners for string editing
         document.addEventListener('input', function(e) {
         if (e.target.classList.contains('json-value')) {
         // Only track changes if content actually changed
         const current = e.target.textContent.trim();
         const originalOnFocus = e.target.dataset.originalOnFocus || '';
         const originalValue = e.target.dataset.original || '';

         // Only mark as edited and track if the value actually changed from original
         if (current !== originalValue) {
          trackJsonChange(e.target);
         }
         }
         });

         // Initialize edit count on page load
         updateEditCount();

         document.addEventListener('focusout', function(e) {
         if (e.target.classList.contains('json-value')) {
         // Clear the focus tracking and validate on blur
         delete e.target.dataset.originalOnFocus;
         trackJsonChange(e.target);
         }
         });

         // Intercept all form submissions for validation
         document.addEventListener('submit', function(e) {
         // Check if this is a pagination form
         const form = e.target;
         const actionInput = form.querySelector('input[name="action"]');

         if (actionInput && actionInput.value === 'view_json') {
         // Intercept JSON pagination and fetch next record from server cache without full reload
         e.preventDefault();
         if (!validateAllFields()) {
           return false;
         }
         const recInput = form.querySelector('input[name="record"]');
         const targetIndex = parseInt((recInput && recInput.value) || '0', 10) || 0;
         // Fetch record from server cache
         fetch('/json-record', {
           method: 'POST',
           headers: { 'Content-Type': 'application/json' },
           body: JSON.stringify({ cache_key: cacheKey, record: targetIndex })
         }).then(r => r.json()).then(data => {
           if (!data || !data.success) { form.submit(); return; }
           // Update in-memory data and re-render editor
           jsonData = data.record;
           // Load edits for this record so edited highlights persist
           jsonEdits = data.record_edits || {};
           const container = document.getElementById('json-editor');
           if (container) { container.innerHTML = ''; const editorEl = createEditor(jsonData); container.appendChild(editorEl); }
           // Update hidden current_record
           const currInput = document.querySelector('input[name="current_record"]');
           if (currInput) currInput.value = targetIndex;
           // Update in-memory record index for subsequent edit tracking
           recordIndex = targetIndex;
           // Update record info text (left side)
           const recInfo = document.querySelector('.record-info');
           if (recInfo) {
             const total = data.total || parseInt(document.querySelector('input[name="total_records"]')?.value || '0', 10) || 0;
             recInfo.innerHTML = `<span class=\"font-bold text-gray-800\">${targetIndex + 1}</span>&nbsp;of&nbsp;<span class=\"font-bold text-gray-800\">${total}</span>`;
           }
           try { updateEditCount(); } catch(e) {}
         }).catch(() => { form.submit(); });
         return false;
         }
         }, true); // Use capture phase to intercept before other handlers

             // Handle form submission
    document.getElementById('json-form').addEventListener('submit', function(e) {
      e.preventDefault();

      // Validate all fields before saving
      if (!validateAllFields()) {
        console.log('Validation failed, preventing form submission');
        return false; // Prevent any further action
      }

      console.log('Validation passed, proceeding with save');

      // Only proceed with save if validation passed
      // Collect the edited data
      const rootElement = document.getElementById('json-editor').children[0];
      console.log('Root element for collection:', rootElement);
      console.log('Root element HTML:', rootElement.outerHTML.substring(0, 200) + '...');

      const editedData = collectData(rootElement);
      console.log('Final collected data:', editedData);
      console.log('Type of collected data:', typeof editedData, Array.isArray(editedData) ? 'array' : 'not array');
      console.log('JSON string preview:', JSON.stringify(editedData, null, 2).substring(0, 500) + '...');

      // Validate that we have a proper object/array
      if (editedData === null || editedData === undefined) {
        showModalMessage('Error', 'Error collecting data. Please check the console for details.');
        return;
      }

      document.getElementById('json_data').value = JSON.stringify(editedData);

      // Check S3 path validity
      const path = document.getElementById('s3_path').value.trim();
      const s3Prefix = /^s3:\/\//i;
      const validExt = /\.(?:json|jsonl|json\.gz|jsonl\.gz)$/i;

      if (!s3Prefix.test(path) || !validExt.test(path)) {
        alert(
          'Please provide a valid S3 path (e.g. s3://my-bucket/path/to/file.json) ' +
          'with one of these extensions: .json, .jsonl, .json.gz, .jsonl.gz'
        );
        return;
      }

      // Show save loader
      showSaveLoaderAndRedirect();

      // Submit the form after a short delay to allow the loader to show
      const form = this;
      setTimeout(() => {
        form.submit();
      }, 100);
    });

         // Toggle JSON don't encrypt preference
         function toggleJsonDontEncrypt() {
         const btn = document.getElementById('jsonDontEncryptToggleBtn');
         if (btn) {
         const isCurrentlyEnabled = btn.classList.contains('selected');
         const newState = !isCurrentlyEnabled;

         if (newState) {
          btn.classList.add('selected');
         } else {
          btn.classList.remove('selected');
         }

         // Update hidden field for form submission
         updateJsonDontEncryptHiddenField();
         }
         }

         // Update hidden field for JSON don't encrypt
         function updateJsonDontEncryptHiddenField() {
         const btn = document.getElementById('jsonDontEncryptToggleBtn');
         const form = document.getElementById('json-form');
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
         document.getElementById('json-form').addEventListener('submit', function() {
         updateJsonDontEncryptHiddenField();
         });

         // Placeholder functions to prevent errors (these features not available in JSON editor)
         window.initializeNotes = function() {
         console.log('Notes not available in JSON editor');
         };

         window.initializeTextEncryption = function() {
         console.log('Text encryption not available in JSON editor');
         };

         // Initialize edit count on page load
         updateEditCount();

      </script>
      {{ s3_browser_styles|safe }}
      {{ s3_browser_modal|safe }}
      {{ s3_browser_script|safe }}
   </body>
</html>
"""

RAW_EDIT_HTML = r"""
<!doctype html>
<html>
   <head>
      <title>Sequoia WorkBench</title>
      <link rel="icon" href="https://www.sequoia.com/wp-content/uploads/2020/03/sequoia-symbol.png" />
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
         .white-theme #s3_path { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
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
         const serverTheme = '{{ theme }}';
         const savedTheme = localStorage.getItem('workbench-theme');
         const currentTheme = savedTheme || serverTheme || 'dark';
         document.documentElement.className = currentTheme + '-theme';
         document.body.className = 'min-h-screen ' + currentTheme + '-theme';
         if (!savedTheme) { localStorage.setItem('workbench-theme', currentTheme); }
         function setTheme(theme) {
           document.documentElement.className = theme + '-theme';
           document.body.className = 'min-h-screen ' + theme + '-theme';
           localStorage.setItem('workbench-theme', theme);
           fetch('/set-theme', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({theme}) });
         }
         function stripOuterQuotes(v) {
           if (!v) return v;
           return v.replace(/^['\"]/,'').replace(/['\"]$/,'');
         }
         function updateModule(module) {
           const moduleField = document.querySelector('input[name=\"module\"]');
           if (moduleField) moduleField.value = module;
           fetch('/set-module', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({module}) });
         }
         function savePathToSession(path) {
           if (path.toLowerCase().startsWith('s3://')) {
             fetch('/set-path', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({path}) });
           }
         }
           // Register custom Monaco themes for better colors
         require.config({ paths: { 'vs': 'https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs' } });
         require(['vs/editor/editor.main'], function() {
         if (window.monaco) {
           monaco.editor.defineTheme('workbench-darcula', {
             base: 'vs-dark', inherit: true,
             rules: [
               { token: '', foreground: 'd4d4d4', background: '1e1e1e' },
               { token: 'comment', foreground: '6a9955' },
               { token: 'keyword', foreground: 'c586c0' },
               { token: 'identifier', foreground: '9cdcfe' },
               { token: 'number', foreground: 'b5cea8' },
               { token: 'string', foreground: 'ce9178' },
               { token: 'type', foreground: '4ec9b0' }
             ],
             colors: {
               'editor.background': '#2b2b2b',
               'editor.foreground': '#a9b7c6',
               'editorLineNumber.foreground': '#606366',
               'editorLineNumber.activeForeground': '#a9b7c6',
               'editorGutter.background': '#2b2b2b',
               'editorCursor.foreground': '#ffffff',
               'editor.selectionBackground': '#214283',
               'editorIndentGuide.background': '#3c3f41',
               'editorIndentGuide.activeBackground': '#606366'
             }
           });
           monaco.editor.defineTheme('workbench-light-intellij', {
             base: 'vs', inherit: true,
             rules: [
               { token: '', foreground: '1f2937', background: 'ffffff' },
               { token: 'comment', foreground: '008000' },
               { token: 'keyword', foreground: '0000ff' },
               { token: 'identifier', foreground: '001080' },
               { token: 'number', foreground: '098658' },
               { token: 'string', foreground: 'a31515' }
             ],
             colors: {
               'editor.background': '#ffffff',
               'editor.foreground': '#1f2328',
               'editorLineNumber.foreground': '#9aa4b2',
               'editorLineNumber.activeForeground': '#111827',
               'editorGutter.background': '#ffffff',
               'editorCursor.foreground': '#111827',
               'editor.selectionBackground': '#cfe8ff',
               'editorIndentGuide.background': '#e5e7eb',
               'editorIndentGuide.activeBackground': '#9ca3af'
             }
           });
         }
         });
      </script>
      <div class="w-full min-h-screen main-container theme-transition p-8">
         <!-- Header Section - Same as JSON/CSV editors -->
         <div class="flex items-center justify-between mb-6">
            <div class="flex items-center space-x-3">
               <a href="{{ url_for('home') }}">
                  <div class="flex items-center">
                     <img src="{{ logo }}" class="h-16 w-auto mr-1" alt="Logo" />
                     <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
                  </div>
               </a>
               <span id="edit-indicator" class="edit-indicator" style="display: none;"></span>
            </div>
            <!-- Right side: Greeting and Theme Toggle -->
            <div class="flex items-center space-x-4">
               <div class="text-right">
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
                     <option value="pink">🌸  Pink</option>
                  </select>
               </div>
            </div>
         </div>
         <!-- S3 Path & Controls -->
         <div class="flex items-center space-x-2 mb-4">
            <div class="flex-1 flex items-center space-x-2">
               <button
                  type="button"
                  class="s3BrowseBtn btn btn-ghost btn-icon"
                  style="width:46px;height:46px;padding:0;font-size:18px;line-height:46px;display:inline-flex;align-items:center;justify-content:center;"
                  title="Browse S3"
                  >🪣️</button>
               <input
                  type="text"
                  id="s3_path"
                  name="s3_path"
                  value="{{ s3_path }}"
                  class="flex-grow border px-4 py-2 text-base theme-transition"
                  style="height: 46px;"
                  onchange="savePathToSession(this.value)"
                  autocomplete="off"
                  />
            </div>
            {% if decryption_module %}
            <div class="flex items-center space-x-2">
               <span class="px-3 py-1 text-sm font-medium theme-transition module-badge">{{ decryption_module }}</span>
            </div>
            {% else %}
            <select id="module-select" name="module" class="border px-4 py-2 text-sm theme-transition" style="font-weight: 500 !important; min-width: 120px; height: 46px;" onchange="updateModule(this.value)">
            <option value="dxp" {{ 'selected' if module == 'dxp' else '' }}>dxp</option>
            <option value="dap" {{ 'selected' if module == 'dap' else '' }}>dap</option>
            <option value="pa" {{ 'selected' if module == 'pa' else '' }}>pa</option>
            </select>
            {% endif %}
            <button id="fileInfoBtn"
               type="button"
               class="btn btn-ghost btn-icon"
               style="height: 46px; width: 46px; position: relative;">
            📋
            <div id="metadata-tooltip" class="metadata-tooltip" style="display: none; position: absolute; bottom: 100%; left: 50%; transform: translateX(-50%); background: #1e293b; color: #e2e8f0; padding: 8px 12px; border: 1px solid #334155; border-radius: 0; font-size: 12px; white-space: nowrap; z-index: 1000; margin-bottom: 8px; box-shadow: 0 4px 12px rgba(0,0,0,0.3); min-width: 180px;">
               <div id="tooltip-content" style="line-height: 1.4;">
                 <div><strong>Size:</strong> <span id="file-size">{{ file_metadata.size }}</span></div>
                 <div><strong>Created:</strong> <span id="created-date">{{ file_metadata.created_date }}</span></div>
                 <div><strong>Modified:</strong> <span id="modified-date">{{ file_metadata.last_modified }}</span></div>
               </div>
               <!-- Chat bubble pointer -->
               <div style="position: absolute; top: 100%; left: 50%; transform: translateX(-50%); width: 0; height: 0; border-left: 8px solid transparent; border-right: 8px solid transparent; border-top: 8px solid #1e293b;"></div>
            </div>
            </button>
            <button id="rawDontEncryptToggleBtn"
               type="button"
               class="btn btn-ghost btn-icon"
               title="Disable encryption for this save"
               onclick="toggleRawDontEncrypt(); return false;"
               style="height: 46px; width: 46px;">
            🔓
            </button>
            <button
               type="submit"
               form="code-save-form"
               class="btn btn-ghost"
               title="Save changes"
               style="height: 46px;">
            💾 Save
            </button>
            <a
               href="{{ url_for('home') }}"
               class="btn btn-ghost btn-icon"
               title="Back to home"
               style="height: 46px; width: 46px;"
               >
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
            <style>
               #rawDontEncryptToggleBtn { height: 46px; width: 46px; }
               /* Hover grey on white theme (match Home) */
               .white-theme #rawDontEncryptToggleBtn:hover:not(:disabled) { background-color: #f1f5f9 !important; border-color: #cbd5e1 !important; }
               /* Persist selected highlight across themes (match Home) */
               #rawDontEncryptToggleBtn.selected,
               .white-theme #rawDontEncryptToggleBtn.selected { background-color: rgba(0, 0, 0, 0.05) !important; border-color: rgba(0, 0, 0, 0.1) !important; }
               .dark-theme #rawDontEncryptToggleBtn.selected { background-color: #334155 !important; border-color: #64748b !important; }
               .pink-theme #rawDontEncryptToggleBtn.selected { background-color: #fce7f3 !important; border-color: #f9a8d4 !important; }
            </style>
         </div>
         <!-- Code Editor Section -->
         <form id="code-save-form" method="post" action="{{ url_for('save_raw') }}" onsubmit="return handleCodeSaveSubmit(event);">
            <input type="hidden" name="s3_path" value="{{ s3_path }}" />
            <input type="hidden" name="module" value="{{ module }}" />
            <input type="hidden" name="decryption_module" value="{{ decryption_module or module }}" />
            <input type="hidden" name="gzipped" value="{{ gzipped }}" />
            <input type="hidden" name="cache_key" value="{{ cache_key }}" />
            <textarea id="code_text" name="code_text" class="hidden-field">{{ code_text | safe }}</textarea>
            <div class="bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 mb-4">
               <div id="editor" style="height: 75vh; min-height: 500px; width: 100%; font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, 'Liberation Mono', 'Courier New', monospace !important; background: transparent; color: inherit; position: relative;">
               </div>
            </div>
         </form>
      </div>
      <script>
         // Define before any use
         const USE_PLAIN_EDITOR = false;

         // Show loading overlay for code editor (pattern from JSON editor)
         function showCodeLoadingOverlay() {
           if (document.getElementById('code-loading-overlay')) return;
           const currentTheme = document.body.className;
           let backgroundColor = '#1e293b';
           let spinnerColor = '#6366f1';
           if (currentTheme.includes('white-theme')) { backgroundColor = '#ffffff'; spinnerColor = '#6366f1'; }
           if (currentTheme.includes('pink-theme')) { backgroundColor = '#ffffff'; spinnerColor = '#ec4899'; }
           const overlay = document.createElement('div');
           overlay.id = 'code-loading-overlay';
           overlay.style.cssText = `position: fixed; top:0; left:0; width:100%; height:100%; background: rgba(0,0,0,0.3); backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px); display:flex; justify-content:center; align-items:center; z-index:9999;`;
           overlay.innerHTML = `
             <div style="text-align:center;">
               <div style="color:white; font-size:18px; font-weight:600; margin-bottom:20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">LOADING</div>
               <div style="width:800px; height:5px; background-color:${currentTheme.includes('dark-theme') ? '#334155' : currentTheme.includes('pink-theme') ? '#fbcfe8' : '#e2e8f0'}; overflow:hidden; position:relative; margin:0 auto;">
                 <div style="position:absolute; top:0; left:0; width:30%; height:100%; background-color:${spinnerColor}; animation: loading-bar 1.5s ease-in-out infinite;"></div>
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

             // Update hidden s3_path field with current visible value
             const visibleS3Path = document.getElementById('s3_path').value;
             const codeForm = document.getElementById('code-save-form');
             const hiddenS3Path = codeForm ? codeForm.querySelector('input[name="s3_path"]') : null;
             if (hiddenS3Path) {
               hiddenS3Path.value = visibleS3Path;
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
           const currentTheme = (localStorage.getItem('workbench-theme') || '{{ theme }}' || 'dark');
           if (themeDropdown) themeDropdown.value = currentTheme;

           // Clean any accidental quotes around inputs
           const s3PathEl = document.getElementById('s3_path');
           if (s3PathEl) s3PathEl.value = stripOuterQuotes(s3PathEl.value || '');

           // Sync hidden s3_path field with visible field on any change
           if (s3PathEl) {
             s3PathEl.addEventListener('input', function() {
               const codeForm = document.getElementById('code-save-form');
               const hiddenS3Path = codeForm ? codeForm.querySelector('input[name="s3_path"]') : null;
               console.log('Input Event - Visible value:', this.value);
               console.log('Input Event - Code form found:', !!codeForm);
               console.log('Input Event - Hidden field found:', !!hiddenS3Path);
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
                            // Custom color themes similar to your screenshot
                              // Build a dynamic theme that matches the page background
                                function applyDynamicTheme(themeName){
                   const isPink = (themeName === 'pink');
                   const isDark = (themeName === 'dark');
                   const bg = isPink ? '#fdf2f8' : (isDark ? '#1e293b' : (themeName === 'white' ? '#f1f5f9' : '#ffffff'));
                   const gutterBg = bg;
                   const fg = isPink ? '#831843' : (isDark ? '#e2e8f0' : '#1e293b');
                   const lineNum = isPink ? '#be185d' : (isDark ? '#94a3b8' : '#64748b');
                   const activeLineNum = isPink ? '#831843' : (isDark ? '#ffffff' : '#111827');
                   const selection = isPink ? '#fbcfe8' : (isDark ? '#334155' : '#cfe8ff');
                   const indentBg = isPink ? '#f9a8d4' : (isDark ? '#334155' : '#e5e7eb');
                   const indentActive = isPink ? '#ec4899' : (isDark ? '#64748b' : '#9ca3af');
                   const themeId = 'workbench-dynamic-theme';
                   monaco.editor.defineTheme(themeId, {
                     base: (isDark ? 'vs-dark' : 'vs'), inherit: true,
                     rules: [],
                     colors: {
                       'editor.background': bg,
                       'editor.foreground': fg,
                       'editorGutter.background': gutterBg,
                       'editorLineNumber.foreground': lineNum,
                       'editorLineNumber.activeForeground': activeLineNum,
                       'editor.selectionBackground': selection,
                       'editorIndentGuide.background': indentBg,
                       'editorIndentGuide.activeBackground': indentActive
                     }
                   });
                   monaco.editor.setTheme(themeId);
                   return themeId;
                 }

                 // Load Monaco
                 require.config({ paths: { 'vs': 'https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs' } });
                 require(['vs/editor/editor.main'], function() {
                   const themeId = applyDynamicTheme(currentTheme);
                   editor = monaco.editor.create(editorDivEl, {
                   value: initialContent,
                   language: mapToMonacoLang(detectedLang),
                   theme: 'workbench-dynamic-theme',
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

                 // Save shortcut
                 editor.addCommand(monaco.KeyMod.CtrlCmd | monaco.KeyCode.KeyS, function(){
                   try { document.getElementById('code-save-form').dispatchEvent(new Event('submit', {cancelable:true})); }
                   catch(e) { handleCodeSaveSubmit(e); }
                 });

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

           // Toggle RAW don't encrypt preference
           function toggleRawDontEncrypt() {
             const btn = document.getElementById('rawDontEncryptToggleBtn');
             if (btn) {
               const isCurrentlyEnabled = btn.classList.contains('selected');
               const newState = !isCurrentlyEnabled;

               if (newState) {
                 btn.classList.add('selected');
               } else {
                 btn.classList.remove('selected');
               }

               // Update hidden field for form submission
               updateRawDontEncryptHiddenField();
             }
           }

           // Update hidden field for RAW don't encrypt
           function updateRawDontEncryptHiddenField() {
             const btn = document.getElementById('rawDontEncryptToggleBtn');
             const form = document.getElementById('code-save-form');
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
           document.getElementById('code-save-form').addEventListener('submit', function() {
             updateRawDontEncryptHiddenField();
           });

           document.getElementById('theme-select').addEventListener('change', function(){
             const t = this.value;
                        if (window.monaco) {
                // Rebuild dynamic theme so background matches page (including pink)
                const isPink = (t === 'pink');
                const isDark = (t === 'dark');
                const bg = isPink ? '#fdf2f8' : (isDark ? '#1e293b' : (t === 'white' ? '#f1f5f9' : '#ffffff'));
                const fg = isPink ? '#831843' : (isDark ? '#e2e8f0' : '#1e293b');
                const themeId = 'workbench-dynamic-theme';
                monaco.editor.defineTheme(themeId, {
                  base: (isDark ? 'vs-dark' : 'vs'), inherit: true,
                  rules: [],
                  colors: {
                    'editor.background': bg,
                    'editor.foreground': fg,
                    'editorGutter.background': bg,
                    'editorLineNumber.foreground': isPink ? '#be185d' : (isDark ? '#94a3b8' : '#64748b'),
                    'editorLineNumber.activeForeground': isPink ? '#831843' : (isDark ? '#ffffff' : '#111827'),
                    'editor.selectionBackground': isPink ? '#fbcfe8' : (isDark ? '#334155' : '#cfe8ff'),
                    'editorIndentGuide.background': isPink ? '#f9a8d4' : (isDark ? '#334155' : '#e5e7eb'),
                    'editorIndentGuide.activeBackground': isPink ? '#ec4899' : (isDark ? '#64748b' : '#9ca3af')
                  }
                });
                monaco.editor.setTheme(themeId);
              }
           });

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

        <!-- File Metadata Script -->
        <script>
           function showMetadataTooltip() {
             const tooltip = document.getElementById('metadata-tooltip');

             if (!tooltip) return;

             // Apply theme-aware styling (matching modal colors exactly)
             const currentTheme = document.body.className;
             let backgroundColor = '#1e293b'; // Default dark theme (like modal)
             let textColor = '#e2e8f0';
             let borderColor = '#334155'; // Default dark theme border (like modal)

             if (currentTheme.includes('white-theme')) {
               backgroundColor = '#f8fafc'; // White theme background (like modal)
               textColor = '#1e293b';
               borderColor = '#e2e8f0'; // White theme border (like modal)
             } else if (currentTheme.includes('pink-theme')) {
               backgroundColor = '#fdf2f8'; // Pink theme background (like modal)
               textColor = '#831843';
               borderColor = '#f9a8d4'; // Pink theme border (like modal)
             }
             // Dark theme uses dark background with light text

             // Update tooltip styling
             tooltip.style.backgroundColor = backgroundColor;
             tooltip.style.color = textColor;
             tooltip.style.border = `1px solid ${borderColor}`;

             // Update pointer color
             const pointer = tooltip.querySelector('div[style*="border-top"]');
             if (pointer) {
               pointer.style.borderTopColor = backgroundColor;
             }

             tooltip.style.display = 'block';
           }

           function hideMetadataTooltip() {
             const tooltip = document.getElementById('metadata-tooltip');
             if (tooltip) {
               tooltip.style.display = 'none';
             }
           }

           // Add hover event listeners
           document.addEventListener('DOMContentLoaded', function() {
             const btn = document.getElementById('fileInfoBtn');
             if (btn) {
               btn.addEventListener('mouseenter', showMetadataTooltip);
               btn.addEventListener('mouseleave', hideMetadataTooltip);
             }
           });
        </script>

        <!-- RAW Don't Encrypt toggle script (self-contained) -->
      <script>
         (function() {
           function setBtnSelected(btn, enabled) {
             if (!btn) return;
             if (enabled) btn.classList.add('selected'); else btn.classList.remove('selected');
           }

           function updateHiddenField() {
             const form = document.getElementById('code-save-form');
             const btn = document.getElementById('rawDontEncryptToggleBtn');
             if (!form || !btn) return;
             const isEnabled = btn.classList.contains('selected');
             const existing = form.querySelector('input[name="dont_encrypt"]');
             if (existing) existing.remove();
             if (isEnabled) {
               const hidden = document.createElement('input');
               hidden.type = 'hidden';
               hidden.name = 'dont_encrypt';
               hidden.value = 'true';
               form.appendChild(hidden);
             }
           }

           function setState(enabled) {
             const btn = document.getElementById('rawDontEncryptToggleBtn');
             setBtnSelected(btn, enabled);
             // Apply inline styles to match Home button exact look
             if (btn) {
               const cls = document.documentElement.className || '';
               if (enabled) {
                 if (cls.includes('white-theme')) { btn.style.backgroundColor = '#f1f5f9'; btn.style.borderColor = '#cbd5e1'; }
                 else if (cls.includes('pink-theme')) { btn.style.backgroundColor = '#fce7f3'; btn.style.borderColor = '#f9a8d4'; }
                 else { btn.style.backgroundColor = 'rgba(255,255,255,0.1)'; btn.style.borderColor = 'rgba(255,255,255,0.2)'; }
               } else {
                 btn.style.backgroundColor = ''; btn.style.borderColor = '';
               }
             }
             // No longer saving decrypt toggle state to localStorage
             updateHiddenField();
           }

           document.addEventListener('DOMContentLoaded', function() {
             const btn = document.getElementById('rawDontEncryptToggleBtn');
             if (!btn) return;
             // Init - no longer loading from localStorage, always start disabled
             let enabled = false;
             setState(enabled);
             // Click handler
             btn.addEventListener('click', function(e) {
               e.preventDefault();
               setState(!btn.classList.contains('selected'));
             });
             // Ensure hidden field is correct on submit
             const form = document.getElementById('code-save-form');
             if (form) {
               form.addEventListener('submit', function() { updateHiddenField(); });
             }
           });
         })();
      </script>
      {{ s3_browser_styles|safe }}
      {{ s3_browser_modal|safe }}
      {{ s3_browser_script|safe }}
   </body>
</html>
"""

CODE_EDIT_HTML = r"""
<!doctype html>
<html>
   <head>
      <title>Sequoia WorkBench</title>
      <link rel="icon" href="https://www.sequoia.com/wp-content/uploads/2020/03/sequoia-symbol.png" />
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
         .white-theme #s3_path { background-color: #f8fafc !important; color: #1e293b !important; border-color: #e2e8f0 !important; }
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
         /* ==================== TERMINAL MODAL STYLES ==================== */
         #terminal-modal { position: fixed; top: 0; left: 0; width: 100%; height: 100%; background-color: rgba(0, 0, 0, 0.5); display: none; align-items: center; justify-content: center; z-index: 10000; }
         #terminal-modal .modal-content { background-color: #ffffff; box-shadow: 0 10px 25px rgba(0, 0, 0, 0.3); display: flex; flex-direction: column; max-width: 90%; max-height: 90%; }
         #terminal-modal .modal-header { display: flex; justify-content: space-between; align-items: center; padding: 1rem; border-bottom: 1px solid #e5e7eb; }
         #terminal-modal .modal-body { padding: 1rem; overflow: auto; }
         #terminal-modal .modal-footer { display: flex; justify-content: flex-end; gap: 0.5rem; padding: 1rem; border-top: 1px solid #e5e7eb; }
         #terminal-modal .close { background: none; border: none; font-size: 1.5rem; cursor: pointer; color: #6b7280; }
         #terminal-modal .close:hover { color: #374151; }
         /* ==================== TERMINAL OUTPUT STYLES ==================== */
         #terminal-output, #terminal-output *, #terminal-output span, #terminal-output div, #terminal-output p, #terminal-output pre, #terminal-output code { font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace !important; font-variant-ligatures: contextual !important; }
         .modal-body #terminal-output, .modal-body #terminal-output * { font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace !important; }
         #terminal-input { width: 100%; background: #0d1117 !important; border: none; color: #ffffff !important; font-weight: bold; font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace !important; font-size: 14px; outline: none; padding: 15px; caret-color: #ffffff !important; box-shadow: none; border-radius: 0; text-align: left; -webkit-tap-highlight-color: transparent; -webkit-appearance: none; -moz-appearance: none; appearance: none; }
         #terminal-output span[style*="color: #00ff00"] { color: #74c0fc !important; }
         #terminal-output span[style*="color: #808080"] { color: #ffffff !important; }
         #terminal-input:focus { outline: none !important; box-shadow: none !important; -webkit-box-shadow: none !important; border-color: transparent !important; background: #0d1117 !important; }
         #terminal-input::selection { background-color: rgba(56, 139, 253, 0.4); }
      </style>
   </head>
   <body class="min-h-screen">
      <script>
         const serverTheme = '{{ theme }}';
         const savedTheme = localStorage.getItem('workbench-theme');
         const currentTheme = savedTheme || serverTheme || 'dark';
         document.documentElement.className = currentTheme + '-theme';
         document.body.className = 'min-h-screen ' + currentTheme + '-theme';
         if (!savedTheme) { localStorage.setItem('workbench-theme', currentTheme); }
         function setTheme(theme) {
           document.documentElement.className = theme + '-theme';
           document.body.className = 'min-h-screen ' + theme + '-theme';
           localStorage.setItem('workbench-theme', theme);
           fetch('/set-theme', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({theme}) });
         }
         function stripOuterQuotes(v) {
           if (!v) return v;
           return v.replace(/^['\"]/,'').replace(/['\"]$/,'');
         }
         function updateModule(module) {
           const moduleField = document.querySelector('input[name=\"module\"]');
           if (moduleField) moduleField.value = module;
           fetch('/set-module', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({module}) });
         }
         function savePathToSession(path) {
           if (path.toLowerCase().startsWith('s3://')) {
             fetch('/set-path', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({path}) });
           }
         }
           // Register custom Monaco themes for better colors
         require.config({ paths: { 'vs': 'https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs' } });
         require(['vs/editor/editor.main'], function() {
         if (window.monaco) {
           monaco.editor.defineTheme('workbench-darcula', {
             base: 'vs-dark', inherit: true,
             rules: [
               { token: '', foreground: 'd4d4d4', background: '1e1e1e' },
               { token: 'comment', foreground: '6a9955' },
               { token: 'keyword', foreground: 'c586c0' },
               { token: 'identifier', foreground: '9cdcfe' },
               { token: 'number', foreground: 'b5cea8' },
               { token: 'string', foreground: 'ce9178' },
               { token: 'type', foreground: '4ec9b0' }
             ],
             colors: {
               'editor.background': '#2b2b2b',
               'editor.foreground': '#a9b7c6',
               'editorLineNumber.foreground': '#606366',
               'editorLineNumber.activeForeground': '#a9b7c6',
               'editorGutter.background': '#2b2b2b',
               'editorCursor.foreground': '#ffffff',
               'editor.selectionBackground': '#214283',
               'editorIndentGuide.background': '#3c3f41',
               'editorIndentGuide.activeBackground': '#606366'
             }
           });
           monaco.editor.defineTheme('workbench-light-intellij', {
             base: 'vs', inherit: true,
             rules: [
               { token: '', foreground: '1f2937', background: 'ffffff' },
               { token: 'comment', foreground: '008000' },
               { token: 'keyword', foreground: '0000ff' },
               { token: 'identifier', foreground: '001080' },
               { token: 'number', foreground: '098658' },
               { token: 'string', foreground: 'a31515' }
             ],
             colors: {
               'editor.background': '#ffffff',
               'editor.foreground': '#1f2328',
               'editorLineNumber.foreground': '#9aa4b2',
               'editorLineNumber.activeForeground': '#111827',
               'editorGutter.background': '#ffffff',
               'editorCursor.foreground': '#111827',
               'editor.selectionBackground': '#cfe8ff',
               'editorIndentGuide.background': '#e5e7eb',
               'editorIndentGuide.activeBackground': '#9ca3af'
             }
           });
         }
         });
      </script>
      <div class="w-full min-h-screen main-container theme-transition p-8">
         <!-- Header Section - Same as JSON/CSV editors -->
         <div class="flex items-center justify-between mb-6">
            <div class="flex items-center space-x-3">
               <a href="{{ url_for('home') }}">
                  <div class="flex items-center">
                     <img src="{{ logo }}" class="h-16 w-auto mr-1" alt="Logo" />
                     <h1 class="text-3xl font-bold">🖥️&nbsp;WorkBench</h1>
                  </div>
               </a>
               <span id="edit-indicator" class="edit-indicator" style="display: none;"></span>
            </div>
            <!-- Right side: Greeting and Theme Toggle -->
            <div class="flex items-center space-x-4">
               <div class="text-right">
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
                     <option value="pink">🌸  Pink</option>
                  </select>
               </div>
            </div>
         </div>
         <!-- S3 Path & Controls -->
         <div class="flex items-center space-x-2 mb-4">
            <div class="flex-1 flex items-center space-x-2">
               <button
                  type="button"
                  class="s3BrowseBtn btn btn-ghost btn-icon"
                  style="width:46px;height:46px;padding:0;font-size:18px;line-height:46px;display:inline-flex;align-items:center;justify-content:center;"
                  title="Browse S3"
                  >🪣️</button>
               <input
                  type="text"
                  id="s3_path"
                  name="s3_path"
                  value="{{ s3_path }}"
                  class="flex-grow border px-4 py-2 text-base theme-transition"
                  style="height: 46px;"
                  onchange="savePathToSession(this.value)"
                  autocomplete="off"
                  />
               <button type="button" id="code-run-button" class="btn btn-ghost" title="Run Code" aria-label="Run Code" style="display: none; width:46px;height:46px;padding:0;">
                  <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                     <polygon points="5 3 19 12 5 21 5 3"></polygon>
                  </svg>
               </button>
               <button type="button" id="code-pause-button" class="btn btn-warning" title="Pause" aria-label="Pause" style="display: none; width:46px;height:46px;padding:0;">
                  <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                     <rect x="6" y="4" width="4" height="16"></rect>
                     <rect x="14" y="4" width="4" height="16"></rect>
                  </svg>
               </button>
               <button type="button" id="code-stop-button" class="btn btn-danger" title="Stop" aria-label="Stop" style="display: none; width:46px;height:46px;padding:0;">
                  <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                     <rect x="3" y="3" width="18" height="18" rx="2" ry="2"></rect>
                  </svg>
               </button>
            </div>
            <button
               type="submit"
               form="code-save-form"
               class="btn btn-ghost"
               title="Save changes"
               style="height: 46px;">
            💾 Save
            </button>
            <a
               href="{{ url_for('home') }}"
               class="btn btn-ghost btn-icon"
               title="Back to home"
               style="height: 46px; width: 46px;"
               >
            ←
            </a>
            <button type="button" id="fullscreen-btn" class="btn btn-ghost" title="Fullscreen" aria-label="Fullscreen" style="display:inline-flex;align-items:center;justify-content:center;width:46px;height:46px;padding:0;">
               <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                  <polyline points="15 3 21 3 21 9"></polyline>
                  <polyline points="9 21 3 21 3 15"></polyline>
                  <line x1="21" y1="3" x2="14" y2="10"></line>
                  <line x1="3" y1="21" x2="10" y2="14"></line>
               </svg>
            </button>
         </div>
         <!-- Code Editor Section -->
         <form id="code-save-form" method="post" action="{{ url_for('save_code') }}" onsubmit="return handleCodeSaveSubmit(event);">
            <input type="hidden" name="s3_path" value="{{ s3_path }}" />
            <textarea id="code_text" name="code_text" class="hidden-field">{{ code_text | safe }}</textarea>
            <div class="bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 mb-4">
               <div id="editor" style="height: 75vh; min-height: 500px; width: 100%; font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, 'Liberation Mono', 'Courier New', monospace !important; background: transparent; color: inherit; position: relative;">
               </div>
            </div>
         </form>
      </div>
      <!-- Terminal Output Modal -->
      <div id="terminal-modal" class="modal" style="display: none; backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px);">
         <div class="modal-content" style="width: 90%; max-width: 1200px; height: 80%; max-height: 600px; border: none; box-shadow: none; background: transparent;">
            <div class="modal-body" style="flex: 1; overflow: hidden; display: flex; flex-direction: column;">
               <div id="terminal-output" style="flex: 1; background: #0d1117; color: #ffffff; font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace !important; padding: 15px; overflow-y: auto; white-space: pre-wrap; font-size: 14px; line-height: 1.5; margin-bottom: 0; border-radius: 0;"></div>
               <div style="padding: 0; margin: 0;">
                  <style>
                     #terminal-input {
                     width: 100%;
                     background: #0d1117 !important;
                     border: none;
                     color: #ffffff;
                     font-weight: bold;
                     font-family: 'Cascadia Code', 'Fira Code', Consolas, 'Liberation Mono', 'Courier New', ui-monospace, SFMono-Regular, Menlo, Monaco, monospace !important;
                     font-size: 14px;
                     outline: none;
                     padding: 15px;
                     caret-color: #00ff00;
                     box-shadow: none;
                     border-radius: 0;
                     text-align: left;
                     -webkit-tap-highlight-color: transparent;
                     -webkit-appearance: none;
                     -moz-appearance: none;
                     appearance: none;
                     }

                     #terminal-input:focus {
                     outline: none !important;
                     box-shadow: none !important;
                     -webkit-box-shadow: none !important;
                     border-color: transparent !important;
                     background: #0d1117 !important;
                     }
                     #terminal-input::selection {
                     background-color: rgba(56, 139, 253, 0.4);
                     }
                  </style>
                  <input type="text" id="terminal-input" 
                  </style>
               </div>
            </div>
         </div>
      </div>
      <script>
         // Define before any use
         function handleCodeSaveSubmit(e) { /* placeholder; real implementation below */ return false; }
         const USE_PLAIN_EDITOR = false;

         // Show loading overlay for code editor (pattern from JSON editor)
         function showCodeLoadingOverlay() {
           if (document.getElementById('code-loading-overlay')) return;
           const currentTheme = document.body.className;
           let backgroundColor = '#1e293b';
           let spinnerColor = '#6366f1';
           if (currentTheme.includes('white-theme')) { backgroundColor = '#ffffff'; spinnerColor = '#6366f1'; }
           if (currentTheme.includes('pink-theme')) { backgroundColor = '#ffffff'; spinnerColor = '#ec4899'; }
           const overlay = document.createElement('div');
           overlay.id = 'code-loading-overlay';
           overlay.style.cssText = `position: fixed; top:0; left:0; width:100%; height:100%; background: rgba(0,0,0,0.3); backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px); display:flex; justify-content:center; align-items:center; z-index:9999;`;
           overlay.innerHTML = `
             <div style="text-align:center;">
               <div style="color:white; font-size:18px; font-weight:600; margin-bottom:20px; -webkit-font-smoothing: antialiased; -moz-osx-font-smoothing: grayscale;">LOADING</div>
               <div style="width:800px; height:5px; background-color:${currentTheme.includes('dark-theme') ? '#334155' : currentTheme.includes('pink-theme') ? '#fbcfe8' : '#e2e8f0'}; overflow:hidden; position:relative; margin:0 auto;">
                 <div style="position:absolute; top:0; left:0; width:30%; height:100%; background-color:${spinnerColor}; animation: loading-bar 1.5s ease-in-out infinite;"></div>
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

             // Update hidden s3_path field with current visible value
             const visibleS3Path = document.getElementById('s3_path').value;
             const codeForm = document.getElementById('code-save-form');
             const hiddenS3Path = codeForm ? codeForm.querySelector('input[name="s3_path"]') : null;
             if (hiddenS3Path) hiddenS3Path.value = visibleS3Path;

             const hidden = document.getElementById('code_text');
             const value = (typeof editor !== 'undefined' && editor) ? editor.getValue() : hidden.value;
             const normalized = (value || '').replace(/\r\n/g, '\n').replace(/\r/g, '\n');
             hidden.value = normalized;

             // Simple form submit - no chunking
             document.getElementById('code-save-form').submit();
           } catch (err) {
             console.error('Save submit failed', err);
             try { if (typeof showModalMessage === 'function') { showModalMessage('Save', 'Save failed: ' + (err && err.message ? err.message : err)); } } catch(_) {}
             if (btn) { btn.disabled = false; btn.textContent = 'Save'; }
           }
           return false;
         }

         let editor;
         (function(){
           const themeDropdown = document.getElementById('theme-select');
           const currentTheme = (localStorage.getItem('workbench-theme') || '{{ theme }}' || 'dark');
           if (themeDropdown) themeDropdown.value = currentTheme;

           // Clean any accidental quotes around inputs
           const s3PathEl = document.getElementById('s3_path');
           if (s3PathEl) s3PathEl.value = stripOuterQuotes(s3PathEl.value || '');

           // Sync hidden s3_path field with visible field on any change
           if (s3PathEl) {
             s3PathEl.addEventListener('input', function() {
               const codeForm = document.getElementById('code-save-form');
               const hiddenS3Path = codeForm ? codeForm.querySelector('input[name="s3_path"]') : null;
               console.log('Input Event - Visible value:', this.value);
               console.log('Input Event - Code form found:', !!codeForm);
               console.log('Input Event - Hidden field found:', !!hiddenS3Path);
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
                            // Custom color themes similar to your screenshot
                              // Build a dynamic theme that matches the page background
                                function applyDynamicTheme(themeName){
                   const isPink = (themeName === 'pink');
                   const isDark = (themeName === 'dark');
                   const bg = isPink ? '#fdf2f8' : (isDark ? '#1e293b' : (themeName === 'white' ? '#f1f5f9' : '#ffffff'));
                   const gutterBg = bg;
                   const fg = isPink ? '#831843' : (isDark ? '#e2e8f0' : '#1e293b');
                   const lineNum = isPink ? '#be185d' : (isDark ? '#94a3b8' : '#64748b');
                   const activeLineNum = isPink ? '#831843' : (isDark ? '#ffffff' : '#111827');
                   const selection = isPink ? '#fbcfe8' : (isDark ? '#334155' : '#cfe8ff');
                   const indentBg = isPink ? '#f9a8d4' : (isDark ? '#334155' : '#e5e7eb');
                   const indentActive = isPink ? '#ec4899' : (isDark ? '#64748b' : '#9ca3af');
                   const themeId = 'workbench-dynamic-theme';
                   monaco.editor.defineTheme(themeId, {
                     base: (isDark ? 'vs-dark' : 'vs'), inherit: true,
                     rules: [],
                     colors: {
                       'editor.background': bg,
                       'editor.foreground': fg,
                       'editorGutter.background': gutterBg,
                       'editorLineNumber.foreground': lineNum,
                       'editorLineNumber.activeForeground': activeLineNum,
                       'editor.selectionBackground': selection,
                       'editorIndentGuide.background': indentBg,
                       'editorIndentGuide.activeBackground': indentActive
                     }
                   });
                   monaco.editor.setTheme(themeId);
                   return themeId;
                 }

                 // Load Monaco
                 require.config({ paths: { 'vs': 'https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs' } });
                 require(['vs/editor/editor.main'], function() {
                   const themeId = applyDynamicTheme(currentTheme);
                   editor = monaco.editor.create(editorDivEl, {
                   value: initialContent,
                   language: mapToMonacoLang(detectedLang),
                   theme: 'workbench-dynamic-theme',
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

                 // Save shortcut
                 editor.addCommand(monaco.KeyMod.CtrlCmd | monaco.KeyCode.KeyS, function(){
                   try { document.getElementById('code-save-form').dispatchEvent(new Event('submit', {cancelable:true})); }
                   catch(e) { handleCodeSaveSubmit(e); }
                 });

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

           document.getElementById('theme-select').addEventListener('change', function(){
             const t = this.value;
                        if (window.monaco) {
                // Rebuild dynamic theme so background matches page (including pink)
                const isPink = (t === 'pink');
                const isDark = (t === 'dark');
                const bg = isPink ? '#fdf2f8' : (isDark ? '#1e293b' : (t === 'white' ? '#f1f5f9' : '#ffffff'));
                const fg = isPink ? '#831843' : (isDark ? '#e2e8f0' : '#1e293b');
                const themeId = 'workbench-dynamic-theme';
                monaco.editor.defineTheme(themeId, {
                  base: (isDark ? 'vs-dark' : 'vs'), inherit: true,
                  rules: [],
                  colors: {
                    'editor.background': bg,
                    'editor.foreground': fg,
                    'editorGutter.background': bg,
                    'editorLineNumber.foreground': isPink ? '#be185d' : (isDark ? '#94a3b8' : '#64748b'),
                    'editorLineNumber.activeForeground': isPink ? '#831843' : (isDark ? '#ffffff' : '#111827'),
                    'editor.selectionBackground': isPink ? '#fbcfe8' : (isDark ? '#334155' : '#cfe8ff'),
                    'editorIndentGuide.background': isPink ? '#f9a8d4' : (isDark ? '#334155' : '#e5e7eb'),
                    'editorIndentGuide.activeBackground': isPink ? '#ec4899' : (isDark ? '#64748b' : '#9ca3af')
                  }
                });
                monaco.editor.setTheme(themeId);
              }
           });

           // Code execution functionality
           let currentSessionId = null;
           let outputStreaming = false;

           // Show/hide run button based on file type
           function updateRunButton() {
             const runBtn = document.getElementById('code-run-button');
             const pauseBtn = document.getElementById('code-pause-button');
             const stopBtn = document.getElementById('code-stop-button');

             // Use the actual file path passed from server for detection
             const actualFilePath = '{{ actual_file_path }}';
             const fileExt = actualFilePath.toLowerCase().split('.').pop();

             console.log('updateRunButton called:', { actualFilePath, fileExt, runBtn: !!runBtn });

             if (fileExt === 'py' || fileExt === 'java') {
               runBtn.style.display = 'inline-flex';
               pauseBtn.style.display = 'none';
               stopBtn.style.display = 'none';
               console.log('Run button shown for:', fileExt);
             } else {
               runBtn.style.display = 'none';
               pauseBtn.style.display = 'none';
               stopBtn.style.display = 'none';
               console.log('Run button hidden for:', fileExt);
             }
           }

           // Initialize run button visibility
           updateRunButton();
           document.getElementById('s3_path').addEventListener('input', updateRunButton);

           // Run button click handler
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

         })();
      </script>
      {{ s3_browser_styles|safe }}
      {{ s3_browser_modal|safe }}
      {{ s3_browser_script|safe }}
   </body>
</html>
"""


## END HTML


## DEFINITION

@app.before_request
def _log_request_start():
    try:
        if request.path == "/" and request.method == "POST":
            act = request.form.get("action", "unknown")
            DXP_LOGGER.info(f"POST / ({act}) started")
        elif request.path != "/":
            DXP_LOGGER.info(f"{request.method} {request.path} started")
    except Exception as e:
        logger.debug(f"Request logging failed: {e}")


@app.after_request
def _log_request_end(response):
    try:
        if request.path == "/" and request.method == "POST":
            act = request.form.get("action", "unknown")
            DXP_LOGGER.info(f"POST / ({act}) completed with {response.status_code}")
        elif request.path != "/":
            DXP_LOGGER.info(f"{request.method} {request.path} completed with {response.status_code}")
    except Exception as e:
        logger.debug(f"Response logging failed: {e}")
    return response


def _modal_redirect(message: str, title: str = "Error"):
    """Return a small HTML page that stores a modal error then redirects to home."""
    try:
        msg_json = json.dumps(message)
    except Exception:
        msg_json = json.dumps(str(message))
    # Using localStorage key consumed by client JS to show the modal
    html = (
        f"""
        <script>
          (function(){{
            try {{ localStorage.setItem('workbench-pending-modal-error', {msg_json}); }} catch(e) {{}}
            window.location = '{url_for('home')}';
          }})();
        </script>
        """
    )
    return html, 200, {"Content-Type": "text/html"}


def server_log(section: str, **fields):
    try:
        titles = {
            'REQUEST': 'Request',
            'RESPONSE': 'Response',
            'HOME_GET': 'Home Page',
            'FILE_OPEN_START': 'Open File',
            'Upload - Encrypt': 'Upload - Encrypt',
            'Upload - Encrypt Start': 'Upload - Encrypt Start',
            'Upload - Encrypt Completed': 'Upload - Encrypt Completed',
            'S3 Upload Start': 'S3 Upload Start',
            'S3 Upload Done': 'S3 Upload Done',
            'Upload (No Encryption)': 'Upload (No Encryption)',
            'Upload (Invalid S3 Path)': 'Upload (Invalid S3 Path)',
            'Upload (No Local File)': 'Upload (No Local File)',
            'Upload (Type Mismatch)': 'Upload (Type Mismatch)',
            'New File Upload': 'New File Upload',
            'File Type Detection': 'File Type Detection',
            'Save JSON': 'Save JSON',
            'Save JSON Completed': 'Save JSON Completed',
            'Save Code': 'Save Code',
            'Download': 'Download',
            'Home Reset': 'Home Reset',
            'Returning from Upload - Encrypt': 'Returning from Upload - Encrypt',
            # Added descriptive sections
            'Environment Changed': 'Environment Changed',
            'Clearing Caches': 'Clearing Caches',
            'Caches Cleared': 'Caches Cleared',
            'UI Path Cleared': 'UI Path Cleared',
            'Browse S3': 'Browse S3',
            'Browse S3 - Cache Hit': 'Browse S3 - Cache Hit',
            'Browse S3 - Fetch Complete': 'Browse S3 - Fetch Complete',
            'S3 Smart Cache': 'S3 Smart Cache',
            'S3 Smart Cache - Priority Path': 'S3 Smart Cache - Priority Path',
            'S3 Smart Cache - Enqueue': 'S3 Smart Cache - Enqueue',
            'S3 Smart Cache - Path Cached': 'S3 Smart Cache - Path Cached',
            'S3 Smart Cache - Complete': 'S3 Smart Cache - Complete',
        }
        title = titles.get(section, section)
        parts = [title]
        for k, v in fields.items():
            key = k.replace('_', ' ').title()
            parts.append(f"{key}: {v}")
        logging.getLogger('DXPUtility').info(" - ".join(parts))
    except Exception:
        pass


def get_big_time_display():
    """Get current time in big display format with greeting and day"""
    try:
        now = datetime.now()
        hour = now.hour
        day_name = now.strftime("%A")  # e.g., "Monday"
        date_str = now.strftime("%d")  # e.g., "25"
        month_str = now.strftime("%b")  # e.g., "Aug"

        # Add ordinal suffix to day
        day = now.day
        if 4 <= day <= 20 or 24 <= day <= 30:
            suffix = "th"
        else:
            suffix = ["st", "nd", "rd"][day % 10 - 1]

        # Get random greeting
        greetings = [
            "Hello",
            "Howdy",
            "Namaste",
            "Hi there",
            "Hey",
            "Greetings",
            "Welcome",
            "Salutations"
        ]
        greeting = random.choice(greetings)

        # Get username (you can customize this)
        username = "Amar"

        return {
            'day_date': f"{day_name}, {date_str}{suffix} {month_str}",
            'big_time': now.strftime("%I:%M %p")  # e.g., "01:18 AM"
        }
    except Exception as e:
        logger.error(f"Error getting big time display: {e}")
        return {
            'day_date': "Monday, 1st Jan",
            'big_time': "12:00 AM"
        }


def get_user_greeting():
    """Get personalized greeting based on username and time of day"""
    try:
        # Get home directory path
        home_dir = os.path.expanduser("~")
        # Extract username from path (e.g., /Users/amar.kumar -> amar.kumar)
        username = os.path.basename(home_dir)

        # Process username: remove numbers and split by dot
        # e.g., amar1.kumar -> amar.kumar -> Amar
        username_cleaned = re.sub(r'\d+', '', username)  # Remove all digits
        name_parts = username_cleaned.split('.')
        first_name = name_parts[0].capitalize() if name_parts else "User"

        # Get current hour to determine greeting
        current_hour = datetime.now().hour

        if 5 <= current_hour < 12:
            greeting = "Good Morning"
        elif 12 <= current_hour < 17:
            greeting = "Good Afternoon"
        elif 17 <= current_hour < 22:
            greeting = "Good Evening"
        else:
            greeting = "Good Night"

        return f"{greeting}, {first_name}"
    except Exception as e:
        logger.error(f"Error getting user greeting: {e}")
        return "Welcome"


def get_witty_message():
    """Get a short witty message with Bangalore flair."""
    try:
        now = datetime.now()
        day = now.weekday()  # 0=Monday, 6=Sunday
        hour = now.hour

        # Short, punchy messages based on time and context
        if day in [5, 6]:  # Weekend
            messages = [
                "Weekend vibes! 🎉",
                "Sofa hackathon time! 💻",
                "Weekend chill mode! 😎"
            ]
        elif 12 <= hour < 14:  # Lunch time
            messages = [
                "Lunch walk time! 🚶‍♂️",
                "Dodge those potholes! 🕳️",
                "Valence Tech Park stroll! 🌳"
            ]
        elif hour < 12:  # Morning
            messages = [
                "Morning chai time! ☕",
                "Early data dive! 📊",
                "Fresh start! 🌅"
            ]
        elif hour < 17:  # Afternoon
            messages = [
                "Afternoon grind! 💪",
                "Code shuffle time! ⌨️",
                "Mid-day sprint! 🏃‍♂️"
            ]
        else:  # Evening
            messages = [
                "Evening wrap-up! 🌆",
                "Final commit time! 💾",
                "Late-night deploy! 🚀"
            ]

        return random.choice(messages)

    except Exception as e:
        logger.error(f"Error getting witty message: {e}")
        return random.choice([
            "Bangalore traffic! 🚦",
            "Chai first! ☕️"
        ])


def clear_boto3_cache():
    """Clear boto3 internal caches to force new session creation"""
    import boto3
    # Clear the default session
    boto3.DEFAULT_SESSION = None
    # Clear any cached sessions in boto3
    if hasattr(boto3, '_get_default_session'):
        boto3._get_default_session.cache_clear() if hasattr(boto3._get_default_session, 'cache_clear') else None


def get_fresh_s3_client():
    """Get a fresh S3 client that uses current AWS_PROFILE"""
    import boto3
    # Create a new session to ensure fresh credentials
    session = boto3.Session(profile_name=os.environ.get('AWS_PROFILE', 'dev'))
    return session.client('s3', verify=False)


def detect_delimiter(text: str) -> str:
    if "\u0001" in text:
        return "\u0001"
    try:
        return csv.Sniffer().sniff(text).delimiter
    except csv.Error:
        return ","


def parse_json_or_jsonl(text: str):
    """Parse JSON or JSONL content, return data and format type"""
    text = text.strip()

    if not text:
        raise ValueError("Empty file content")

    # Try standard JSON first
    try:
        parsed = json.loads(text)
        if isinstance(parsed, list):
            logger.info(f"Successfully parsed JSON array with {len(parsed)} items")
            return parsed, "json-array"
        elif isinstance(parsed, dict):
            logger.info(f"Successfully parsed JSON object")
            # Wrap single object in array for consistent handling
            return [parsed], "json-object"
        else:
            # Handle other JSON types (string, number, boolean, null)
            logger.info(f"Successfully parsed JSON primitive: {type(parsed)}")
            return [{"value": parsed}], "json-primitive"
    except JSONDecodeError as e:
        logger.info(f"Not valid JSON, trying JSONL. Error: {e}")
        # Try JSONL format - parse each line separately
        lines = text.strip().splitlines()
        objects = []
        valid_lines = 0
        errors = []

        for i, line in enumerate(lines):
            line = line.strip()
            if not line:  # Skip empty lines
                continue
            try:
                obj = json.loads(line)
                objects.append(obj)
                valid_lines += 1
            except JSONDecodeError as e:
                error_msg = f"Line {i + 1}: {repr(line[:50])}... Error: {e}"
                logger.warning(f"Failed to parse JSONL {error_msg}")
                errors.append(error_msg)
                continue

        if objects:
            logger.info(
                f"Successfully parsed {len(objects)} JSONL records from {len(lines)} lines ({valid_lines} valid)")
            if errors and len(errors) < 10:
                logger.warning(f"JSONL parse errors: {errors}")
            return objects, "jsonl"
        else:
            error_detail = "\n".join(errors[:5]) if errors else "No valid JSON lines found"
            raise ValueError(f"Could not parse as JSON array, object, or JSONL. Errors:\n{error_detail}")


def cleanup_temp_files():
    """Clean up temporary files from LOCAL_UPLOADS"""
    try:
        for upload_id, file_path in list(LOCAL_UPLOADS.items()):
            try:
                if os.path.exists(file_path):
                    os.unlink(file_path)
                    logger.info(f"Cleaned up temp file: {file_path}")
            except Exception as e:
                logger.warning(f"Failed to clean up temp file {file_path}: {e}")
        LOCAL_UPLOADS.clear()
    except Exception as e:
        logger.error(f"Error during temp file cleanup: {e}")


def download_file():
    # Extract parameters
    path = request.form.get("path") or request.form.get("s3_path", "").strip()
    module = request.form.get("module", "dxp")

    if not path:
        logger.error("No path provided for download")
        msg = "No file path provided for download"
        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }})();
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )

    gz = path.lower().endswith(".gz")
    raw_del = request.form.get("delim", "")

    # Properly detect file type
    path_lower = path.lower()
    if path_lower.endswith((".json", ".json.gz")):
        ft = "json"
    elif path_lower.endswith((".jsonl", ".jsonl.gz")):
        ft = "jsonl"
    elif path_lower.endswith((".xlsx", ".xls")):
        ft = "excel"
    elif path_lower.endswith((".pdf")):
        ft = "pdf"
    elif path_lower.endswith((".docx", ".docs")):
        ft = "doc"
    elif path_lower.endswith(
            (".py", ".html", ".htm", ".js", ".go", ".md", ".xml", ".css", ".sql", ".sh", ".bash", ".yaml", ".yml",
             ".toml", ".ini", ".conf", ".cfg", ".txt", ".log")):
        ft = "text"
    elif path_lower.endswith((".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tiff", ".webp", ".svg")):
        ft = "image"
    elif path_lower.endswith((".mp4", ".avi", ".mov", ".wmv", ".flv", ".webm", ".mkv")):
        ft = "video"
    elif path_lower.endswith((".mp3", ".wav", ".flac", ".aac", ".ogg", ".wma")):
        ft = "audio"
    elif path_lower.endswith((".csv", ".csv.gz")):
        ft = "csv"
    elif path_lower.endswith((".zip", ".rar", ".7z", ".tar", ".bz2")):
        ft = "archive"
    elif path_lower.endswith(".gz"):
        ft = "archive"
    else:
        ft = "binary"

    count = request.form.get("download_count", "All")
    server_log("Download", Source=path)
    logger.info(f"Download requested - Count: {count}, Module: {module}, Type: {ft}")
    logger.info(f"Module for download operation: {module}")

    # Check cache first to get format info
    upload_id = session.get("upload_id")
    cache_key = f"{path}:{module}:{upload_id or 'no-upload'}"

    # Try to get format from cache
    cached_format = None
    if cache_key in JSON_DATA_CACHE:
        _, cached_format = JSON_DATA_CACHE[cache_key]
        logger.info(f"Found cached format: {cached_format}")

    # Read source data
    if upload_id and upload_id in LOCAL_UPLOADS:
        try:
            with open(LOCAL_UPLOADS[upload_id], "rb") as f:
                raw_bytes = f.read()
            # Decrypt if needed
            if raw_bytes.startswith(b"ENC"):
                crypto_api = get_cached_crypto_api(module, "download_decrypt")
                raw_bytes = crypto_api.decrypt(raw_bytes)
            # Decompress if gzipped
            if gz:
                try:
                    raw_bytes = gzip.decompress(raw_bytes)
                except:
                    pass

            # Try to decode as text for text-based files
            try:
                text = raw_bytes.decode("utf-8")
                logger.debug(f"Read {len(text)} chars from local upload")
            except UnicodeDecodeError:
                # Binary file - keep as bytes
                text = None
                logger.debug(f"Read {len(raw_bytes)} bytes from local upload (binary file)")
        except Exception as e:
            logger.error(f"Error reading local upload: {e}")
            msg = f"Error reading uploaded file: {str(e)}"
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                        window.location = '{url_for('home')}';
                      }})();
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )
    else:
        # Read from S3
        try:
            logger.info(f"Reading S3 key {path} using module: {module}")
            raw = S3Utils(verify=False).read_key(path, utf_decode=False, module=module)

            # Decrypt if needed
            if isinstance(raw, (bytes, bytearray)) and raw.startswith(b"ENC"):
                logger.info(f"Decrypting file using module: {module}")
                logger.info(f"CRYPTO DEBUG - Environment: {env}, AWS_PROFILE: {os.environ.get('AWS_PROFILE')}")
                logger.info(f"CRYPTO DEBUG - About to create CryptoAPI instance for module: {module}")
                crypto_api = get_cached_crypto_api(module, "crypt_operation")
                logger.info(f"CRYPTO DEBUG - CryptoAPI instance created successfully for module: {module}")
                raw = crypto_api.decrypt(raw)
                logger.info(f"CRYPTO DEBUG - Decryption completed successfully")

            # Decompress if gzipped
            if gz:
                try:
                    raw = gzip.decompress(raw)
                except:
                    pass  # Not actually gzipped

            # Try to convert to text for text-based files
            try:
                text = raw.decode("utf-8") if isinstance(raw, (bytes, bytearray)) else raw
                logger.debug(f"Read {len(text)} chars from S3 path {path}")
            except UnicodeDecodeError:
                # Binary file - keep as bytes
                text = None
                raw_bytes = raw if isinstance(raw, (bytes, bytearray)) else str(raw).encode("utf-8")
                logger.debug(f"Read {len(raw_bytes)} bytes from S3 path {path} (binary file)")
        except Exception as e:
            from botocore.exceptions import ClientError
            logger.error(f"Error reading S3 file: {e}")
            try:
                DXP_LOGGER.error(f"Download Error - {str(e)}")
            except Exception:
                pass

            # Build user-facing message
            msg = None
            if isinstance(e, ClientError):
                error_code = e.response.get('Error', {}).get('Code', 'Unknown')
                error_message = e.response.get('Error', {}).get('Message', 'Unknown error')
                if any(k in (error_code or '').lower() for k in ['token', 'expired', 'invalid']) or any(
                        k in (error_message or '').lower() for k in ['token', 'expired', 'invalid']):
                    msg = f"AWS Token Expired: {error_code} - {error_message}\n\nPlease refresh your AWS token and try again."
            if not msg:
                msg = f"Error reading file from S3: {str(e)}"

            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                        window.location = '{url_for('home')}';
                      }})();
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )

    # Prepare filename
    base = os.path.basename(path)
    root, ext = os.path.splitext(base)
    if gz and ext == ".gz":
        root, inner_ext = os.path.splitext(root)
        # Preserve the original extension (json or jsonl)
        if inner_ext == ".jsonl":
            ft = "jsonl"

    # Check if it's a JSONL file based on extension
    is_jsonl_file = path.lower().endswith((".jsonl", ".jsonl.gz"))

    # Set correct file type for JSONL
    if is_jsonl_file:
        ft = "jsonl"

    # For binary files, preserve the original extension
    if ft in ["excel", "pdf", "text", "image", "video", "audio", "archive", "binary", "doc"]:
        filename = base  # Use original filename
    else:
        filename = f"{root}.{ft}"

    # Slice and serialize
    if ft == "json" or ft == "jsonl":
        try:
            data_obj, json_format = parse_json_or_jsonl(text)

            # Use cached format if available
            if cached_format:
                json_format = cached_format
                logger.info(f"Using cached format: {json_format}")

            logger.info(f"Format for download: {json_format}")

        except ValueError as ve:
            logger.error(f"Download validation error: {ve}")
            msg = f"Download failed: {str(ve)}"
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                        window.location = '{url_for('home')}';
                      }})();
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )

        # For JSON objects, ignore count and download as-is
        if json_format == "json-object":
            # Single object - unwrap from array wrapper and download as object
            payload = json.dumps(data_obj[0], indent=2).encode("utf-8")
            logger.info(f"Downloading as JSON object (ignoring count parameter)")
        elif json_format == "jsonl" or is_jsonl_file:
            # JSONL format - apply count if specified
            if isinstance(data_obj, list) and count.isdigit():
                data_obj = data_obj[: int(count)]
            # Output as JSONL - one object per line, no indentation
            lines = [json.dumps(obj, separators=(',', ':')) for obj in data_obj]
            payload = '\n'.join(lines).encode("utf-8")
            logger.info(f"Downloading as JSONL with {len(data_obj)} lines")
        else:
            # JSON array - apply count if specified
            if isinstance(data_obj, list) and count.isdigit():
                data_obj = data_obj[: int(count)]
            # Output as regular JSON array with indentation
            payload = json.dumps(data_obj, indent=2).encode("utf-8")
            logger.info(f"Downloading as JSON array with {len(data_obj)} items")

        mime = "application/json"
    elif ft == "csv":
        # CSV handling
        try:
            sep = detect_delimiter(text[:2048])
            # Read all fields as strings to avoid numeric coercion (e.g., 1234 -> 1234.0)
            df = pd.read_csv(io.StringIO(text), sep=sep, dtype=str, keep_default_na=False, na_filter=False)
            if count.isdigit():
                df = df.head(int(count))
            buf = io.StringIO()
            # Always use comma when downloading CSV
            df.to_csv(buf, index=False, sep=',')
            payload = buf.getvalue().encode("utf-8")
            mime = "text/csv"
        except Exception as e:
            logger.warning(f"CSV parse failed, falling back to raw text download: {e}")
            payload = (text or '').encode('utf-8')
            mime = "text/plain"
    else:
        # Binary file handling (Excel, PDF, etc.) - download as-is
        if text is None:
            # Binary file - use raw bytes
            if upload_id and upload_id in LOCAL_UPLOADS:
                payload = raw_bytes
            else:
                payload = raw_bytes if 'raw_bytes' in locals() else raw
        else:
            # Text file that's not JSON/CSV - treat as plain text
            payload = text.encode("utf-8")

        # Set appropriate MIME type
        if ft == "excel":
            mime = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
        elif ft == "pdf":
            mime = "application/pdf"
        elif ft == "doc":
            mime = "application/vnd.openxmlformats-officedocument.wordprocessingml.document"
        elif ft == "text":
            mime = "text/plain"
        elif ft == "image":
            # Set appropriate image MIME type based on extension
            if path_lower.endswith(".jpg") or path_lower.endswith(".jpeg"):
                mime = "image/jpeg"
            elif path_lower.endswith(".png"):
                mime = "image/png"
            elif path_lower.endswith(".gif"):
                mime = "image/gif"
            elif path_lower.endswith(".bmp"):
                mime = "image/bmp"
            elif path_lower.endswith(".tiff"):
                mime = "image/tiff"
            elif path_lower.endswith(".webp"):
                mime = "image/webp"
            elif path_lower.endswith(".svg"):
                mime = "image/svg+xml"
            else:
                mime = "image/jpeg"
        elif ft == "video":
            mime = "video/mp4"
        elif ft == "audio":
            mime = "audio/mpeg"
        elif ft == "archive":
            mime = "application/zip"
        else:
            mime = "application/octet-stream"

    logger.info(f"Sending {len(payload)} bytes as {filename}")

    # Save to local home directory with S3 path structure
    try:
        # Parse S3 path to extract bucket and key
        if path.startswith("s3://"):
            # Remove s3:// prefix and split into bucket and key
            s3_path_clean = path[5:]  # Remove "s3://"
            path_parts = s3_path_clean.split('/', 1)
            if len(path_parts) >= 2:
                bucket = path_parts[0]
                key = path_parts[1]
            else:
                bucket = path_parts[0]
                key = filename
        else:
            # If not a full S3 path, treat the entire path as the key structure
            bucket = "unknown-bucket"
            key = path.lstrip('/')

        # Create local path: ~/bucket/key1/key2/file.ext
        home_dir = os.path.expanduser("~")
        local_path = os.path.join(home_dir, bucket, key)

        # Ensure directory exists
        local_dir = os.path.dirname(local_path)
        os.makedirs(local_dir, exist_ok=True)

        # Write file to local path (replace if exists)
        with open(local_path, 'wb') as f:
            f.write(payload)

        logger.info(f"File saved locally to: {local_path}")

    except Exception as e:
        logger.error(f"Failed to save file locally: {e}")
        # Continue with download even if local save fails

    response = send_file(
        io.BytesIO(payload),
        as_attachment=True,
        download_name=filename,
        mimetype=mime
    )
    # Add headers to ensure download
    response.headers["Content-Disposition"] = f"attachment; filename={filename}"
    return response


def get_cache_path(bucket, prefix=""):
    """Get cache file path for a bucket/prefix"""
    cache_key = hashlib.md5(f"{bucket}:{prefix}".encode()).hexdigest()
    return os.path.join(S3_CACHE_DIR, f"{bucket}_{cache_key}.pkl")


def format_size(size):
    """Format file size"""
    if size < 1024:
        return f"{size} B"
    elif size < 1024 * 1024:
        return f"{size / 1024:.1f} KB"
    elif size < 1024 * 1024 * 1024:
        return f"{size / (1024 * 1024):.1f} MB"
    else:
        return f"{size / (1024 * 1024 * 1024):.1f} GB"


def update_bucket_cache_path(bucket, prefix, items):
    """Update a specific path in the bucket cache"""
    with CACHE_LOCK:
        if bucket not in S3_BUCKET_CACHE:
            return

        tree = S3_BUCKET_CACHE[bucket].get('tree', {})

        # Navigate to the correct position in tree
        current = tree
        if prefix:
            parts = prefix.rstrip('/').split('/')
            for part in parts:
                if 'folders' not in current:
                    current['folders'] = {}
                if part not in current['folders']:
                    current['folders'][part] = {'folders': {}, 'files': []}
                current = current['folders'][part]

        # Clear existing data
        current['folders'] = {}
        current['files'] = []

        # Add new items
        for item in items:
            if item['type'] == 'folder':
                current['folders'][item['name']] = {'folders': {}, 'files': []}
            else:
                current['files'].append(item)

        # Update timestamp
        S3_BUCKET_CACHE[bucket]['last_update'] = time.time()


def apply_cached_edits_to_record(record_data, record_edits):
    """Apply cached edits to a record for display"""
    for field_path, edit_data in record_edits.items():
        try:
            value = edit_data['value']
            data_type = edit_data['type']

            # Convert value based on type
            if data_type == 'string':
                # Value is already a string without quotes from frontend
                converted_value = str(value)
            elif data_type == 'number':
                # Value should already be a number from frontend
                if isinstance(value, (int, float)):
                    converted_value = value
                else:
                    # Fallback parsing if needed
                    converted_value = float(value) if '.' in str(value) else int(value)
            elif data_type == 'boolean':
                converted_value = bool(value) if isinstance(value, bool) else str(value).lower() == 'true'
            elif data_type == 'null':
                converted_value = None
            else:
                converted_value = value

            # Apply to nested field path
            apply_field_change(record_data, field_path, converted_value)
        except Exception as e:
            logger.error(f"Error applying cached edit to field {field_path}: {e}")

    return record_data


def apply_field_change(obj, field_path, value):
    """Apply a change to a nested field path in an object"""
    if not field_path:
        return

    parts = field_path.split('.')
    current = obj

    # Navigate to the parent of the target field
    for part in parts[:-1]:
        if part.isdigit():
            # Array index
            idx = int(part)
            if isinstance(current, list) and idx < len(current):
                current = current[idx]
            else:
                return  # Invalid path
        else:
            # Object key
            if isinstance(current, dict) and part in current:
                current = current[part]
            else:
                return  # Invalid path

    # Set the final value
    final_key = parts[-1]
    if final_key.isdigit():
        # Array index
        idx = int(final_key)
        if isinstance(current, list) and idx < len(current):
            current[idx] = value
    else:
        # Object key
        if isinstance(current, dict):
            current[final_key] = value


# Register cleanup function to run on application shutdown
import atexit

atexit.register(cleanup_temp_files)


## END DEFINITION


## ROUTES

# Add theme setter route after app initialization
@app.route("/set-theme", methods=["POST"])
def set_theme():
    """Set theme preference in session"""
    theme = request.json.get('theme', 'dark')
    session['theme'] = theme
    return {'status': 'ok'}


@app.route("/set-module", methods=["POST"])
def set_module():
    """Set module preference in session"""
    module = request.json.get('module', 'dxp')
    session['module'] = module
    # Clear caches on module switch to avoid stale listings/data
    try:
        PATH_CACHE.clear()
        S3_BUCKET_CACHE.clear()
    except Exception:
        pass
    try:
        clear_boto3_cache()
    except Exception:
        pass
    return {'status': 'ok'}


@app.route("/set-environment", methods=["POST"])
def set_environment_route():
    """Set environment preference globally"""
    global env, S3_BUCKET_CACHE, PATH_CACHE, CSV_DATA_CACHE, CSV_EDITS_CACHE, JSON_DATA_CACHE, JSON_EDITS_CACHE
    old_env = env
    environment = request.json.get('environment', 'dev')
    if environment in ['dev', 'stage', 'production']:
        env = environment
        # Save to persistent storage
        save_environment(environment)

        # Update AWS profile and environment variables immediately
        os.environ['AWS_PROFILE'] = env
        os.environ['ENVIRONMENT'] = env

        # Enhanced logging for environment changes, especially for stage
        if environment == 'stage':
            logger.info(f"STAGE ENVIRONMENT DEBUG - Environment changed TO stage")
            logger.info(f"STAGE ENVIRONMENT DEBUG - AWS_PROFILE set to: {os.environ.get('AWS_PROFILE')}")
            logger.info(f"STAGE ENVIRONMENT DEBUG - ENVIRONMENT set to: {os.environ.get('ENVIRONMENT')}")
            logger.info(f"STAGE ENVIRONMENT DEBUG - Next CryptoAPI calls will use stage parameters")

        # Clear UI S3 path because it may not be valid across environments
        previous_path = session.get('last_path', '')
        session['last_path'] = ''
        server_log("UI Path Cleared", Previous_Path=previous_path)

        # Log high-level change and cache sizes before clearing
        s3_cache_count = 0
        path_cache_count = 0
        with CACHE_LOCK:
            s3_cache_count = len(S3_BUCKET_CACHE)
        with PATH_CACHE_LOCK:
            path_cache_count = len(PATH_CACHE)
        server_log("Environment Changed", From=old_env, To=environment, AWS_Profile=os.environ.get('AWS_PROFILE'))
        server_log("Clearing Caches", S3_Buckets=s3_cache_count, Path_Entries=path_cache_count)

        # Aggressive AWS cache clearing
        clear_boto3_cache()

        # Clear crypto key cache when environment changes
        clear_crypto_cache()

        # Additional AWS session cache clearing
        import boto3

        # Clear boto3 session cache
        boto3.DEFAULT_SESSION = None

        # Keep S3_BUCKET_CACHE - don't clear it when switching environments
        with CACHE_LOCK:
            logger.info(f"Keeping S3_BUCKET_CACHE - entries: {len(S3_BUCKET_CACHE)}")

        # DO NOT clear PATH_CACHE when switching environments - keep all caches
        with PATH_CACHE_LOCK:
            logger.info(f"Keeping all cache entries - total: {len(PATH_CACHE)}")
            logger.info(
                f"Cache entries for old environment '{old_env}': {len([k for k in PATH_CACHE.keys() if k.startswith(f'{old_env}:')])}")
            logger.info(
                f"Cache entries for new environment '{environment}': {len([k for k in PATH_CACHE.keys() if k.startswith(f'{environment}:')])}")
            # All caches are preserved across environment switches

        # Keep data caches - don't clear them when switching environments
        logger.info(f"Keeping data caches - CSV: {len(CSV_DATA_CACHE)}, JSON: {len(JSON_DATA_CACHE)}")
        server_log("Caches Preserved", S3_Buckets=s3_cache_count, Path_Entries=path_cache_count)

        # Clear any potential CryptoAPI internal caches by clearing module imports
        # This forces fresh imports when CryptoAPI is next used
        import sys
        crypto_modules = [name for name in sys.modules.keys() if 'crypto' in name.lower() or 'dxpflow.secure' in name]
        for module_name in crypto_modules:
            if module_name in sys.modules:
                del sys.modules[module_name]
                logger.info(f"Cleared cached module: {module_name}")
        logger.info("Cleared CryptoAPI-related module caches for environment change")

        # Update session for user-specific tracking if needed
        session['environment'] = environment
        logger.info(f"=== ENVIRONMENT CHANGED ===")
        logger.info(f"Previous environment: {old_env}")
        logger.info(f"New environment: {environment}")
        logger.info(f"Global env variable now: {env}")
        logger.info(f"AWS_PROFILE updated to: {os.environ.get('AWS_PROFILE')}")
        logger.info(f"ENVIRONMENT updated to: {os.environ.get('ENVIRONMENT')}")
        logger.info(f"Boto3 cache cleared for new environment")
        logger.info(f"Boto3 session cache cleared for new environment")
        logger.info(f"Application S3 caches cleared for new environment")
    else:
        logger.warning(f"Invalid environment requested: {environment}, keeping: {env}")
    return {'status': 'ok', 'environment': env}


@app.route("/crypt", methods=["POST"])
def crypt():
    """Handle text encryption/decryption"""
    try:
        text = request.form.get('text', '').strip()
        action = request.form.get('action', 'encrypt')
        module = request.form.get('module', 'dxp')

        if not text:
            return "No text provided", 400

        # Force clear boto3 cache and create fresh CryptoAPI instance to use current environment
        clear_boto3_cache()

        # Additional cache clearing for AWS sessions
        import boto3

        # Clear boto3 session cache
        boto3.DEFAULT_SESSION = None

        # Force environment variables to be current
        os.environ['AWS_PROFILE'] = env
        os.environ['ENVIRONMENT'] = env

        # Log current environment for debugging
        logger.info(f"=== CRYPT OPERATION ===")
        logger.info(f"Current environment: {env}")
        logger.info(f"AWS_PROFILE: {os.environ.get('AWS_PROFILE')}")
        logger.info(f"ENVIRONMENT: {os.environ.get('ENVIRONMENT')}")
        logger.info(f"Module: {module}")
        logger.info(f"Action: {action}")

        # Create a fresh boto3 session with current profile
        session = boto3.Session(profile_name=env)
        logger.info(f"Created fresh boto3 session with profile: {session.profile_name}")

        # Test AWS credentials with the current session
        try:
            sts_client = session.client('sts')
            identity = sts_client.get_caller_identity()
            logger.info(f"AWS credentials verified - Account: {identity.get('Account')}, User: {identity.get('Arn')}")
        except Exception as aws_error:
            logger.error(f"AWS credentials test failed: {aws_error}")
            return f"❌ AWS Credentials Error\n\nFailed to verify AWS credentials for environment '{env}':\n{str(aws_error)}\n\n🔧 Please:\n1. Check your AWS SSO login status\n2. Run 'aws sso login --profile {env}' in terminal\n3. Or switch to a different environment", 400

        # Force the CryptoAPI to use the current environment by temporarily setting AWS_PROFILE
        # and clearing any potential internal caches
        original_aws_profile = os.environ.get('AWS_PROFILE', '')
        os.environ['AWS_PROFILE'] = env

        try:
            # Clear any cached CryptoAPI modules to force fresh import
            import sys
            crypto_modules = [name for name in sys.modules.keys() if
                              'crypto' in name.lower() or 'dxpflow.secure' in name]
            for module_name in crypto_modules:
                if module_name in sys.modules:
                    del sys.modules[module_name]
                    logger.info(f"Cleared cached module before CryptoAPI creation: {module_name}")

            # Import CryptoAPI here to ensure it uses the current environment
            logger.info(f"CRYPTO DEBUG - About to import CryptoAPI with environment: {env}")
            logger.info(f"CRYPTO DEBUG - Current AWS_PROFILE: {os.environ.get('AWS_PROFILE')}")
            logger.info(f"CRYPTO DEBUG - Current ENVIRONMENT: {os.environ.get('ENVIRONMENT')}")
            from dxpflow.secure.crypto import CryptoAPI
            logger.info(f"CRYPTO DEBUG - CryptoAPI import successful, creating instance for module: {module}")
            crypto_api = CryptoAPI(module)
            logger.info(f"CRYPTO DEBUG - CryptoAPI instance created successfully for module: {module}")
            logger.info(f"Successfully created CryptoAPI instance for module: {module}")
        except Exception as crypto_init_error:
            logger.error(f"CryptoAPI initialization failed: {crypto_init_error}")
            # Restore original AWS_PROFILE if CryptoAPI creation fails
            if original_aws_profile:
                os.environ['AWS_PROFILE'] = original_aws_profile
            else:
                os.environ.pop('AWS_PROFILE', None)
            raise crypto_init_error
        except Exception as e:
            error_msg = str(e)
            if "ResourceNotFoundException" in error_msg or "can't find the specified secret" in error_msg:
                return f"❌ AWS Secrets Manager Access Error\n\nYou don't have access to the required secrets for the '{module}' module in the current environment.\n\n🔧 To fix this:\n1. Switch to 'dev' environment (top-right dropdown)\n2. Or ensure you have proper AWS permissions for the current environment\n3. Or contact your AWS administrator to grant access to the required secrets\n\nCurrent environment: {env}\nModule: {module}", 400
            else:
                return f"❌ Crypto API Initialization Error\n\nFailed to initialize encryption for module '{module}':\n{error_msg}\n\nPlease check your AWS credentials and permissions.", 400

        if action == 'encrypt':
            try:
                logger.info(f"Starting encryption for text length: {len(text)}")
                # For encryption, pass text as string and encrypt
                encrypted_result = crypto_api.encrypt(text)
                logger.info(f"Encryption completed successfully - Result type: {type(encrypted_result)}")
                # Check if result is bytes or string and handle appropriately
                if isinstance(encrypted_result, bytes):
                    # If bytes, encode to base64 for display
                    import base64
                    result = base64.b64encode(encrypted_result).decode('utf-8')
                    logger.info(f"Encoded result to base64 - Length: {len(result)}")
                else:
                    # If already a string, return as-is
                    result = encrypted_result
                    logger.info(f"Result is already string - Length: {len(result)}")
            except Exception as e:
                error_msg = str(e)
                logger.error(f"Encryption failed with error: {error_msg}")
                if "ResourceNotFoundException" in error_msg or "can't find the specified secret" in error_msg:
                    return f"❌ Encryption Failed - No Secret Access\n\nCannot encrypt text for module '{module}' because you don't have access to the required AWS secrets.\n\n🔧 Solutions:\n1. Switch to 'dev' environment using the dropdown\n2. Check your AWS SSO login status\n3. Ensure you have proper permissions for the current environment\n\nCurrent environment: {env}", 400
                else:
                    return f"❌ Encryption Failed\n\nError: {error_msg}\n\nPlease try again or contact support if the issue persists.", 400
        elif action == 'decrypt':
            # For decryption, handle both base64 encoded and direct encrypted strings
            import base64
            try:
                logger.info(f"Starting decryption for text length: {len(text)}")
                # First try to treat it as base64 encoded bytes
                try:
                    encrypted_bytes = base64.b64decode(text.encode('utf-8'))
                    logger.info(f"Successfully decoded base64 - Bytes length: {len(encrypted_bytes)}")
                    decrypted_bytes = crypto_api.decrypt(encrypted_bytes)
                    logger.info(f"Decryption completed successfully - Result type: {type(decrypted_bytes)}")
                    result = decrypted_bytes.decode('utf-8')
                    logger.info(f"Decoded result to string - Length: {len(result)}")
                except Exception as base64_error:
                    logger.info(f"Base64 decode failed, trying direct decryption: {base64_error}")
                    # If that fails, try treating it as a direct encrypted string
                    decrypted_result = crypto_api.decrypt(text)
                    logger.info(f"Direct decryption completed - Result type: {type(decrypted_result)}")
                    if isinstance(decrypted_result, bytes):
                        result = decrypted_result.decode('utf-8')
                        logger.info(f"Decoded bytes result to string - Length: {len(result)}")
                    else:
                        result = decrypted_result
                        logger.info(f"Result is already string - Length: {len(result)}")
            except Exception as e:
                error_msg = str(e)
                logger.error(f"Decryption failed with error: {error_msg}")
                if "ResourceNotFoundException" in error_msg or "can't find the specified secret" in error_msg:
                    return f"❌ Decryption Failed - No Secret Access\n\nCannot decrypt text for module '{module}' because you don't have access to the required AWS secrets.\n\n🔧 Solutions:\n1. Switch to 'dev' environment using the dropdown\n2. Check your AWS SSO login status\n3. Ensure you have proper permissions for the current environment\n\nCurrent environment: {env}", 400
                elif "Incorrect padding" in error_msg:
                    return f"❌ Decryption Failed - Invalid Format\n\nThe encrypted text appears to be in an invalid format or corrupted.\n\nPlease ensure you're using the correct encrypted text and try again.", 400
                else:
                    return f"❌ Decryption Failed\n\nError: {error_msg}\n\nPlease check the encrypted text format and try again.", 400
        else:
            return "Invalid action", 400

        return result, 200

    except Exception as e:
        logger.error(f"Crypt operation failed: {e}", exc_info=True)
        return f"❌ Unexpected Error\n\nAn unexpected error occurred: {str(e)}\n\nPlease try again or contact support if the issue persists.", 500


@app.route("/", methods=["GET", "POST"])
def home():
    try:
        if request.method == "GET":
            server_log("Home Page", Environment=env)

            # Check if we're coming from an encrypt-upload operation
            from_encrypt_upload = session.pop('from_encrypt_upload', False)
            if from_encrypt_upload:
                server_log("Returning from Upload - Encrypt", Upload_Id=session.get('upload_id'),
                           Upload_Filename=session.get('upload_filename'), Last_Path=session.get('last_path'))
            else:
                server_log("Home Reset")

            # Only clear session data if we're not coming from encrypt-upload
            if not from_encrypt_upload:
                # Clear any cached local upload when landing on the form
                if 'upload_id' in session:
                    upload_id = session['upload_id']
                    if upload_id in LOCAL_UPLOADS:
                        try:
                            os.unlink(LOCAL_UPLOADS[upload_id])
                            LOCAL_UPLOADS.pop(upload_id)
                        except:
                            pass
                session.pop("upload_id", None)
                session.pop("upload_filename", None)  # Also clear the filename

                # Clear CSV caches when returning home
                CSV_DATA_CACHE.clear()
                CSV_EDITS_CACHE.clear()
                JSON_DATA_CACHE.clear()
                JSON_EDITS_CACHE.clear()

            # Get last path from session
            last_path = session.get('last_path', '')
            # Get current module from session, default to 'dxp'
            current_module = session.get('module', 'dxp')
            return render_template_string(
                HOME_HTML,
                logo=LOGO_URL,
                last_path=last_path,
                env=env,
                theme=session.get('theme', 'dark'),
                module=current_module,
                big_time_display=get_big_time_display(),
                s3_browser_modal=render_s3_browser_modal(env),
                s3_browser_styles=S3_BROWSER_STYLES,
                s3_browser_script=S3_BROWSER_SCRIPT,
            )

        # POST
        module = request.form.get("module", "dxp")
        # Save module to session
        session['module'] = module
        server_log("FILE_OPEN_START", module=module)
        action = request.form.get("action", "edit")

        # If a local file was submitted for editing, cache it and mark upload_id before any S3 checks
        upload = request.files.get("upload_file")
        if upload and upload.filename and action in ("edit", "view_json", "view_code", "view_text"):
            try:
                raw_bytes = upload.read()
                tmp = tempfile.NamedTemporaryFile(delete=False)
                tmp.write(raw_bytes)
                tmp.close()

                upload_id = str(uuid.uuid4())
                LOCAL_UPLOADS[upload_id] = tmp.name
                session["upload_id"] = upload_id
                session["upload_filename"] = upload.filename
                try:
                    server_log("Local Edit - Uploaded Temp File", Path=tmp.name, Upload_Id=upload_id,
                               Filename=upload.filename)
                except Exception:
                    pass
            except Exception as e:
                logger.error(f"Error handling local upload for edit: {e}", exc_info=True)
                flash("Failed to read selected local file")
                return redirect(url_for("home"))

        upload_id = session.get("upload_id")

        # Get the S3 path from form (this should always be present)
        s3_path_from_form = request.form.get("s3_path", "").strip()
        # If user is trying to Edit via S3 path and path is invalid, show modal and redirect
        if action in ("edit",
                      "view_json") and not upload_id and s3_path_from_form and not s3_path_from_form.lower().startswith(
            's3://'):
            msg = "Please provide a valid S3 path starting with s3://"
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                        window.location = '{url_for('home')}';
                      }}());
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )

        # 2) Or reuse previous upload_id / S3 path
        if s3_path_from_form:
            s3_path = s3_path_from_form
        elif upload_id and session.get("upload_filename"):
            s3_path = session["upload_filename"]
        else:
            s3_path = s3_path_from_form

        # If we're navigating JSON and have an upload_id but no s3_path, use the filename
        if action == "view_json" and upload_id and not s3_path:
            # Get filename from session
            if "upload_filename" in session:
                s3_path = session["upload_filename"]
            else:
                # Fallback - should not happen
                s3_path = "uploaded_file.json"

        if not s3_path and not upload_id:
            try:
                DXP_LOGGER.error("Edit Abort - No path or upload selected")
            except Exception:
                pass
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {"Please enter a valid S3 path or select a file"!r}); }} catch(err) {{}}
                        window.location = '{url_for('home')}';
                      }}());
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )
        gz_flag = s3_path.lower().endswith(".gz")

        # Save path to session only if it's a valid S3 path
        if s3_path and s3_path.lower().startswith('s3://'):
            session['last_path'] = s3_path

        # Create a cache key for data
        # For local files, use the upload_id in the cache key to ensure consistency
        if upload_id:
            cache_key = f"local:{upload_id}:{module}"
        else:
            cache_key = f"{s3_path}:{module}:no-upload"

        # 3) Initialize decryption_module
        decryption_module = None

        # Log action intent
        try:
            server_log("Edit Request", S3_Path=s3_path, Module_Selected=module)
        except Exception:
            pass

        # 4) Read raw bytes and get metadata in TRUE PARALLEL (optimized)
        file_metadata = {
            'size': 'Not Available',
            'created_date': 'Not Available',
            'last_modified': 'Not Available'
        }

        def get_metadata():
            """Get file metadata in parallel"""
            try:
                if upload_id and upload_id in LOCAL_UPLOADS:
                    # Get local file metadata
                    local_file_path = LOCAL_UPLOADS[upload_id]
                    if os.path.exists(local_file_path):
                        stat_info = os.stat(local_file_path)
                        size_bytes = stat_info.st_size
                        size_formatted = format_file_size(size_bytes)

                        created_time = datetime.fromtimestamp(stat_info.st_ctime)
                        modified_time = datetime.fromtimestamp(stat_info.st_mtime)

                        return {
                            'size': size_formatted,
                            'created_date': created_time.strftime('%d %b %Y, %I:%M %p'),
                            'last_modified': modified_time.strftime('%d %b %Y, %I:%M %p')
                        }
                elif s3_path and s3_path.startswith('s3://'):
                    # Get S3 metadata
                    s3_clean = s3_path[5:]
                    bucket, key = s3_clean.split('/', 1) if '/' in s3_clean else (s3_clean, '')
                    if bucket and key:
                        s3_client = get_fresh_s3_client()
                        response = s3_client.head_object(Bucket=bucket, Key=key)
                        size_bytes = response.get('ContentLength', 0)
                        size_formatted = format_file_size(size_bytes)
                        last_modified = response.get('LastModified')

                        if last_modified:
                            try:
                                last_modified_local = last_modified.replace(tzinfo=timezone.utc).astimezone()
                                last_modified_str = last_modified_local.strftime('%d %b %Y, %I:%M %p')
                            except Exception as e:
                                logger.warning(f"Error converting S3 timestamp: {e}")
                                last_modified_str = last_modified.strftime('%d %b %Y, %I:%M %p')
                        else:
                            last_modified_str = 'Not Available'

                        return {
                            'size': size_formatted,
                            'created_date': 'Not Available',
                            'last_modified': last_modified_str
                        }
            except Exception as e:
                logger.warning(f"Error getting metadata: {e}")
            return file_metadata

        def get_content():
            """Get file content in parallel"""
            try:
                if upload_id:
                    with open(LOCAL_UPLOADS[upload_id], "rb") as f:
                        return f.read()
                else:
                    logger.info(f"Reading S3 key {s3_path} using module: {module}")
                    return S3Utils(verify=False).read_key(
                        s3_path, utf_decode=False, module=module
                    )
            except Exception as e:
                logger.error(f"Error reading file content: {e}")
                raise e

        # Execute both operations in parallel
        try:
            with ThreadPoolExecutor(max_workers=2) as executor:
                # Submit both tasks simultaneously
                metadata_future = executor.submit(get_metadata)
                content_future = executor.submit(get_content)

                # Get results (this will wait for both to complete)
                file_metadata = metadata_future.result()
                raw = content_future.result()

                logger.info(f"Parallel fetch completed - Content: {len(raw)} bytes, Metadata: {file_metadata}")

        except Exception as e:
            logger.error(f"Error in parallel fetch: {e}")
            # Fallback to sequential if parallel fails
            try:
                raw = get_content()
                file_metadata = get_metadata()
            except Exception as fallback_e:
                logger.error(f"Fallback also failed: {fallback_e}")
                raise fallback_e

        # 5) Decrypt if needed
        if isinstance(raw, (bytes, bytearray)) and raw.startswith(b"ENC"):
            # Skip decryption for code/text-like files which should be plain
            lower_name = (s3_path or "").lower()
            base_name = os.path.basename(lower_name)
            has_extension = "." in base_name
            is_code_like = lower_name.endswith((".py", ".html", ".htm", ".js", ".go", ".md")) or not has_extension
            if not is_code_like:
                logger.info(f"Decrypting file using module: {module}")
                crypto_api = get_cached_crypto_api(module, "file_decrypt")
                raw = crypto_api.decrypt(raw)
                decryption_module = module
                logger.info(f"File decrypted using module: {module}")

        # 6) Decompress if gzipped
        if gz_flag:
            try:
                raw = gzip.decompress(raw)
            except:
                pass

        # 7) Decode to text
        text = raw.decode("utf-8") if isinstance(raw, (bytes, bytearray)) else raw

        # 8) Detect file type - properly handle JSONL and other formats
        # Use the uploaded filename for type detection if it's a local file
        detect_path = session.get('upload_filename') if (upload_id and session.get('upload_filename')) else s3_path
        path_lower = detect_path.lower()

        server_log("File Type Detection")
        logger.info(f"Detecting file type for: {detect_path}")

        # Check if it's an editable file type
        is_json = path_lower.endswith((".json", ".json.gz", ".jsonl", ".jsonl.gz")) or (
                text and text.lstrip().startswith(("{", "[")))
        is_csv = path_lower.endswith((".csv", ".csv.gz")) or (
                text and not text.lstrip().startswith(("{", "[")))

        # Determine if file is editable
        is_editable = is_json or is_csv

        logger.info(f"File type detection - JSON: {is_json}, CSV: {is_csv}, Editable: {is_editable}")

        # Set file type with code precedence (extensions or no extension)
        is_code_path = path_lower.endswith(
            (".py", ".html", ".htm", ".js", ".go", ".md", ".xml", ".css", ".sql", ".sh", ".bash", ".yaml", ".yml",
             ".toml", ".ini", ".conf", ".cfg", ".txt", ".properties", ".dockerfile")) or (
                               detect_path and "." not in os.path.basename(detect_path))
        if is_code_path:
            file_type = "code"
        elif is_json:
            file_type = "json"
        elif path_lower.endswith((".csv", ".csv.gz")):
            file_type = "csv"
        else:
            # For non-editable files, still determine a type for display purposes
            if path_lower.endswith((".xlsx", ".xls")):
                file_type = "excel"
            elif path_lower.endswith((".pdf")):
                file_type = "pdf"
            elif path_lower.endswith((".docx", ".docs")):
                file_type = "doc"
            elif path_lower.endswith((".txt", ".log")):
                file_type = "text"
            else:
                file_type = "other"

        logger.info(f"Final file type determined: {file_type}")
        try:
            server_log("Edit Routing", Action=action, File_Type=file_type, Gzipped=gz_flag,
                       Cached=(cache_key in JSON_DATA_CACHE or cache_key in CSV_DATA_CACHE))
        except Exception:
            pass

        # 9) Download shortcut - moved up before file type detection
        if action == "download":
            return download_file()

        # 10) For JSON/JSONL files, show the JSON editor
        if file_type == "json" and action in ["edit", "view_json"]:
            try:
                # Use cached data if available
                if cache_key in JSON_DATA_CACHE:
                    data_list, json_format = JSON_DATA_CACHE[cache_key]
                    logger.info(f"Using cached JSON data: {len(data_list)} records")
                else:
                    data_list, json_format = parse_json_or_jsonl(text)
                    JSON_DATA_CACHE[cache_key] = (data_list, json_format)
                    logger.info(f"Parsed and cached JSON data: {len(data_list)} records, format: {json_format}")

                record = int(request.form.get("record", 0))

                # Get the specific record to display
                if record >= len(data_list):
                    record = 0

                current_data = data_list[record] if data_list else {}

                # Apply cached edits to current record if they exist
                if cache_key in JSON_EDITS_CACHE and record in JSON_EDITS_CACHE[cache_key]:
                    current_data = apply_cached_edits_to_record(current_data.copy(),
                                                                JSON_EDITS_CACHE[cache_key][record])
                    logger.info(f"Applied cached edits to record {record}")

                # For single objects, hide pagination
                show_pagination = len(data_list) > 1 or json_format == "jsonl"

                # Calculate total edit count across all records
                total_edits = 0
                if cache_key in JSON_EDITS_CACHE:
                    for record_edits in JSON_EDITS_CACHE[cache_key].values():
                        total_edits += len(record_edits)

                logger.info(
                    f"Displaying record {record + 1}/{len(data_list)}: {json.dumps(current_data, indent=2)[:500]}...")

                # For local files, show a placeholder S3 path
                display_s3_path = s3_path
                if upload_id and not s3_path.lower().startswith('s3://'):
                    # This is a local file - show a suggested S3 path
                    display_s3_path = f"s3://bucket/path/{s3_path}"

                # Check if raw edit is enabled
                raw_edit_enabled = request.form.get("raw_edit") == "true"
                logger.info(f"Raw edit parameter received: {request.form.get('raw_edit')}, enabled: {raw_edit_enabled}")

                # Log JSON editor readiness
                try:
                    server_log("JSON Editor Ready",
                               S3_Path=display_s3_path,
                               Module_Selected=module,
                               Data_Format=json_format.upper(),
                               Total_Records=len(data_list),
                               Current_Record=f"{record + 1} of {len(data_list)}",
                               Raw_Edit=raw_edit_enabled,
                               Cache_Dir=S3_CACHE_DIR,
                               Cache_Key=cache_key[:50] + "..." if len(cache_key) > 50 else cache_key)
                except Exception:
                    pass

                # Choose template based on raw edit preference
                if raw_edit_enabled:
                    # For raw edit, we need to provide the raw text content
                    return render_template_string(
                        RAW_EDIT_HTML,
                        logo=LOGO_URL,
                        s3_path=display_s3_path,
                        module=module,
                        decryption_module=decryption_module,
                        gzipped=gz_flag,
                        file_type="json",
                        code_text=text,  # Raw text content for Monaco editor
                        actual_file_path=session.get('upload_filename') if upload_id else s3_path,
                        # For language detection
                        cache_key=cache_key,
                        theme=session.get('theme', 'dark'),
                        env=env,
                        big_time_display=get_big_time_display(),
                        s3_browser_modal=render_s3_browser_modal(env),
                        s3_browser_styles=S3_BROWSER_STYLES,
                        s3_browser_script=S3_BROWSER_SCRIPT,
                        file_metadata=file_metadata,  # Pass metadata from parallel fetch
                    )
                else:
                    # Use structured JSON editor
                    return render_template_string(
                        JSON_EDIT_HTML,
                        logo=LOGO_URL,
                        s3_path=display_s3_path,
                        module=module,
                        decryption_module=decryption_module,
                        gzipped=gz_flag,
                        is_jsonl=(json_format == "jsonl"),
                        is_json_object=(json_format == "json-object"),
                        json_type=json_format,
                        show_pagination=show_pagination,
                        current_record=record,
                        total_records=len(data_list),
                        json_data_str=json.dumps(current_data),
                        cache_key=cache_key,
                        record_index=record,
                        total_edits=total_edits,
                        record_edits=JSON_EDITS_CACHE.get(cache_key, {}).get(record, {}),
                        theme=session.get('theme', 'dark'),
                        env=env,
                        big_time_display=get_big_time_display(),
                        s3_browser_modal=render_s3_browser_modal(env),
                        s3_browser_styles=S3_BROWSER_STYLES,
                        s3_browser_script=S3_BROWSER_SCRIPT,
                    )
            except ValueError as ve:
                # If JSON parsing fails, check if raw edit is enabled
                raw_edit_enabled = request.form.get("raw_edit") == "true"
                logger.info(f"JSON parsing failed: {ve}")

                # For local files, show a placeholder S3 path
                display_s3_path = s3_path
                if upload_id and not s3_path.lower().startswith('s3://'):
                    display_s3_path = f"s3://bucket/path/{s3_path}"

                if raw_edit_enabled:
                    # Use raw editor for invalid JSON
                    return render_template_string(
                        RAW_EDIT_HTML,
                        logo=LOGO_URL,
                        s3_path=display_s3_path,
                        module=module,
                        decryption_module=decryption_module,
                        gzipped=gz_flag,
                        file_type="json",
                        code_text=text,  # Raw text content for Monaco editor
                        actual_file_path=session.get('upload_filename') if upload_id else s3_path,
                        # For language detection
                        cache_key=cache_key,
                        theme=session.get('theme', 'dark'),
                        env=env,
                        big_time_display=get_big_time_display(),
                        s3_browser_modal=render_s3_browser_modal(env),
                        s3_browser_styles=S3_BROWSER_STYLES,
                        s3_browser_script=S3_BROWSER_SCRIPT,
                    )
                else:
                    # Show JSON editor with error data
                    data_list = [{"error": str(ve), "raw_content": text[:1000] + "..." if len(text) > 1000 else text}]
                    json_format = "json-array"

                    return render_template_string(
                        JSON_EDIT_HTML,
                        logo=LOGO_URL,
                        s3_path=display_s3_path,
                        module=module,
                        decryption_module=decryption_module,
                        gzipped=gz_flag,
                        is_jsonl=False,
                        is_json_object=False,
                        json_type=json_format,
                        show_pagination=False,
                        current_record=0,
                        total_records=len(data_list),
                        json_data_str=json.dumps(data_list[0]),
                        cache_key=cache_key,
                        record_index=0,
                        theme=session.get('theme', 'dark'),
                        env=env,
                        big_time_display=get_big_time_display(),
                        s3_browser_modal=render_s3_browser_modal(env),
                        s3_browser_styles=S3_BROWSER_STYLES,
                        s3_browser_script=S3_BROWSER_SCRIPT,
                    )
            except Exception as e:
                # If JSON parsing fails, check if raw edit is enabled
                raw_edit_enabled = request.form.get("raw_edit") == "true"
                logger.info(f"JSON parsing error: {e}")

                # For local files, show a placeholder S3 path
                display_s3_path = s3_path
                if upload_id and not s3_path.lower().startswith('s3://'):
                    display_s3_path = f"s3://bucket/path/{s3_path}"

                if raw_edit_enabled:
                    # Use raw editor for any JSON errors
                    return render_template_string(
                        RAW_EDIT_HTML,
                        logo=LOGO_URL,
                        s3_path=display_s3_path,
                        module=module,
                        decryption_module=decryption_module,
                        gzipped=gz_flag,
                        file_type="json",
                        code_text=text,  # Raw text content for Monaco editor
                        actual_file_path=session.get('upload_filename') if upload_id else s3_path,
                        # For language detection
                        cache_key=cache_key,
                        theme=session.get('theme', 'dark'),
                        env=env,
                        big_time_display=get_big_time_display(),
                        s3_browser_modal=render_s3_browser_modal(env),
                        s3_browser_styles=S3_BROWSER_STYLES,
                        s3_browser_script=S3_BROWSER_SCRIPT,
                    )
                else:
                    # Show JSON editor with error data
                    data_list = [{"error": str(e), "raw_content": text[:1000] + "..." if len(text) > 1000 else text}]
                    json_format = "json-array"

                    return render_template_string(
                        JSON_EDIT_HTML,
                        logo=LOGO_URL,
                        s3_path=display_s3_path,
                        module=module,
                        decryption_module=decryption_module,
                        gzipped=gz_flag,
                        is_jsonl=False,
                        is_json_object=False,
                        json_type=json_format,
                        show_pagination=False,
                        current_record=0,
                        total_records=len(data_list),
                        json_data_str=json.dumps(data_list[0]),
                        cache_key=cache_key,
                        record_index=0,
                        theme=session.get('theme', 'dark'),
                        env=env,
                        big_time_display=get_big_time_display(),
                        s3_browser_modal=render_s3_browser_modal(env),
                        s3_browser_styles=S3_BROWSER_STYLES,
                        s3_browser_script=S3_BROWSER_SCRIPT,
                    )

        # 10.25) If Visual Studio (raw_edit) is enabled for CSV, open RAW editor instead of table editor
        raw_edit_enabled = request.form.get("raw_edit") == "true"
        if file_type == "csv" and raw_edit_enabled and action in ["edit", "view_text", "view_code", "view_json"]:
            # For local files, show a placeholder S3 path
            display_s3_path = s3_path
            if upload_id and not s3_path.lower().startswith('s3://'):
                display_s3_path = f"s3://bucket/path/{s3_path}"

            # Normalize line endings for Monaco
            code_text = text.replace('\r\n', '\n') if isinstance(text, str) else ''

            return render_template_string(
                RAW_EDIT_HTML,
                logo=LOGO_URL,
                s3_path=display_s3_path,
                module=module,
                decryption_module=decryption_module,
                gzipped=gz_flag,
                file_type="csv",
                code_text=code_text,
                actual_file_path=session.get('upload_filename') if upload_id else s3_path,
                cache_key=cache_key,
                theme=session.get('theme', 'dark'),
                env=env,
                big_time_display=get_big_time_display(),
                s3_browser_modal=render_s3_browser_modal(env),
                s3_browser_styles=S3_BROWSER_STYLES,
                s3_browser_script=S3_BROWSER_SCRIPT,
                file_metadata=file_metadata,  # Pass metadata from parallel fetch
            )

        # 10.5) For Code files, show the Code editor (no decryption/encryption on save)
        if file_type == "code" and action in ["edit", "view_json", "view_text", "view_code"]:
            display_s3_path = s3_path
            if upload_id and not s3_path.lower().startswith('s3://'):
                display_s3_path = f"s3://bucket/path/{s3_path}"
            code_text = text.replace('\r\n', '\n') if isinstance(text, str) else ''
            logger.info(f"Code text length: {len(code_text)}")

            # DEBUG REMOVED: avoid logging sensitive file contents

            # Determine the actual file path for detection (local filename vs S3 path)
            actual_file_path = session.get('upload_filename') if upload_id else s3_path

            return render_template_string(
                CODE_EDIT_HTML,
                logo=LOGO_URL,
                s3_path=display_s3_path,
                actual_file_path=actual_file_path,
                module=module,
                code_text=code_text,
                theme=session.get('theme', 'dark'),
                env=env,
                big_time_display=get_big_time_display(),
                s3_browser_modal=render_s3_browser_modal(env),
                s3_browser_styles=S3_BROWSER_STYLES,
                s3_browser_script=S3_BROWSER_SCRIPT,
                file_metadata=file_metadata,  # Pass metadata from parallel fetch
            )

        # 11) For CSV files or failed JSON, continue with the original table editor
        if file_type == "csv":
            # Check if we already have this CSV cached
            if cache_key not in CSV_DATA_CACHE or request.form.get("force_reload"):
                delim = detect_delimiter(text[:2048])
                escaped = f"\\u{ord(delim):04x}" if delim and ord(delim) < 32 else (delim or ",")

                # Parse CSV into DataFrame - CRITICAL: Use dtype=str to preserve all values as strings
                try:
                    df_full = pd.read_csv(io.StringIO(text), sep=(delim or ","), dtype=str, keep_default_na=False)

                    # DO NOT SORT HERE - keep original order in cache
                    # Cache the ORIGINAL UNSORTED DataFrame
                    CSV_DATA_CACHE[cache_key] = {
                        'dataframe': df_full,
                        'delimiter': delim,
                        'original_text': text
                    }
                    logger.info(f"Cached original CSV data for {cache_key}: {len(df_full)} rows")
                except Exception as e:
                    try:
                        DXP_LOGGER.error(f"CSV Parse Error - {str(e)}")
                    except Exception:
                        pass
                    return (
                        f"""
                            <script>
                              (function(){{
                                try {{ localStorage.setItem('workbench-pending-modal-error', {('Error parsing CSV: ' + str(e))!r}); }} catch(err) {{}}
                                window.location = '{url_for('home')}';
                              }}());
                            </script> """,
                        200,
                        {"Content-Type": "text/html"},
                    )
            else:
                # Use cached data
                cached_data = CSV_DATA_CACHE[cache_key]
                df_full = cached_data['dataframe'].copy()  # Work with a copy
                delim = cached_data['delimiter']
                escaped = f"\\u{ord(delim):04x}" if delim and ord(delim) < 32 else (delim or ",")
                logger.info(f"Using cached CSV data for {cache_key}")

            # Get edits for this file
            edits = CSV_EDITS_CACHE.get(cache_key, {})
        else:
            # For JSON files being edited as CSV
            delim = ","
            escaped = ","
            edits = {}
            try:
                parsed = json.loads(text)
                if isinstance(parsed, list):
                    df_full = pd.json_normalize(parsed)
                else:
                    df_full = pd.DataFrame([parsed])
            except:
                # Try JSONL
                lines = text.strip().splitlines()
                records = []
                for line in lines:
                    if line.strip():
                        try:
                            records.append(json.loads(line))
                        except:
                            pass
                df_full = pd.json_normalize(records) if records else pd.DataFrame()

            # Only fill NA for non-CSV files
            df_full.fillna("", inplace=True)

        # Create a display copy for sorting and editing
        df_display = df_full.copy()

        # Sort the display copy by first column
        if len(df_display.columns) > 0:
            first_col = df_display.columns[0]
            df_display = df_display.sort_values(
                by=first_col, key=lambda col: col.astype(str), ignore_index=True
            )
            logger.info(f"Sorted display DataFrame by column '{first_col}'")

        # Apply edits to the sorted display DataFrame
        applied_edits = 0
        for edit_key, value in edits.items():
            row_idx, col_idx = map(int, edit_key.split(','))
            if row_idx < len(df_display) and col_idx < len(df_display.columns):
                col_name = df_display.columns[col_idx]
                old_value = df_display.iloc[row_idx, col_idx]
                df_display.iloc[row_idx, col_idx] = value
                applied_edits += 1
                logger.debug(f"Applied edit: Row {row_idx}, Col {col_idx} ({col_name}): '{old_value}' -> '{value}'")
            else:
                logger.warning(f"Edit out of bounds: Row {row_idx}, Col {col_idx}, DataFrame shape: {df_display.shape}")

        logger.info(f"Applied {applied_edits} edits to sorted display DataFrame")

        # 12) Paginate (use display DataFrame which is sorted and has edits applied)
        page = int(request.form.get("page", 1))
        per_page = int(
            request.form.get("records_per_page", request.form.get("recordsPerPage", 40)))  # sync with front-end span
        total_rows = len(df_display)
        page_count = max(1, math.ceil(total_rows / per_page))

        # Ensure page number is valid for current pagination settings
        page = max(1, min(page, page_count))

        start = (page - 1) * per_page
        end = start + per_page
        df_page = df_display.iloc[start:end]
        start_rec = start + 1
        end_rec = min(end, total_rows)

        # Convert to list of lists to preserve column order
        data_as_lists = []
        columns = list(df_display.columns)
        for idx, row in df_page.iterrows():
            row_data = {}
            for col in columns:
                row_data[col] = row[col]
            data_as_lists.append(row_data)

        # For local files being edited as CSV, show a placeholder S3 path
        display_s3_path = s3_path
        if upload_id and not s3_path.lower().startswith('s3://') and file_type == "csv":
            display_s3_path = f"s3://bucket/path/{s3_path}"

        # Human-friendly CSV editor log
        try:
            server_log("CSV Editor Ready",
                       S3_Path=display_s3_path,
                       Module_Selected=module,
                       Total_Records=total_rows,
                       Records_Per_Page=per_page,
                       Pages=page_count,
                       Showing=f"{start_rec}-{end_rec}",
                       Delimiter=escaped,
                       Cache_Dir=S3_CACHE_DIR,
                       Cache_Key=cache_key[:50] + "..." if len(cache_key) > 50 else cache_key)
        except Exception:
            pass

        # 13) Render editor - Pass cache_key and edits
        return render_template_string(
            CSV_EDIT_HTML,
            logo=LOGO_URL,
            upload_id=upload_id,
            s3_path=display_s3_path,
            module=module,
            decryption_module=decryption_module,
            file_type=file_type,
            gzipped=gz_flag,
            columns=columns,
            data=data_as_lists,
            escaped_delimiter=escaped,
            page=page,
            page_count=page_count,
            per_page=per_page,  # Add per_page for pagination forms
            start_rec=start_rec,
            end_rec=end_rec,
            total_rows=total_rows,
            cache_key=cache_key,
            edits=edits,
            edits_json=json.dumps(edits),
            start=start,  # Add this for row indexing
            theme=session.get('theme', 'dark'),
            env=env,
            big_time_display=get_big_time_display(),
            s3_browser_modal=render_s3_browser_modal(env),
            s3_browser_styles=S3_BROWSER_STYLES,
            s3_browser_script=S3_BROWSER_SCRIPT,
        )
    except Exception as e:
        logger.error(f"Error in home route: {e}", exc_info=True)
        try:
            DXP_LOGGER.error(f"Edit Flow Error - {str(e)}")
        except Exception:
            pass
        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {('An error occurred: ' + str(e))!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }}());
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )


@app.route("/refreshtoken")
def refreshtoken():
    # Set browser for SSO login - Windows compatible
    if os.name == 'nt':  # Windows
        # On Windows, try common browsers or leave default
        os.environ["BROWSER"] = os.environ.get("BROWSER", "")
    else:  # Unix-like (macOS, Linux)
        os.environ["BROWSER"] = "Island"
    # Login to SSO
    sso_command = ["aws", "sso", "login", "--profile", env]
    server_log("SSO Login")
    logger.info(f"Environment: {env}")
    logger.info(f"Command: {' '.join(sso_command)}")
    logger.info(f"Full command: aws sso login --profile {env}")

    try:
        shell_needed = os.name == 'nt'
        result = subprocess.run(sso_command, capture_output=True, text=True, shell=shell_needed)
        logger.info(f"SSO login exit code: {result.returncode}")
        if result.stdout:
            logger.info(f"SSO login stdout: {result.stdout}")
        if result.stderr:
            logger.info(f"SSO login stderr: {result.stderr}")
        if result.returncode != 0:
            msg = f"AWS SSO login failed (exit {result.returncode}).\n\n{(result.stderr or '').strip() or (result.stdout or '').strip()}"
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                        window.location = '{url_for('home')}';
                      }}());
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )
    except Exception as e:
        logger.error(f"SSO login error: {e}")
        if os.name == 'nt':
            logger.error("Windows users: Ensure AWS CLI is installed and in PATH")
            logger.error("Try running 'aws --version' in Command Prompt to verify")
        msg = f"AWS SSO login error: {str(e)}"
        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }}());
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )

    return redirect(url_for("home"))


# Add path setter route
@app.route("/open-airflow", methods=["POST"])
def open_airflow():
    """Open Airflow (MWAA) console for the current environment (dev/stage)."""
    try:
        current_env = env  # 'dev' or 'stage'
        product = 'cdm'
        domain = 'sequoia-development.com'
        host = f"mwaa-{product}-{current_env}.{domain}"
        mwaa_name = f"pp-data-mwaa-{product}-us-west-2-{current_env}"

        cmd = [
            'aws', 'mwaa', 'create-web-login-token',
            '--name', mwaa_name,
            '--query', 'WebToken',
            '--output', 'text',
            '--profile', current_env
        ]
        shell_needed = os.name == 'nt'
        server_log("Airflow Token Request", Name=mwaa_name, Profile=current_env)
        result = subprocess.run(cmd, capture_output=True, text=True, shell=shell_needed)
        # Detailed logging for diagnostics
        logger.info(f"MWAA token exit code: {result.returncode}")
        stdout_text = (result.stdout or '').strip()
        stderr_text = (result.stderr or '').strip()
        logger.info(f"MWAA token stdout length: {len(stdout_text)}")
        if stderr_text:
            logger.error(f"MWAA token stderr: {stderr_text}")
        if result.returncode != 0 or not stdout_text:
            lc_err = stderr_text.lower()
            if 'token has expired' in lc_err or 'expired' in lc_err:
                msg = "AWS SSO token expired. Please refresh token and try again."
                server_log("Airflow SSO Expired", Profile=current_env)
                # 401 to indicate auth issue
                return {'status': 'error', 'message': msg, 'stderr': stderr_text, 'returncode': result.returncode}, 401
            msg = "Failed to get Airflow token"
            flash(f"{msg}. Ensure AWS SSO is logged in for this profile.")
            return {'status': 'error', 'message': msg, 'stderr': stderr_text, 'returncode': result.returncode}, 500
        token = stdout_text

        url = f"https://{host}/aws_mwaa/aws-console-sso?login=true#{token}"
        server_log("Airflow URL", URL=url)

        # Client will open the URL; do not open server-side to avoid duplicates
        return {'status': 'ok', 'url': url}
    except Exception as e:
        logger.error(f"/open-airflow error: {e}", exc_info=True)
        flash("Error opening Airflow. Check logs for details.")
        return {'status': 'error', 'message': str(e)}, 500


@app.route('/open-cloudwatch', methods=['POST'])
def open_cloudwatch():
    """Open AWS CloudWatch console via federation sign-in using current AWS profile."""
    try:
        import json as _json
        import urllib.parse as _urlparse
        import urllib.request as _urlreq
        import ssl as _ssl
        import boto3 as _boto3
        from botocore.exceptions import BotoCoreError, ClientError

        profile = os.environ.get('AWS_PROFILE', env)
        region = 'us-west-2'
        server_log("CloudWatch Open Request", Profile=profile, Region=region)

        session = _boto3.Session(profile_name=profile, region_name=region)
        sts = session.client('sts')
        try:
            sts.get_caller_identity()
        except (BotoCoreError, ClientError) as e:
            msg = str(e)
            if 'expired' in msg.lower() or 'token' in msg.lower():
                return {'status': 'error', 'message': 'AWS SSO token expired. Please refresh token and try again.'}, 401
            return {'status': 'error', 'message': f'Failed to validate AWS credentials: {msg}'}, 500

        creds = session.get_credentials()
        if not creds:
            return {'status': 'error', 'message': 'No AWS credentials found for current profile. Please log in.'}, 401
        fc = creds.get_frozen_credentials()

        session_dict = {
            'sessionId': fc.access_key,
            'sessionKey': fc.secret_key,
            'sessionToken': fc.token,
        }
        session_json = _json.dumps(session_dict)
        get_token_url = (
                'https://signin.aws.amazon.com/federation?'
                + _urlparse.urlencode({
            'Action': 'getSigninToken',
            'SessionType': 'json',
            'Session': session_json,
        })
        )
        _ctx = _ssl._create_unverified_context()
        with _urlreq.urlopen(get_token_url, context=_ctx) as resp:
            body = resp.read().decode('utf-8')
            token = _json.loads(body).get('SigninToken')
        if not token:
            return {'status': 'error', 'message': 'Failed to obtain federation sign-in token'}, 500

        # Try to read a Glue job run id (jr_...) from clipboard (macOS pbpaste). If present, deep-link to that stream.
        job_event = None
        try:
            import subprocess as _subprocess
            clip_text = _subprocess.check_output(['pbpaste'], text=True, stderr=_subprocess.DEVNULL).strip()
            if clip_text:
                import re as _re
                m = _re.search(r'\bjr_[0-9A-Za-z]+\b', clip_text)
                if m:
                    job_event = m.group(0)
        except Exception:
            job_event = None

        base_group = '$252Faws-glue$252Fjobs$252Foutput'
        destination = f'https://console.aws.amazon.com/cloudwatch/home?region={region}#logsV2:log-groups/log-group/{base_group}'
        if job_event:
            destination = destination + '/log-events/' + _urlparse.quote(job_event, safe='')

        login_url = (
                'https://signin.aws.amazon.com/federation?'
                + _urlparse.urlencode({
            'Action': 'login',
            'Issuer': 'workbench-utility',
            'Destination': destination,
            'SigninToken': token,
        })
        )
        server_log("CloudWatch URL", URL=login_url, JobEvent=job_event or '')
        return {'status': 'ok', 'url': login_url}
    except Exception as e:
        logger.error(f"/open-cloudwatch error: {e}", exc_info=True)
        return {'status': 'error', 'message': str(e)}, 500


@app.route('/open-glue', methods=['POST'])
def open_glue():
    """Open AWS Glue (Glue Studio) console via federation sign-in using current AWS profile."""
    try:
        import json as _json
        import urllib.parse as _urlparse
        import urllib.request as _urlreq
        import ssl as _ssl
        import boto3 as _boto3
        from botocore.exceptions import BotoCoreError, ClientError

        profile = os.environ.get('AWS_PROFILE', env)
        region = 'us-west-2'
        server_log("Glue Open Request", Profile=profile, Region=region)

        session = _boto3.Session(profile_name=profile, region_name=region)
        sts = session.client('sts')
        try:
            sts.get_caller_identity()
        except (BotoCoreError, ClientError) as e:
            msg = str(e)
            if 'expired' in msg.lower() or 'token' in msg.lower():
                return {'status': 'error', 'message': 'AWS SSO token expired. Please refresh token and try again.'}, 401
            return {'status': 'error', 'message': f'Failed to validate AWS credentials: {msg}'}, 500

        creds = session.get_credentials()
        if not creds:
            return {'status': 'error', 'message': 'No AWS credentials found for current profile. Please log in.'}, 401
        fc = creds.get_frozen_credentials()

        session_dict = {
            'sessionId': fc.access_key,
            'sessionKey': fc.secret_key,
            'sessionToken': fc.token,
        }
        session_json = _json.dumps(session_dict)
        get_token_url = (
                'https://signin.aws.amazon.com/federation?'
                + _urlparse.urlencode({
            'Action': 'getSigninToken',
            'SessionType': 'json',
            'Session': session_json,
        })
        )
        _ctx = _ssl._create_unverified_context()
        with _urlreq.urlopen(get_token_url, context=_ctx) as resp:
            body = resp.read().decode('utf-8')
            token = _json.loads(body).get('SigninToken')
        if not token:
            return {'status': 'error', 'message': 'Failed to obtain federation sign-in token'}, 500

        destination = f'https://console.aws.amazon.com/gluestudio/home?region={region}#/jobs'
        login_url = (
                'https://signin.aws.amazon.com/federation?'
                + _urlparse.urlencode({
            'Action': 'login',
            'Issuer': 'workbench-utility',
            'Destination': destination,
            'SigninToken': token,
        })
        )
        server_log("Glue URL", URL=login_url)
        return {'status': 'ok', 'url': login_url}
    except Exception as e:
        logger.error(f"/open-glue error: {e}", exc_info=True)
        return {'status': 'error', 'message': str(e)}, 500


@app.route('/open-s3', methods=['POST'])
def open_s3():
    """Open AWS S3 console via federation sign-in using current AWS profile."""
    try:
        import json as _json
        import urllib.parse as _urlparse
        import urllib.request as _urlreq
        import ssl as _ssl
        import boto3 as _boto3
        from botocore.exceptions import BotoCoreError, ClientError

        profile = os.environ.get('AWS_PROFILE', env)
        region = 'us-west-2'
        server_log("S3 Open Request", Profile=profile, Region=region)

        session = _boto3.Session(profile_name=profile, region_name=region)
        sts = session.client('sts')
        try:
            sts.get_caller_identity()
        except (BotoCoreError, ClientError) as e:
            msg = str(e)
            if 'expired' in msg.lower() or 'token' in msg.lower():
                return {'status': 'error', 'message': 'AWS SSO token expired. Please refresh token and try again.'}, 401
            return {'status': 'error', 'message': f'Failed to validate AWS credentials: {msg}'}, 500

        creds = session.get_credentials()
        if not creds:
            return {'status': 'error', 'message': 'No AWS credentials found for current profile. Please log in.'}, 401
        fc = creds.get_frozen_credentials()

        session_dict = {
            'sessionId': fc.access_key,
            'sessionKey': fc.secret_key,
            'sessionToken': fc.token,
        }
        session_json = _json.dumps(session_dict)
        get_token_url = (
                'https://signin.aws.amazon.com/federation?'
                + _urlparse.urlencode({
            'Action': 'getSigninToken',
            'SessionType': 'json',
            'Session': session_json,
        })
        )
        _ctx = _ssl._create_unverified_context()
        with _urlreq.urlopen(get_token_url, context=_ctx) as resp:
            body = resp.read().decode('utf-8')
            token = _json.loads(body).get('SigninToken')
        if not token:
            return {'status': 'error', 'message': 'Failed to obtain federation sign-in token'}, 500

        destination = f'https://console.aws.amazon.com/s3/home?region={region}'
        login_url = (
                'https://signin.aws.amazon.com/federation?'
                + _urlparse.urlencode({
            'Action': 'login',
            'Issuer': 'workbench-utility',
            'Destination': destination,
            'SigninToken': token,
        })
        )
        server_log("S3 URL", URL=login_url)
        return {'status': 'ok', 'url': login_url}
    except Exception as e:
        logger.error(f"/open-s3 error: {e}", exc_info=True)
        return {'status': 'error', 'message': str(e)}, 500


@app.route("/set-path", methods=["POST"])
def set_path():
    """Save path in session"""
    path = request.json.get('path', '')
    session['last_path'] = path
    return {'status': 'ok'}


@app.route("/update-csv-edit", methods=["POST"])
def update_csv_edit():
    """Update CSV edit cache via AJAX"""
    cache_key = request.json.get('cache_key')
    edits = request.json.get('edits', {})

    if cache_key:
        CSV_EDITS_CACHE[cache_key] = edits
        logger.info(f"Updated edits for {cache_key}: {len(edits)} edits")

    return {'status': 'ok', 'edit_count': len(edits)}


@app.route("/update-json-edit", methods=["POST"])
def update_json_edit():
    """Update JSON edit cache via AJAX"""
    cache_key = request.json.get('cache_key')
    record_index = request.json.get('record_index')
    field_path = request.json.get('field_path')
    value = request.json.get('value')
    data_type = request.json.get('data_type', 'string')

    if cache_key not in JSON_EDITS_CACHE:
        JSON_EDITS_CACHE[cache_key] = {}

    if record_index not in JSON_EDITS_CACHE[cache_key]:
        JSON_EDITS_CACHE[cache_key][record_index] = {}

    JSON_EDITS_CACHE[cache_key][record_index][field_path] = {
        'value': value,
        'type': data_type
    }

    logger.info(f"Updated JSON edit for {cache_key}, record {record_index}, field {field_path}")

    return {'status': 'ok'}


@app.route("/browse-s3", methods=["POST"])
def browse_s3():
    """Smart S3 browsing with intelligent caching and pagination support"""
    from botocore.exceptions import NoCredentialsError, ClientError

    try:
        path = request.json.get('path', '')
        module = request.json.get('module', 'dxp')
        force_refresh = request.json.get('force_refresh', False)

        if not path:
            return {'error': 'No path provided'}

        server_log("Browse S3", Path=path, Force_Refresh=force_refresh, Module=module)

        # Parse bucket and prefix
        parts = path.split('/', 1)
        bucket = parts[0]
        prefix = parts[1] if len(parts) > 1 else ''

        # Ensure prefix ends with / for folder listing
        if prefix and not prefix.endswith('/'):
            prefix += '/'

        cache_key = make_path_cache_key(bucket, prefix)
        logger.info(f"Cache key for {path}: {cache_key} (env: {os.environ.get('AWS_PROFILE', 'dev')})")

        # Check path-specific cache first (much longer cache time for better performance)
        with PATH_CACHE_LOCK:
            cache_exists = cache_key in PATH_CACHE
            logger.info(f"Cache check for {cache_key}: {'EXISTS' if cache_exists else 'MISS'}")
            # Debug: Show all cache keys that start with the same environment
            env_prefix = f"{os.environ.get('AWS_PROFILE', 'dev')}:"
            env_cache_keys = [k for k in PATH_CACHE.keys() if k.startswith(env_prefix)]
            logger.info(
                f"All cache keys for environment '{os.environ.get('AWS_PROFILE', 'dev')}': {env_cache_keys[:3]}...")

            if not force_refresh and cache_exists:
                cache_data = PATH_CACHE[cache_key]
                # Much longer cache time - 24 hours for better performance
                if cache_data['timestamp'] > time.time() - 86400:  # 24 hours
                    age = int(time.time() - cache_data['timestamp'])
                    server_log("Browse S3 - Cache Hit", Path=path, Cache_Age_Sec=age)
                    logger.info(f"Cache HIT for {path} (age: {age}s)")
                    return {
                        'items': cache_data['items'],
                        'cached': True,
                        'cache_age': age,
                        'total_items': len(cache_data['items'])
                    }
                else:
                    logger.info(f"Cache EXPIRED for {path} (age: {int(time.time() - cache_data['timestamp'])}s)")
            else:
                logger.info(f"Cache MISS for {path} (force_refresh: {force_refresh})")

        # Create S3 client with fresh session
        s3_client = get_fresh_s3_client()

        items = []
        folders_set = set()  # Use set to avoid duplicates

        # Pagination loop
        continuation_token = None
        page_count = 0
        total_objects = 0

        logger.info(f"Fetching from S3: {path}")

        while True:
            # Build request parameters
            list_params = {
                'Bucket': bucket,
                'Prefix': prefix,
                'Delimiter': '/',
                'MaxKeys': 1000
            }

            # Add continuation token if this is not the first page
            if continuation_token:
                list_params['ContinuationToken'] = continuation_token

            # Make the request
            response = s3_client.list_objects_v2(**list_params)
            page_count += 1

            # Process folders (common prefixes)
            if 'CommonPrefixes' in response:
                for prefix_info in response['CommonPrefixes']:
                    folder_path = prefix_info['Prefix']
                    folder_name = folder_path[len(prefix):].rstrip('/')
                    if folder_name and folder_name not in folders_set:
                        folders_set.add(folder_name)
                        items.append({
                            'name': folder_name,
                            'type': 'folder'
                        })

            # Process files
            if 'Contents' in response:
                total_objects += len(response['Contents'])
                for obj in response['Contents']:
                    key = obj['Key']
                    # Skip the prefix itself
                    if key == prefix:
                        continue

                    file_name = key[len(prefix):]
                    # Skip files in subfolders
                    if '/' in file_name:
                        continue

                    # Show all file types (removed restrictive filtering)
                    items.append({
                        'name': file_name,
                        'type': 'file',
                        'size': format_size(obj['Size']),
                        'modified': obj.get('LastModified', '').isoformat() if obj.get('LastModified') else ''
                    })

            # Check if there are more results
            if response.get('IsTruncated', False):
                continuation_token = response.get('NextContinuationToken')
                if not continuation_token:
                    logger.warning("IsTruncated is True but no NextContinuationToken found")
                    break
            else:
                # No more results
                break

            # Log progress for large listings
            if page_count % 5 == 0:
                logger.info(
                    f"Still fetching... processed {page_count} pages, {total_objects} objects, {len(items)} items so far")

        server_log("Browse S3 - Fetch Complete", Path=path, Pages=page_count, Objects=total_objects, Items=len(items))

        # Add debugging information to help track missing files
        if total_objects > len(items):
            logger.warning(f"Note: {total_objects - len(items)} objects were processed but not included in results")
            logger.warning(f"This could be due to: prefix matches, subfolder files, or other filtering")

        # Sort items: folders first, then files
        items.sort(key=lambda x: (x['type'] == 'file', x['name'].lower()))

        # Update path cache
        with PATH_CACHE_LOCK:
            PATH_CACHE[cache_key] = {
                'items': items,
                'timestamp': time.time()
            }
            logger.info(f"Cache UPDATED for {path} (key: {cache_key})")
        _prune_path_cache()
        _persist_path_cache()

        # Also update the main bucket cache if it exists
        update_bucket_cache_path(bucket, prefix, items)

        # Auto-cache parent paths for faster navigation
        if prefix:
            parent_prefix = '/'.join(prefix.rstrip('/').split('/')[:-1])
            if parent_prefix:
                parent_prefix += '/'
                parent_cache_key = make_path_cache_key(bucket, parent_prefix)
                # Only cache parent if not already cached
                with PATH_CACHE_LOCK:
                    if parent_cache_key not in PATH_CACHE:
                        logger.info(f"Auto-caching parent path: {bucket}/{parent_prefix}")
                        # This will be cached when user navigates to parent

        return {
            'items': items,
            'cached': False,
            'cache_age': 0,
            'total_items': len(items),
            'pages_fetched': page_count
        }

    except NoCredentialsError:
        return {'error': 'AWS credentials not found. Please configure your AWS credentials.'}
    except ClientError as e:
        error_code = e.response['Error']['Code']
        if error_code == 'NoSuchBucket':
            return {'error': f'Bucket "{bucket}" does not exist'}
        elif error_code == 'AccessDenied':
            return {'error': f'Access denied to bucket "{bucket}"'}
        else:
            return {'error': f'AWS Error: {str(e)}'}
    except Exception as e:
        logger.error(f"Error browsing S3: {e}", exc_info=True)
        return {'error': str(e)}


@app.route('/delete-s3', methods=['POST'])
def delete_s3():
    """Delete a single S3 object and refresh caches for its parent path"""
    try:
        data = request.get_json(force=True)
        bucket = data.get('bucket', '')
        key = data.get('key', '')
        if not bucket or not key:
            return jsonify({'success': False, 'error': 'bucket and key are required'}), 400

        s3_client = get_fresh_s3_client()
        s3_client.delete_object(Bucket=bucket, Key=key)

        # Invalidate parent path cache
        prefix = key.rsplit('/', 1)[0] + '/' if '/' in key else ''
        cache_key = make_path_cache_key(bucket, prefix)
        with PATH_CACHE_LOCK:
            if cache_key in PATH_CACHE:
                del PATH_CACHE[cache_key]
        _persist_path_cache()

        return jsonify({'success': True})
    except Exception as e:
        logger.error(f"Error deleting s3://{bucket}/{key}: {e}", exc_info=True)
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route("/refresh-s3-path", methods=["POST"])
def refresh_s3_path():
    """Refresh only the current path"""
    path = request.json.get('path', '')
    module = request.json.get('module', 'dxp')

    if not path:
        return {'error': 'No path provided'}

    # Clear path cache for this specific path
    parts = path.split('/', 1)
    bucket = parts[0]
    prefix = parts[1] if len(parts) > 1 else ''

    if prefix and not prefix.endswith('/'):
        prefix += '/'

    cache_key = make_path_cache_key(bucket, prefix)

    # Remove from path cache
    with PATH_CACHE_LOCK:
        if cache_key in PATH_CACHE:
            del PATH_CACHE[cache_key]
    _persist_path_cache()

    # Now fetch fresh data
    return browse_s3()


@app.route("/prefetch-s3-paths", methods=["POST"])
def prefetch_s3_paths():
    """Prefetch multiple paths in parallel"""

    paths = request.json.get('paths', [])
    module = request.json.get('module', 'dxp')

    if not paths:
        return {'status': 'no_paths'}

    s3_client = get_fresh_s3_client()

    def fetch_path(path):
        try:
            parts = path.split('/', 1)
            bucket = parts[0]
            prefix = parts[1] if len(parts) > 1 else ''

            if prefix and not prefix.endswith('/'):
                prefix += '/'

            items = []
            folders_set = set()  # Use set to avoid duplicates
            continuation_token = None

            # Pagination loop to get all items
            while True:
                list_params = {
                    'Bucket': bucket,
                    'Prefix': prefix,
                    'Delimiter': '/',
                    'MaxKeys': 1000
                }

                if continuation_token:
                    list_params['ContinuationToken'] = continuation_token

                response = s3_client.list_objects_v2(**list_params)

                if 'CommonPrefixes' in response:
                    for prefix_info in response['CommonPrefixes']:
                        folder_path = prefix_info['Prefix']
                        folder_name = folder_path[len(prefix):].rstrip('/')
                        if folder_name and folder_name not in folders_set:
                            folders_set.add(folder_name)
                            items.append({
                                'name': folder_name,
                                'type': 'folder'
                            })

                if 'Contents' in response:
                    for obj in response['Contents']:
                        key = obj['Key']
                        if key == prefix:
                            continue

                        file_name = key[len(prefix):]
                        if '/' in file_name:
                            continue

                        # Show all file types (removed restrictive filtering)
                        items.append({
                            'name': file_name,
                            'type': 'file',
                            'size': format_size(obj['Size']),
                            'modified': obj.get('LastModified', '').isoformat() if obj.get('LastModified') else ''
                        })

                # Check if there are more results
                if response.get('IsTruncated', False):
                    continuation_token = response.get('NextContinuationToken')
                    if not continuation_token:
                        break
                else:
                    break

            # Sort items: folders first, then files
            items.sort(key=lambda x: (x['type'] == 'file', x['name'].lower()))

            # Cache the result
            cache_key = f"{bucket}:{prefix}"
            with PATH_CACHE_LOCK:
                PATH_CACHE[cache_key] = {
                    'items': items,
                    'timestamp': time.time()
                }

            return path, True
        except Exception as e:
            logger.error(f"Error prefetching {path}: {e}")
            return path, False

    # Prefetch in parallel
    with ThreadPoolExecutor(max_workers=min(len(paths), 10)) as executor:
        futures = [executor.submit(fetch_path, path) for path in paths[:20]]  # Limit to 20 paths
        results = []
        for future in as_completed(futures):
            path, success = future.result()
            results.append({'path': path, 'success': success})

    return {'status': 'prefetched', 'results': results}


@app.route("/cache-s3-bucket-smart", methods=["POST"])
def cache_s3_bucket_smart():
    """Smart bucket caching that starts with visible paths"""

    bucket = request.json.get('bucket', '')
    initial_path = request.json.get('initial_path', '')
    module = request.json.get('module', 'dxp')

    if not bucket:
        return {'error': 'No bucket provided'}

    def cache_bucket_progressive():
        """Progressive caching that prioritizes visible content"""
        try:
            s3_client = get_fresh_s3_client()
            server_log("S3 Smart Cache", Bucket=bucket, Initial_Path=initial_path or '(root)')

            with CACHE_LOCK:
                if bucket not in S3_BUCKET_CACHE:
                    S3_BUCKET_CACHE[bucket] = {
                        'tree': {'folders': {}, 'files': []},
                        'status': 'caching',
                        'cached_paths': set(),
                        'total_paths': 0
                    }

            # Priority queue for paths to cache
            priority_paths = []

            # Add initial path and its parents to priority
            if initial_path:
                parts = initial_path.split('/')
                for i in range(len(parts)):
                    priority_paths.append('/'.join(parts[:i + 1]) + '/')

            # Add root
            priority_paths.insert(0, '')

            # Process priority paths first
            for path in priority_paths:
                try:
                    server_log("S3 Smart Cache - Priority Path", Bucket=bucket, Path=path or '(root)')
                    cache_single_path(s3_client, bucket, path)
                except Exception as e:
                    logger.error(f"Error caching priority path {path}: {e}")

            # Then continue with full bucket scan in background
            paginator = s3_client.get_paginator('list_objects_v2')
            all_prefixes = set()

            for page in paginator.paginate(
                    Bucket=bucket,
                    Delimiter='/'
            ):
                if 'CommonPrefixes' in page:
                    for prefix_info in page['CommonPrefixes']:
                        all_prefixes.add(prefix_info['Prefix'])

            # Cache remaining prefixes
            with ThreadPoolExecutor(max_workers=20) as executor:
                remaining = all_prefixes - set(priority_paths)
                futures = []

                for prefix in sorted(remaining):
                    server_log("S3 Smart Cache - Enqueue", Bucket=bucket, Prefix=prefix)
                    future = executor.submit(cache_single_path, s3_client, bucket, prefix)
                    futures.append(future)

                # Process results
                for future in as_completed(futures):
                    try:
                        future.result()
                    except Exception as e:
                        logger.error(f"Error in parallel caching: {e}")

            # Mark as complete
            with CACHE_LOCK:
                if bucket in S3_BUCKET_CACHE:
                    S3_BUCKET_CACHE[bucket]['status'] = 'ready'
                else:
                    S3_BUCKET_CACHE[bucket] = {
                        'tree': {'folders': {}, 'files': []},
                        'status': 'ready',
                        'cached_paths': set(),
                        'total_paths': 0
                    }
                server_log("S3 Smart Cache - Complete", Bucket=bucket, Status="ready")

        except Exception as e:
            logger.error(f"Error in smart caching: {e}")
            with CACHE_LOCK:
                if bucket in S3_BUCKET_CACHE:
                    S3_BUCKET_CACHE[bucket]['status'] = 'error'
                    S3_BUCKET_CACHE[bucket]['error'] = str(e)
                else:
                    S3_BUCKET_CACHE[bucket] = {
                        'tree': {'folders': {}, 'files': []},
                        'status': 'error',
                        'error': str(e),
                        'cached_paths': set(),
                        'total_paths': 0
                    }
            server_log("S3 Smart Cache - Complete", Bucket=bucket, Status="error")

    def cache_single_path(s3_client, bucket, prefix):
        """Cache a single path with pagination support"""
        items = []
        folders_set = set()
        continuation_token = None
        page_count = 0
        total_objects = 0

        try:
            while True:
                # Build request parameters
                list_params = {
                    'Bucket': bucket,
                    'Prefix': prefix,
                    'Delimiter': '/',
                    'MaxKeys': 1000
                }

                if continuation_token:
                    list_params['ContinuationToken'] = continuation_token

                response = s3_client.list_objects_v2(**list_params)
                page_count += 1

                # Process folders (common prefixes)
                if 'CommonPrefixes' in response:
                    for prefix_info in response['CommonPrefixes']:
                        folder_path = prefix_info['Prefix']
                        folder_name = folder_path[len(prefix):].rstrip('/')
                        if folder_name and folder_name not in folders_set:
                            folders_set.add(folder_name)
                            items.append({
                                'name': folder_name,
                                'type': 'folder'
                            })

                # Process files
                if 'Contents' in response:
                    total_objects += len(response['Contents'])
                    for obj in response['Contents']:
                        key = obj['Key']
                        if key == prefix:
                            continue

                        file_name = key[len(prefix):]
                        if '/' in file_name:
                            continue

                        # Show all file types (removed restrictive filtering)
                        items.append({
                            'name': file_name,
                            'type': 'file',
                            'size': format_size(obj['Size']),
                            'modified': obj.get('LastModified', '').isoformat() if obj.get('LastModified') else ''
                        })

                # Check if there are more results
                if not response.get('IsTruncated', False):
                    break

                continuation_token = response.get('NextContinuationToken')
                if not continuation_token:
                    logger.warning(f"IsTruncated is True but no NextContinuationToken found for {bucket}/{prefix}")
                    break

            server_log("S3 Smart Cache - Path Cached", Bucket=bucket, Prefix=prefix or '(root)', Items=len(items),
                       Pages=page_count)

            # Log progress for very large directories
            if page_count % 10 == 0:
                logger.debug(f"Cache progress for {bucket}/{prefix}: {page_count} pages, {len(items)} items")

            # Sort items: folders first, then files
            items.sort(key=lambda x: (x['type'] == 'file', x['name'].lower()))

            # Update bucket cache
            update_bucket_cache_path(bucket, prefix, items)

            # Also update path cache
            cache_key = f"{bucket}:{prefix}"
            with PATH_CACHE_LOCK:
                PATH_CACHE[cache_key] = {
                    'items': items,
                    'timestamp': time.time()
                }

            with CACHE_LOCK:
                if bucket in S3_BUCKET_CACHE:
                    S3_BUCKET_CACHE[bucket]['cached_paths'].add(prefix)

            logger.info(f"Cached path {bucket}/{prefix}: {len(items)} items across {page_count} pages")

        except Exception as e:
            logger.error(f"Error caching path {bucket}/{prefix}: {e}")
            raise

    # Start caching in background
    thread = threading.Thread(target=cache_bucket_progressive)
    thread.daemon = True
    thread.start()

    return {'status': 'started'}


@app.route("/get-cache-status", methods=["POST"])
def get_cache_status():
    """Get detailed cache status"""
    bucket = request.json.get('bucket', '')

    with CACHE_LOCK:
        if bucket in S3_BUCKET_CACHE:
            cache = S3_BUCKET_CACHE[bucket]
            return {
                'status': cache.get('status', 'unknown'),
                'cached_paths': len(cache.get('cached_paths', [])),
                'total_paths': cache.get('total_paths', 0)
            }

    return {'status': 'not_cached'}


@app.route("/clear-path-cache", methods=["POST"])
def clear_path_cache():
    """Clear cache for specific paths or all"""
    paths = request.json.get('paths', [])
    clear_all = request.json.get('clear_all', False)

    if clear_all:
        with PATH_CACHE_LOCK:
            PATH_CACHE.clear()
        return {'status': 'cleared_all'}

    cleared = []
    with PATH_CACHE_LOCK:
        for path in paths:
            parts = path.split('/', 1)
            bucket = parts[0]
            prefix = parts[1] if len(parts) > 1 else ''

            if prefix and not prefix.endswith('/'):
                prefix += '/'

            cache_key = f"{bucket}:{prefix}"
            if cache_key in PATH_CACHE:
                del PATH_CACHE[cache_key]
                cleared.append(path)

    return {'status': 'cleared', 'cleared_paths': cleared}


@app.route("/download", methods=["POST"])
def download():
    try:
        result = download_file()
        return result
    except Exception as e:
        logger.error(f"Download error: {e}", exc_info=True)

        # Build friendly message
        msg = None
        if isinstance(e, ClientError):
            error_code = e.response.get('Error', {}).get('Code', 'Unknown')
            error_message = e.response.get('Error', {}).get('Message', 'Unknown error')
            if any(k in (error_code or '').lower() for k in ['token', 'expired', 'invalid']) or any(
                    k in (error_message or '').lower() for k in ['token', 'expired', 'invalid']):
                msg = f"AWS Token Expired: {error_code} - {error_message}\n\nPlease refresh your AWS token and try again."
        if not msg:
            msg = f"Error downloading file: {str(e)}"

        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }})();
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )


@app.route("/download-all", methods=["POST"])
def download_all():
    try:
        data = request.json or {}
        s3_path = (data.get('path') or '').strip()
        module = data.get('module') or session.get('module', 'dxp')
        if not s3_path or not s3_path.lower().startswith('s3://'):
            return {'status': 'error', 'message': 'Provide a valid S3 path starting with s3://'}, 400
        s3_path_clean = s3_path[5:]
        parts = s3_path_clean.split('/', 1)
        bucket = parts[0]
        prefix = parts[1] if len(parts) > 1 else ''
        if prefix and not prefix.endswith('/'):
            prefix += '/'
        job_id = str(uuid.uuid4())
        with BATCH_LOCK:
            BATCH_DOWNLOADS[job_id] = {
                'status': 'running',
                'bucket': bucket,
                'prefix': prefix,
                'module': module,
                'total': 0,
                'done': 0,
                'saved': 0,
                'errors': [],
                'current_key': None,
                'last_saved': None,
                'recent_saved': [],
                'saved_files': [],
                'started_at': time.time(),
                'finished_at': None,
            }
        try:
            server_log("Download All Start", Bucket=bucket, Prefix=prefix, Module=module, Job_Id=job_id)
        except Exception:
            pass
        try:
            home_dir = os.path.expanduser('~')
            DXP_LOGGER.info(
                f"Extract Job Start - Job_Id: {job_id} - Module: {module} - Source: s3://{bucket}/{prefix} - Dest Root: {os.path.join(home_dir, bucket)}")
        except Exception:
            pass

        def worker():
            try:
                s3_client = get_fresh_s3_client()
                paginator = s3_client.get_paginator('list_objects_v2')
                total = 0
                for page in paginator.paginate(Bucket=bucket, Prefix=prefix):
                    contents = page.get('Contents', [])
                    for obj in contents:
                        key = obj.get('Key')
                        if not key or key.endswith('/'):
                            continue
                        total += 1
                with BATCH_LOCK:
                    if job_id in BATCH_DOWNLOADS:
                        BATCH_DOWNLOADS[job_id]['total'] = total
                        # Collect unique folder paths that contain downloaded files
                folder_set = set()
                for page in paginator.paginate(Bucket=bucket, Prefix=prefix):
                    contents = page.get('Contents', [])
                    for obj in contents:
                        key = obj.get('Key')
                        if not key or key.endswith('/'):
                            continue
                        try:
                            with BATCH_LOCK:
                                if job_id in BATCH_DOWNLOADS:
                                    BATCH_DOWNLOADS[job_id]['current_key'] = key
                            s3_uri = f"s3://{bucket}/{key}"
                            home_dir = os.path.expanduser('~')
                            local_path = os.path.join(home_dir, bucket, key)
                            try:
                                server_log("Download Object", From=s3_uri, To=local_path)
                            except Exception:
                                pass
                            raw = S3Utils(verify=False).read_key(s3_uri, utf_decode=False, module=module)
                            # Decrypt if encrypted; otherwise download as-is
                            if isinstance(raw, (bytes, bytearray)) and raw.startswith(b"ENC"):
                                try:
                                    crypto_api = get_cached_crypto_api(module, "batch_download")
                                    raw = crypto_api.decrypt(raw)
                                except Exception as dec_err:
                                    logger.error(f"Decrypt failed for {s3_uri}: {dec_err}", exc_info=True)
                                    raise
                            if key.lower().endswith('.gz'):
                                try:
                                    raw = gzip.decompress(raw)
                                except Exception:
                                    pass
                            os.makedirs(os.path.dirname(local_path), exist_ok=True)
                            with open(local_path, 'wb') as f:
                                f.write(raw if isinstance(raw, (bytes, bytearray)) else str(raw).encode('utf-8'))
                            try:
                                server_log("Saved Object", To=local_path)
                            except Exception:
                                pass
                            # Track folder for this file
                            try:
                                dirpath = os.path.dirname(key)
                                if dirpath:
                                    folder_set.add(dirpath)
                            except Exception:
                                pass
                            with BATCH_LOCK:
                                if job_id in BATCH_DOWNLOADS:
                                    BATCH_DOWNLOADS[job_id]['saved'] += 1
                                    BATCH_DOWNLOADS[job_id]['last_saved'] = key
                                    rs = BATCH_DOWNLOADS[job_id]['recent_saved']
                                    rs.append(key)
                                    if len(rs) > 5:
                                        del rs[0]
                                    BATCH_DOWNLOADS[job_id]['saved_files'].append(key)
                        except Exception as ex:
                            # log error to server log
                            try:
                                server_log("Download All Error", Key=key, Error=str(ex), From=s3_uri, To=local_path)
                            except Exception:
                                pass
                            logger.error(f"Download All error for key s3://{bucket}/{key}: {ex}", exc_info=True)
                            with BATCH_LOCK:
                                if job_id in BATCH_DOWNLOADS:
                                    BATCH_DOWNLOADS[job_id]['errors'].append(
                                        {'key': key, 'error': str(ex), 'from': s3_uri, 'to': local_path})
                        finally:
                            with BATCH_LOCK:
                                if job_id in BATCH_DOWNLOADS:
                                    BATCH_DOWNLOADS[job_id]['done'] += 1
                # Summarize folders, files, and errors
                try:
                    with BATCH_LOCK:
                        if job_id in BATCH_DOWNLOADS:
                            BATCH_DOWNLOADS[job_id]['folder_count'] = len(folder_set)
                            BATCH_DOWNLOADS[job_id]['file_total'] = BATCH_DOWNLOADS[job_id].get('total', 0)
                except Exception:
                    pass
                with BATCH_LOCK:
                    if job_id in BATCH_DOWNLOADS:
                        BATCH_DOWNLOADS[job_id]['status'] = 'completed'
                        BATCH_DOWNLOADS[job_id]['finished_at'] = time.time()
                        err_count = len(BATCH_DOWNLOADS[job_id].get('errors', []))
                        saved_count = BATCH_DOWNLOADS[job_id].get('saved', 0)
                        total_count = BATCH_DOWNLOADS[job_id].get('total', 0)
                        folder_count = BATCH_DOWNLOADS[job_id].get('folder_count', 0)
                        try:
                            server_log(
                                "Download All Complete",
                                Bucket=bucket,
                                Prefix=prefix,
                                Folders=folder_count,
                                Files=saved_count,
                                Total=total_count,
                                Errors=err_count,
                            )
                        except Exception:
                            pass
                try:
                    server_log("Download All End", Bucket=bucket, Prefix=prefix, Module=module, Job_Id=job_id)
                except Exception:
                    pass
            except Exception as e:
                logger.error(f"Download-all worker error: {e}", exc_info=True)
                with BATCH_LOCK:
                    if job_id in BATCH_DOWNLOADS:
                        BATCH_DOWNLOADS[job_id]['status'] = 'error'
                        BATCH_DOWNLOADS[job_id]['errors'].append({'error': str(e)})
                        BATCH_DOWNLOADS[job_id]['finished_at'] = time.time()

        t = threading.Thread(target=worker, daemon=True)
        t.start()
        return {'status': 'started', 'job_id': job_id}
    except Exception as e:
        logger.error(f"/download-all error: {e}", exc_info=True)
        return {'status': 'error', 'message': str(e)}, 500


@app.route("/download-all-status", methods=["POST"])
def download_all_status():
    try:
        job_id = (request.json or {}).get('job_id')
        if not job_id:
            return {'status': 'error', 'message': 'job_id required'}, 400
        with BATCH_LOCK:
            job = BATCH_DOWNLOADS.get(job_id)
            if not job:
                return {'status': 'error', 'message': 'job not found'}, 404
            total = job.get('total', 0)
            done = job.get('done', 0)
            saved = job.get('saved', 0)
            err_count = len(job.get('errors', []))
            percent = int((done / total) * 100) if total else (
                100 if job.get('status') in ('completed', 'error') else 0)
            return {
                'status': job.get('status'),
                'total': total,
                'done': done,
                'saved': saved,
                'errors': job.get('errors', []),
                'error_count': err_count,
                'folder_count': job.get('folder_count', 0),
                'file_total': job.get('file_total', total),
                'percent': percent,
                'current_key': job.get('current_key'),
                'last_saved': job.get('last_saved'),
                'recent_saved': job.get('recent_saved', []),
                'saved_files': job.get('saved_files', []),
            }
    except Exception as e:
        logger.error(f"/download-all-status error: {e}", exc_info=True)
        return {'status': 'error', 'message': str(e)}, 500


@app.route("/encrypt-upload", methods=["POST"])
def encrypt_upload():
    try:
        server_log("Upload - Encrypt Start")

        # Extract parameters
        s3_path = request.form.get("s3_path", "").strip()
        module = request.form.get("module", "dxp")
        upload_id = session.get("upload_id")

        server_log("Upload - Encrypt", S3_Path=s3_path, Module=module, Upload_Id=upload_id)

        if not s3_path:
            logger.error("No S3 path provided for upload")
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {"No S3 path provided for upload"!r}); }} catch(e) {{}}
                        window.location = '{url_for('home')}';
                      }})();
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )

        if not s3_path.lower().startswith('s3://'):
            logger.error(f"Invalid S3 path format: {s3_path}")
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {"Please provide a valid S3 path starting with s3://"!r}); }} catch(err) {{}}
                        window.location = '{url_for('home')}';
                      }})();
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )

        # Check for file upload in this request
        upload = request.files.get("upload_file")
        if upload and upload.filename:
            logger.info(f"File uploaded in encrypt-upload request: {upload.filename}")
            # Handle file upload
            raw_bytes = upload.read()
            tmp = tempfile.NamedTemporaryFile(delete=False)
            tmp.write(raw_bytes)
            tmp.close()

            upload_id = str(uuid.uuid4())
            LOCAL_UPLOADS[upload_id] = tmp.name
            session["upload_id"] = upload_id
            session["upload_filename"] = upload.filename

            server_log("Upload Temp File", Path=tmp.name, Upload_Id=upload_id)
        elif not upload_id or upload_id not in LOCAL_UPLOADS:
            logger.error(f"No local file found for upload_id: {upload_id}")
            logger.error(f"Available upload_ids: {list(LOCAL_UPLOADS.keys())}")
            flash("No local file selected for upload")
            return redirect(url_for("home"))

        # Read the local file
        local_file_path = LOCAL_UPLOADS[upload_id]
        server_log("Upload", From=local_file_path, To=s3_path)

        if not os.path.exists(local_file_path):
            logger.error(f"Local file does not exist: {local_file_path}")
            flash("Local file not found. Please select the file again.")
            return redirect(url_for("home"))

        with open(local_file_path, "rb") as f:
            file_content = f.read()

        logger.info(f"File read successfully - Size: {len(file_content)} bytes")

        # Determine file format based on original uploaded filename (not temp path)
        selected_name = session.get("upload_filename") or (
            upload.filename if upload and upload.filename else os.path.basename(local_file_path))
        selected_lower = selected_name.lower()
        file_extension = os.path.splitext(selected_lower)[1]
        server_log("Upload Source Name", Selected=selected_name, Extension=file_extension)

        # Set format for S3Utils.put_object
        if file_extension in ['.xlsx', '.xls']:
            format_type = "xlsx"
        elif file_extension in ['.csv', '.csv.gz']:
            format_type = "csv"
        elif file_extension in ['.json', '.jsonl', '.json.gz', '.jsonl.gz']:
            format_type = "json"
        else:
            format_type = "str"  # Default for binary files

        logger.info(f"Using format type: {format_type}")

        # Enforce S3 target extension compatibility with selected file (allow only matching or non-gz -> gz upgrade)
        target_lower = s3_path.lower()

        def ext_core(name):
            # Return logical type: 'csv','json','jsonl','xlsx','xls', or others; and gz flag
            if name.endswith('.csv.gz'): return ('csv', True)
            if name.endswith('.jsonl.gz'): return ('jsonl', True)
            if name.endswith('.json.gz'): return ('json', True)
            if name.endswith('.csv'): return ('csv', False)
            if name.endswith('.jsonl'): return ('jsonl', False)
            if name.endswith('.json'): return ('json', False)
            if name.endswith('.xlsx'): return ('xlsx', False)
            if name.endswith('.xls'): return ('xls', False)
            return (os.path.splitext(name)[1].lstrip('.'), False)

        sel_core, sel_gz = ext_core(selected_lower)
        tgt_core, tgt_gz = ext_core(target_lower)
        # Allow: exact match; or same core where selected is not gz and target is gz
        allowed = (sel_core == tgt_core and sel_gz == tgt_gz) or (sel_core == tgt_core and not sel_gz and tgt_gz)
        if not allowed:
            logger.error(
                f"Extension mismatch: selected={selected_name} ({sel_core}{'.gz' if sel_gz else ''}), target={s3_path} ({tgt_core}{'.gz' if tgt_gz else ''})")
            flash(f"Selected file type does not match S3 target. Selected {selected_name} → Target {s3_path}")
            return redirect(url_for("home"))

        # Upload to S3 using put_object method
        s3_utils = S3Utils(verify=False)

        # For binary files, we need to handle them differently
        if format_type == "str":
            # Binary file - encrypt first, then upload as bytes
            logger.info("Processing binary file - encrypting content")
            crypto_api = get_cached_crypto_api(module, "save_encrypt")
            encrypted_content = crypto_api.encrypt(file_content)
            logger.info(f"Content encrypted successfully - Size: {len(encrypted_content)} bytes")

            # Upload encrypted binary content
            response = s3_utils.put_object(
                file_path=s3_path,
                content=encrypted_content,
                format="str",
                cse_encrypt=False,  # Already encrypted
                module=module
            )
        else:
            # Text-based file - gzip first if target ends with .gz, then encrypt via S3Utils
            logger.info("Processing text-based file")
            target_lower = s3_path.lower()
            is_gz_target = target_lower.endswith('.gz')

            if is_gz_target:
                try:
                    raw_bytes = file_content if isinstance(file_content, (bytes, bytearray)) else str(
                        file_content).encode('utf-8')
                    gz_bytes = gzip.compress(raw_bytes)
                    logger.info(f"Gzipped text content from {len(raw_bytes)} -> {len(gz_bytes)} bytes")
                    put_fmt = 'bytes'
                    put_content = gz_bytes
                except Exception as gz_err:
                    logger.warning(f"Gzip failed; uploading uncompressed as text: {gz_err}")
                    put_fmt = 'text'
                    try:
                        put_content = file_content.decode('utf-8')
                    except Exception:
                        put_content = str(file_content)
            else:
                # Non-gz target: upload text as UTF-8 string to avoid b'..' artifacts
                put_fmt = 'text'
                try:
                    put_content = file_content.decode('utf-8')
                except Exception:
                    put_content = str(file_content)

            response = s3_utils.put_object(
                file_path=s3_path,
                content=put_content,
                format=put_fmt,
                cse_encrypt=True,
                module=module
            )

        server_log("S3 Upload Done", S3_Path=s3_path, Response=response)
        flash(f"File encrypted and uploaded successfully to {s3_path}")
        server_log("Upload - Encrypt Completed")

        # Update the last_path to the new upload path
        session['last_path'] = s3_path
        # Set a flag to preserve session data when redirecting back to home
        session['from_encrypt_upload'] = True
        session.modified = True
        return redirect(url_for("home"))

    except Exception as e:
        logger.error(f"Encrypt upload error: {e}", exc_info=True)
        flash(f"Error encrypting and uploading file: {str(e)}")
        return redirect(url_for("home"))


@app.route("/save", methods=["POST"])
def save():
    # 0) pull in form bits
    upload_id = session.get("upload_id", None)
    original_path = (
            request.form.get("orig_s3_path", "").strip() or request.form["s3_path"].strip()
    )
    target_path = request.form["s3_path"].strip()
    module = request.form.get("module", "dxp")
    file_type = request.form["file_type"]  # how it was opened (csv or json)
    gz_flag = request.form.get("gzipped") == "True"
    cache_key = request.form.get("cache_key", "")
    all_edits_json = request.form.get("all_edits", "{}")
    page = int(request.form.get("page", 1))
    original_decryption_module = request.form.get("decryption_module", module)

    # Parse all edits
    try:
        all_edits = json.loads(all_edits_json)
    except:
        all_edits = {}

    # Get delimiters
    raw_detect = request.form.get("detected_delimiter", "")
    if raw_detect.startswith("\\u"):
        try:
            parse_sep = chr(int(raw_detect[2:], 16))
        except:
            parse_sep = ","
    else:
        parse_sep = raw_detect or ","

    # out_sep ← what the user typed (visible "delimiter" box)
    raw_out = request.form.get("delimiter", "").strip()
    if raw_out.startswith("\\u"):
        try:
            out_sep = chr(int(raw_out[2:], 16))
        except:
            out_sep = parse_sep
    else:
        out_sep = raw_out or parse_sep

    # Check if we should allow saving
    should_save = False
    reason = ""

    if all_edits:
        should_save = True
        reason = "edits"
    elif target_path != original_path:
        should_save = True
        reason = "path change"
    elif parse_sep != out_sep:
        should_save = True
        reason = "delimiter change"
    else:
        # Check for format conversion
        orig_ext = os.path.splitext(original_path.lower())[1]
        target_ext = os.path.splitext(target_path.lower())[1]

        # Remove .gz for comparison
        orig_ext = orig_ext.replace('.gz', '')
        target_ext = target_ext.replace('.gz', '')

        if orig_ext != target_ext:
            should_save = True
            reason = "format conversion"
        else:
            # Allow overwrite - user explicitly clicked save
            should_save = True
            reason = "overwrite"

    logger.info(f"Save decision: should_save={should_save}, reason={reason}, edits={len(all_edits)}")
    logger.info(f"Module for save operation: {module}")
    logger.info(f"Original decryption module: {original_decryption_module}")
    server_log("Save", From=original_path, To=target_path)

    # Save path to session only if it's a valid S3 path
    if target_path.lower().startswith('s3://'):
        session['last_path'] = target_path

    # 1) infer output type + compression from target_path
    tp = target_path.lower()
    if tp.endswith(".json.gz"):
        out_type, gz_out = "json", True
    elif tp.endswith(".json"):
        out_type, gz_out = "json", False
    elif tp.endswith(".jsonl.gz"):
        out_type, gz_out = "jsonl", True
    elif tp.endswith(".jsonl"):
        out_type, gz_out = "jsonl", False
    elif tp.endswith(".csv.gz"):
        out_type, gz_out = "csv", True
    elif tp.endswith(".csv"):
        out_type, gz_out = "csv", False
    else:
        out_type, gz_out = file_type, gz_flag

    # 3) Get full DataFrame - prefer cache
    if cache_key in CSV_DATA_CACHE and file_type == "csv":
        # Use cached DataFrame (which is in ORIGINAL order, not sorted)
        cached_data = CSV_DATA_CACHE[cache_key]
        full_df = cached_data['dataframe'].copy()
        parse_sep = cached_data['delimiter']

        # Sort the DataFrame by first column (same as display)
        if len(full_df.columns) > 0:
            first_col = full_df.columns[0]
            full_df = full_df.sort_values(
                by=first_col, key=lambda col: col.astype(str), ignore_index=True
            )
            logger.info(f"Sorted DataFrame by column '{first_col}' before applying edits")

        # Apply ALL edits from all pages
        # Note: edits use row indices from the SORTED DataFrame
        for edit_key, value in all_edits.items():
            row_idx, col_idx = map(int, edit_key.split(','))
            if row_idx < len(full_df) and col_idx < len(full_df.columns):
                col_name = full_df.columns[col_idx]
                old_value = full_df.iloc[row_idx, col_idx]
                full_df.iloc[row_idx, col_idx] = value
                logger.info(f"Edit applied: Row {row_idx}, Col {col_idx} ({col_name}): '{old_value}' -> '{value}'")
            else:
                logger.warning(f"Edit out of bounds: Row {row_idx}, Col {col_idx}, DataFrame shape: {full_df.shape}")

        logger.info(f"Applied {len(all_edits)} edits to sorted DataFrame")
    else:
        # Fallback to original method if no cache
        # 4) load full original bytes (local-temp or S3), decrypt + gunzip
        if upload_id and upload_id in LOCAL_UPLOADS:
            try:
                with open(LOCAL_UPLOADS[upload_id], "rb") as f:
                    raw = f.read()
            except Exception as e:
                logger.error(f"Error reading local upload: {e}")
                flash(f"Error reading uploaded file: {str(e)}")
                return redirect(url_for("home"))
        else:
            logger.info(f"Reading S3 key {original_path} using module: {original_decryption_module}")
            raw = S3Utils(verify=False).read_key(
                original_path, utf_decode=False, module=original_decryption_module
            )

        if isinstance(raw, (bytes, bytearray)) and raw.startswith(b"ENC"):
            logger.info(f"Decrypting file using module: {original_decryption_module}")
            logger.info(f"CRYPTO DEBUG - Save operation - Environment: {env}, Module: {original_decryption_module}")
            crypto_api = get_cached_crypto_api(original_decryption_module, "save_decrypt")
            logger.info(
                f"CRYPTO DEBUG - Save operation - CryptoAPI instance created for module: {original_decryption_module}")
            raw = crypto_api.decrypt(raw)
            logger.info(f"CRYPTO DEBUG - Save operation - Decryption completed")
        # Decompress if actually gzipped or target suggests gz
        try:
            if gz_flag or (isinstance(raw, (bytes, bytearray)) and raw[:2] == b"\x1f\x8b"):
                raw = gzip.decompress(raw)
                gz_flag = True
        except Exception:
            pass

        # Robust decode: try utf-8, then common fallbacks
        if isinstance(raw, (bytes, bytearray)):
            # Check if this is a binary file type that shouldn't be decoded as text
            path_lower = original_path.lower()
            is_binary_file = (path_lower.endswith(
                (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tiff", ".webp", ".svg", ".mp4", ".avi", ".mov", ".mp3",
                 ".wav", ".zip", ".rar", ".pdf", ".xlsx", ".xls", ".docx", ".docs")) or
                              path_lower.endswith((".exe", ".dll", ".so", ".dylib", ".bin", ".dat")))

            if is_binary_file:
                flash(
                    "Cannot save binary files (images, videos, executables, etc.) as text. Please use download instead.")
                return redirect(url_for("home"))

            text = None
            for enc in ("utf-8", "utf-16", "utf-16-le", "utf-16-be", "latin-1"):
                try:
                    text = raw.decode(enc)
                    break
                except Exception:
                    continue
            if text is None:
                flash("Could not decode file bytes as text. Please upload a UTF-8/UTF-16 CSV or convert locally.")
                return redirect(url_for("home"))
        else:
            text = raw

        # 5) parse the **full** DataFrame with the original delimiter / JSON logic
        if file_type == "csv":
            # CRITICAL: Read with dtype=str to preserve all values as strings
            full_df = pd.read_csv(io.StringIO(text), sep=parse_sep, dtype=str, keep_default_na=False)
        else:
            # try standard JSON
            try:
                parsed = json.loads(text)
            except json.JSONDecodeError:
                # fallback to JSON Lines
                lines = [ln for ln in text.splitlines() if ln.strip()]
                parsed = [json.loads(ln) for ln in lines]
            if isinstance(parsed, dict):
                full_df = pd.DataFrame([parsed])
            else:
                full_df = pd.json_normalize(parsed)
            full_df.fillna("", inplace=True)

        # 5.5) Sort by first column BEFORE applying edits (edits are based on sorted indices)
        if len(full_df.columns) > 0:
            first_col = full_df.columns[0]
            full_df = full_df.sort_values(
                by=first_col, key=lambda col: col.astype(str), ignore_index=True
            )
            logger.info(f"Sorted DataFrame by column '{first_col}' before applying edits")

        # 6) Apply edits (for non-cached scenario)
        if all_edits:
            for edit_key, value in all_edits.items():
                row_idx, col_idx = map(int, edit_key.split(','))
                if row_idx < len(full_df) and col_idx < len(full_df.columns):
                    full_df.iloc[row_idx, col_idx] = value
            logger.info(f"Applied {len(all_edits)} edits to sorted DataFrame")

    # 7) serialize + upload based on output type
    if out_type == "csv":
        # Create CSV text
        csv_txt = full_df.to_csv(index=False, sep=out_sep)
        payload = csv_txt.encode("utf-8")

        # For CSV, we need to pass the DataFrame for S3Utils
        if gz_out:
            payload = gzip.compress(payload)
            fmt = "bytes"
            content_to_save = payload
        else:
            fmt = "csv"
            content_to_save = full_df
            extra = {"csv_delimiter": out_sep}

    elif out_type == "jsonl":
        # Convert DataFrame to JSONL format
        records = full_df.to_dict("records")
        json_lines = [json.dumps(record, separators=(',', ':')) for record in records]
        json_txt = '\n'.join(json_lines)
        payload = json_txt.encode("utf-8")

        if gz_out:
            payload = gzip.compress(payload)
            fmt = "bytes"
            content_to_save = payload
        else:
            fmt = "text"  # Use text format for JSONL
            content_to_save = json_txt

    else:  # json
        # Convert DataFrame to JSON format
        records = full_df.to_dict("records")
        json_txt = json.dumps(records, indent=2)
        payload = json_txt.encode("utf-8")

        if gz_out:
            payload = gzip.compress(payload)
            fmt = "bytes"
            content_to_save = payload
        else:
            fmt = "json"
            content_to_save = records  # Pass the Python object for JSON

    # Prepare extra parameters
    extra = {}
    if out_type == "csv" and not gz_out:
        extra = {"csv_delimiter": out_sep}

    # Upload to S3
    try:
        logger.info(f"Uploading to {target_path}, format: {fmt}, type: {out_type}, gzipped: {gz_out}")
        logger.info(f"Using module for upload: {module}")

        # Determine encryption preference from form
        dont_encrypt_flag = request.form.get("dont_encrypt") is not None
        cse_encrypt_flag = not dont_encrypt_flag
        logger.info(f"Encryption: {'disabled' if dont_encrypt_flag else 'enabled'}")

        S3Utils(verify=False).put_object(
            file_path=target_path,
            content=content_to_save,
            format=fmt,
            module=module,
            cse_encrypt=cse_encrypt_flag,
            **extra,
        )

        logger.info(f"Successfully uploaded to {target_path} using module: {module}")
    except Exception as e:
        logger.error(f"Failed to upload: {e}", exc_info=True)
        msg = f"Error uploading file: {str(e)}"
        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }}());
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )

    # Clear edits cache after successful save
    if cache_key in CSV_EDITS_CACHE:
        del CSV_EDITS_CACHE[cache_key]
        logger.info(f"Cleared edits cache for {cache_key}")

    # Clear the data cache too to ensure fresh data on next load
    if cache_key in CSV_DATA_CACHE:
        del CSV_DATA_CACHE[cache_key]
        logger.info(f"Cleared data cache for {cache_key}")

    # If path changed, also clear cache for the new path
    if target_path != original_path:
        new_cache_key = f"{target_path}:{module}:{upload_id or 'no-upload'}"
        if new_cache_key in CSV_DATA_CACHE:
            del CSV_DATA_CACHE[new_cache_key]
        if new_cache_key in CSV_EDITS_CACHE:
            del CSV_EDITS_CACHE[new_cache_key]

    # Clean up temp file after successful save
    if upload_id and upload_id in LOCAL_UPLOADS:
        try:
            os.unlink(LOCAL_UPLOADS[upload_id])
            LOCAL_UPLOADS.pop(upload_id)
            session.pop("upload_id", None)
        except:
            pass

    total_edits = len(all_edits)

    # Create appropriate flash message based on what happened
    flash_parts = []

    if file_type != out_type:
        flash_parts.append(f"Converted {file_type.upper()} to {out_type.upper()}")

    if total_edits > 0:
        flash_parts.append(f"saved {total_edits} edit{'s' if total_edits != 1 else ''}")
    elif parse_sep != out_sep:
        flash_parts.append(f"changed delimiter")
    elif target_path != original_path:
        flash_parts.append(f"saved to new location")
    else:
        flash_parts.append(f"saved")

    flash_msg = " and ".join(flash_parts).capitalize()
    flash_msg += f" to {target_path}"

    if gz_out:
        flash_msg += " (compressed)"

    flash(flash_msg)

    return redirect(url_for("home"))


@app.route("/save_json", methods=["POST"])
def save_json():
    """Save JSON/JSONL data"""
    upload_id = session.get("upload_id", None)
    original_path = request.form.get("orig_s3_path", "").strip()
    target_path = request.form["s3_path"].strip()
    module = request.form.get("module", "dxp")
    gz_flag = request.form.get("gzipped") == "True"
    json_data = request.form.get("json_data", "")
    is_jsonl = request.form.get("is_jsonl") == "True"
    is_json_object = request.form.get("is_json_object") == "True"
    json_type = request.form.get("json_type", "json-array")
    current_record = int(request.form.get("current_record", 0))
    total_records = int(request.form.get("total_records", 1))

    # Get original decryption module from form (if available)
    original_decryption_module = request.form.get("decryption_module", module)

    if not json_data:
        msg = "No data to save."
        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }}());
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )

    # Save path to session only if it's a valid S3 path
    if target_path.lower().startswith('s3://'):
        session['last_path'] = target_path

    # Parse the edited data
    try:
        edited_data = json.loads(json_data)
        server_log("Save JSON")
        logger.info(f"Module for save operation: {module}")
        logger.info(f"Original decryption module: {original_decryption_module}")
        server_log("Save", From=original_path, To=target_path)
        logger.info(f"JSON type from form: {json_type}")
        logger.info(f"is_json_object from form: {is_json_object}")
        logger.info(f"is_jsonl from form: {is_jsonl}")
        logger.info(f"Current record index: {current_record}")
        logger.info(f"Total records: {total_records}")
        logger.info(f"Edited data: {json.dumps(edited_data, indent=2)[:500]}...")
    except Exception as e:
        msg = f"Invalid JSON data: {str(e)}"
        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }}());
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )

    # Get cache key
    cache_key = f"{original_path}:{module}:{upload_id or 'no-upload'}"

    # Get all records from cache or reload
    if cache_key in JSON_DATA_CACHE:
        all_data, original_format = JSON_DATA_CACHE[cache_key]
        all_data = list(all_data)  # Make a copy
        logger.info(f"Using cached data for save: {len(all_data)} records, original format: {original_format}")
    else:
        # Reload the full file
        logger.info("Reloading file for save - cache miss")
        if original_decryption_module != module:
            logger.info(
                f"NOTE: Using different modules - decrypt with '{original_decryption_module}', save with '{module}'")
        try:
            if upload_id and upload_id in LOCAL_UPLOADS:
                with open(LOCAL_UPLOADS[upload_id], "rb") as f:
                    raw = f.read()
            else:
                logger.info(f"Reading S3 key {original_path} using module: {original_decryption_module}")
                raw = S3Utils(verify=False).read_key(
                    original_path, utf_decode=False, module=original_decryption_module
                )

            if isinstance(raw, (bytes, bytearray)) and raw.startswith(b"ENC"):
                logger.info(f"Decrypting file using original module: {original_decryption_module}")
                crypto_api = get_cached_crypto_api(original_decryption_module, "save_json_decrypt")
                raw = crypto_api.decrypt(raw)
            if gz_flag:
                try:
                    raw = gzip.decompress(raw)
                except:
                    pass

            text = raw.decode("utf-8") if isinstance(raw, (bytes, bytearray)) else raw

            # Debug logging
            logger.info(f"Reloaded text length: {len(text)}")
            logger.info(f"First 200 chars: {text[:200]}")

            all_data, original_format = parse_json_or_jsonl(text)
            logger.info(f"Reloaded data: {len(all_data)} records, format: {original_format}")

            # Update cache
            JSON_DATA_CACHE[cache_key] = (all_data, original_format)

        except Exception as e:
            logger.error(f"Error reloading file: {e}", exc_info=True)
            # If we can't reload, include the error in the UI but still allow saving edited data
            try:
                server_log("Save JSON Reload Error", Error=str(e))
            except Exception:
                pass
            try:
                # Persist a non-blocking warning for visibility
                warn = f"Warning: Failed to reload original file. Saving only edited data.\n\nDetails: {str(e)}"
                # Do not redirect here; proceed to save, and the home page will show the warning after redirect
                session['pending_warning'] = warn
            except Exception:
                pass
            all_data = [edited_data]
            original_format = json_type

    # Apply cached changes from all records
    if cache_key in JSON_EDITS_CACHE:
        logger.info(f"Applying cached JSON edits for {cache_key}")
        cached_edits = JSON_EDITS_CACHE[cache_key]

        for record_idx, field_edits in cached_edits.items():
            record_idx = int(record_idx)
            if record_idx < len(all_data):
                for field_path, edit_data in field_edits.items():
                    value = edit_data['value']
                    data_type = edit_data['type']

                    # Apply the edit to the record
                    try:
                        # Convert value based on type
                        if data_type == 'string':
                            # Value is already a string without quotes from frontend
                            converted_value = str(value)
                        elif data_type == 'number':
                            # Value should already be a number from frontend
                            if isinstance(value, (int, float)):
                                converted_value = value
                            else:
                                # Fallback parsing if needed
                                converted_value = float(value) if '.' in str(value) else int(value)
                        elif data_type == 'boolean':
                            converted_value = bool(value) if isinstance(value, bool) else str(value).lower() == 'true'
                        elif data_type == 'null':
                            converted_value = None
                        else:
                            converted_value = value

                        # Apply to nested field path
                        apply_field_change(all_data[record_idx], field_path, converted_value)
                        logger.info(f"Applied edit to record {record_idx}, field {field_path}: {converted_value}")
                    except Exception as e:
                        logger.error(f"Error applying edit to record {record_idx}, field {field_path}: {e}")

    # Update the current record with the edited data (this overrides any cached changes for current record)
    if current_record < len(all_data):
        logger.info(
            f"Before update - Record {current_record}: {json.dumps(all_data[current_record], indent=2)[:500]}...")
        all_data[current_record] = edited_data
        logger.info(
            f"After update - Record {current_record}: {json.dumps(all_data[current_record], indent=2)[:500]}...")
    else:
        logger.error(f"Current record index {current_record} out of bounds for {len(all_data)} records")

    # Determine output format from target path
    tp = target_path.lower()
    op = original_path.lower()

    # Check if original was JSONL based on multiple indicators
    original_was_jsonl = (
            is_jsonl == "True" or
            original_format == "jsonl" or
            op.endswith((".jsonl", ".jsonl.gz"))
    )

    # Check if original was JSON object - use json_type which comes from the form
    original_was_object = (
            json_type == "json-object" or
            original_format == "json-object" or
            is_json_object == "True"
    )

    server_log("Format Detection")
    logger.info(f"json_type from form: {json_type}")
    logger.info(f"is_json_object from form: {is_json_object}")
    logger.info(f"original_format from cache/reload: {original_format}")
    logger.info(f"original_was_object calculated: {original_was_object}")
    logger.info(f"original_was_jsonl calculated: {original_was_jsonl}")

    # If saving to same path as original, preserve format
    if target_path == original_path:
        if op.endswith(".jsonl.gz"):
            out_type, gz_out = "jsonl", True
        elif op.endswith(".jsonl"):
            out_type, gz_out = "jsonl", False
        elif op.endswith(".json.gz"):
            out_type, gz_out = "json", True
        elif op.endswith(".json"):
            out_type, gz_out = "json", False
        else:
            # Fallback to detected format
            if original_was_jsonl:
                out_type = "jsonl"
            elif original_was_object:
                out_type = "json-object"
            else:
                out_type = "json-array"
            gz_out = gz_flag
    else:
        # Target path is different, use target extension
        if tp.endswith(".jsonl.gz"):
            out_type, gz_out = "jsonl", True
        elif tp.endswith(".jsonl"):
            out_type, gz_out = "jsonl", False
        elif tp.endswith(".json.gz"):
            out_type, gz_out = "json", True
        elif tp.endswith(".json"):
            out_type, gz_out = "json", False
        else:
            # No clear extension in target, maintain original format
            if original_was_jsonl:
                out_type = "jsonl"
            elif original_was_object:
                out_type = "json-object"
            else:
                out_type = "json-array"
            gz_out = gz_flag

    # IMPORTANT: If original was object and target is .json, preserve object format
    if original_was_object and out_type == "json":
        out_type = "json-object"
        logger.info("Preserving json-object format for .json file")

    # Log format decision
    logger.info(f"Format decision: original_path={original_path}, target_path={target_path}")
    logger.info(f"Final decision: out_type={out_type}, gz_out={gz_out}")

    # Serialize based on format
    if out_type == "json-object":
        # For single object, extract from array wrapper
        if len(all_data) >= 1:
            content_to_save = all_data[0]
        else:
            logger.error(f"No data to save as json-object")
            content_to_save = {}

        json_txt = json.dumps(content_to_save, indent=2)
        logger.info(f"Saving as JSON object")
        logger.info(f"JSON object preview (first 500 chars): {json_txt[:500]}...")

    elif out_type == "jsonl":
        # JSONL format: one JSON object per line (no indentation)
        json_txt = '\n'.join(json.dumps(record, separators=(',', ':')) for record in all_data)
        content_to_save = all_data
        logger.info(f"Saving as JSONL with {len(all_data)} records")
        logger.info(f"JSONL preview (first 500 chars): {json_txt[:500]}...")

    else:  # json-array or json
        # Regular JSON format - save as array
        json_txt = json.dumps(all_data, indent=2)
        content_to_save = all_data
        logger.info(f"Saving as JSON array with {len(all_data)} records")
        logger.info(f"JSON preview (first 500 chars): {json_txt[:500]}...")

    payload = json_txt.encode("utf-8")

    if gz_out:
        payload = gzip.compress(payload)
        fmt = "bytes"
    else:
        fmt = "json"

    # Upload
    try:
        logger.info(f"Uploading to {target_path}, format: {fmt}, gzipped: {gz_out}")
        logger.info(f"Using module for upload: {module}")

        # Determine what content to pass based on format
        if fmt == "bytes":
            # For gzipped content, use the compressed payload directly
            upload_content = payload
        elif out_type == "jsonl":
            # For JSONL, use the raw text - don't parse it
            upload_content = json_txt
            fmt = "text"  # Use text format for JSONL
        else:
            # For regular JSON, parse it back to object/array
            upload_content = json.loads(json_txt)

        # Determine encryption preference from form
        dont_encrypt_flag = request.form.get("dont_encrypt") is not None
        cse_encrypt_flag = not dont_encrypt_flag
        logger.info(f"Encryption: {'disabled' if dont_encrypt_flag else 'enabled'}")

        S3Utils(verify=False).put_object(
            file_path=target_path,
            content=upload_content,
            format=fmt,
            module=module,
            cse_encrypt=cse_encrypt_flag,
        )
        logger.info(f"Successfully uploaded to {target_path} using module: {module}")
    except Exception as e:
        logger.error(f"Failed to upload: {e}", exc_info=True)
        msg = f"Error uploading file: {str(e)}"
        return (
            f"""
                <script>
                  (function(){{
                    try {{ localStorage.setItem('workbench-pending-modal-error', {msg!r}); }} catch(err) {{}}
                    window.location = '{url_for('home')}';
                  }}());
                </script> """,
            200,
            {"Content-Type": "text/html"},
        )

    # Update cache with the new data and format
    final_format = out_type if out_type in ["json-object", "jsonl"] else original_format
    if cache_key in JSON_DATA_CACHE:
        JSON_DATA_CACHE[cache_key] = (all_data, final_format)
        logger.info(f"Updated cache for key: {cache_key} with format: {final_format}")

    # Clear JSON edits cache after successful save
    if cache_key in JSON_EDITS_CACHE:
        del JSON_EDITS_CACHE[cache_key]
        logger.info(f"Cleared JSON edits cache for {cache_key}")

    # Also update with new cache key if path changed
    if target_path != original_path:
        new_cache_key = f"{target_path}:{module}:{upload_id or 'no-upload'}"
        JSON_DATA_CACHE[new_cache_key] = (all_data, final_format)
        logger.info(f"Created new cache entry for key: {new_cache_key} with format: {final_format}")

        # Clear edits cache for new path too
        if new_cache_key in JSON_EDITS_CACHE:
            del JSON_EDITS_CACHE[new_cache_key]

    # Clean up local upload if saving to S3
    if upload_id and upload_id in LOCAL_UPLOADS and target_path.lower().startswith('s3://'):
        try:
            os.unlink(LOCAL_UPLOADS[upload_id])
            LOCAL_UPLOADS.pop(upload_id)
            session.pop("upload_id", None)
            logger.info("Cleaned up local upload after successful S3 save")
        except Exception as e:
            logger.warning(f"Failed to clean up local upload: {e}")

    server_log("Save JSON Completed")
    flash(f"Saved to {target_path}")
    return redirect(url_for("home"))


@app.route("/run_code", methods=["POST"])
def run_code():
    """Run Python or Java code locally and return the output."""
    try:
        code_text = request.form.get("code_text", "")
        file_extension = request.form.get("file_extension", "").lower()

        if not code_text.strip():
            return jsonify({"error": "No code provided"}), 400

        # Only allow Python and Java files
        if file_extension not in [".py", ".java"]:
            return jsonify({"error": "Only Python (.py) and Java (.java) files can be executed"}), 400

        # Create a temporary file
        import tempfile
        import subprocess
        import threading
        import time

        # Create temp file with appropriate extension
        with tempfile.NamedTemporaryFile(mode='w', suffix=file_extension, delete=False) as temp_file:
            temp_file.write(code_text)
            temp_file_path = temp_file.name

        try:
            output_queue = queue.Queue()
            error_queue = queue.Queue()

            def run_process():
                try:
                    if file_extension == ".py":
                        # Run Python code with unbuffered output
                        process = subprocess.Popen(
                            ["python3", "-u", temp_file_path],
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                            bufsize=0,
                            universal_newlines=True
                        )
                    else:  # .java
                        # Compile Java first
                        java_file = temp_file_path
                        class_file = temp_file_path[:-5] + ".class"

                        # Compile
                        compile_process = subprocess.run(
                            ["javac", java_file],
                            capture_output=True,
                            text=True
                        )

                        if compile_process.returncode != 0:
                            error_queue.put(f"Compilation Error:\n{compile_process.stderr}")
                            return

                        # Run the compiled class
                        class_name = os.path.basename(temp_file_path)[:-5]
                        class_dir = os.path.dirname(temp_file_path)

                        process = subprocess.Popen(
                            ["java", "-cp", class_dir, class_name],
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                            bufsize=1,
                            universal_newlines=True
                        )

                    # Use communicate to get all output at once
                    stdout, stderr = process.communicate()

                    # Process stdout
                    if stdout:
                        for line in stdout.splitlines():
                            if line:
                                output_queue.put(("stdout", line + "\n"))

                    # Process stderr
                    if stderr:
                        for line in stderr.splitlines():
                            if line:
                                output_queue.put(("stderr", line + "\n"))

                    # Signal completion
                    output_queue.put(("complete", f"Process finished with exit code: {process.returncode}"))

                except Exception as e:
                    error_queue.put(f"Execution Error: {str(e)}")

            execution_thread = threading.Thread(target=run_process)
            execution_thread.daemon = True
            execution_thread.start()

            session_id = str(uuid.uuid4())
            RUNNING_PROCESSES[session_id] = {
                'output_queue': output_queue,
                'error_queue': error_queue,
                'thread': execution_thread,
                'temp_file': temp_file_path,
                'start_time': time.time()
            }

            return jsonify({
                "session_id": session_id,
                "message": "Code execution started"
            })

        except Exception as e:
            try:
                os.unlink(temp_file_path)
            except:
                pass
            return jsonify({"error": f"Failed to start execution: {str(e)}"}), 500

    except Exception as e:
        logger.error(f"Run code error: {e}", exc_info=True)
        return jsonify({"error": f"Server error: {str(e)}"}), 500


@app.route("/execute_command", methods=["POST"])
def execute_command():
    """Execute a shell command and return the output."""
    try:
        data = request.json or {}
        command = data.get('command', '').strip()

        if not command:
            return jsonify({"error": "No command provided"}), 400

        # Security: Only allow safe commands
        dangerous_commands = ['rm -rf', 'sudo', 'chmod 777', 'dd if=', '> /dev/', 'mkfs', 'fdisk']
        if any(dangerous in command.lower() for dangerous in dangerous_commands):
            return jsonify({"error": "Command not allowed for security reasons"}), 403

        # Execute command
        import subprocess
        import tempfile

        try:
            # Use shell=True for command execution, but with timeout
            process = subprocess.run(
                command,
                shell=True,
                capture_output=True,
                text=True,
                timeout=30,  # 30 second timeout
                cwd=os.path.expanduser('~')  # Start in user's home directory
            )

            output = process.stdout
            error = process.stderr
            return_code = process.returncode

            return jsonify({
                "output": output,
                "error": error,
                "return_code": return_code,
                "command": command
            })

        except subprocess.TimeoutExpired:
            return jsonify({"error": "Command timed out after 30 seconds"}), 408
        except Exception as e:
            return jsonify({"error": f"Command execution failed: {str(e)}"}), 500

    except Exception as e:
        logger.error(f"Execute command error: {e}", exc_info=True)
        return jsonify({"error": f"Server error: {str(e)}"}), 500


@app.route("/stream_output/<session_id>")
def stream_output(session_id):
    """Stream output from a running code execution."""
    if session_id not in RUNNING_PROCESSES:
        return jsonify({"error": "Session not found"}), 404

    process_info = RUNNING_PROCESSES[session_id]
    output_queue = process_info['output_queue']
    error_queue = process_info['error_queue']

    # Check for errors first
    try:
        error = error_queue.get_nowait()
        return jsonify({"error": error, "complete": True})
    except queue.Empty:
        pass

    # Get available output
    output_lines = []
    try:
        while True:
            output_type, line = output_queue.get_nowait()
            if output_type == "complete":
                # Clean up
                try:
                    os.unlink(process_info['temp_file'])
                    if session_id in RUNNING_PROCESSES:
                        del RUNNING_PROCESSES[session_id]
                except:
                    pass
                return jsonify({"output": output_lines, "complete": True, "message": line})
            else:
                output_lines.append({"type": output_type, "content": line})
    except queue.Empty:
        pass

    return jsonify({"output": output_lines, "complete": False})


@app.route("/save_code", methods=["POST"])
def save_code():
    """Save plain text code files to S3 without encryption."""
    try:
        target_path = request.form.get("s3_path", "").strip()
        code_text = request.form.get("code_text", "")

        if not target_path or not target_path.lower().startswith('s3://'):
            flash("Please provide a valid S3 path.")
            return redirect(url_for("home"))

        # Validate allowed extensions; allow no extension (default to code)
        lower = target_path.lower()
        base = os.path.basename(lower)
        has_ext = "." in base
        allowed_ext = lower.endswith((
            ".py", ".html", ".htm", ".js", ".go", ".md", ".txt",
            ".xml", ".css", ".sql", ".sh", ".bash",
            ".yaml", ".yml", ".toml", ".ini", ".conf", ".cfg",
            ".properties", ".dockerfile"
        ))
        if has_ext and not allowed_ext:
            flash(
                "Unsupported file extension. Allowed: .py, .html, .htm, .js, .go, .md, .txt, .xml, .css, .sql, .sh, .bash, .yaml, .yml, .toml, .ini, .conf, .cfg or no extension")
            return redirect(url_for("home"))

        # Save path in session for convenience
        session['last_path'] = target_path

        server_log("Save Code", Destination=target_path)
        logger.info(f"Code size: {len(code_text)} chars")

        # Upload as plain text without any encryption (no module needed)
        S3Utils(verify=False).put_object(
            file_path=target_path,
            content=code_text,
            format="text",
            cse_encrypt=False,
        )

        logger.info(f"Saved code to {target_path} without encryption")
        flash(f"Saved to {target_path}")
        return redirect(url_for("home"))
    except Exception as e:
        logger.error(f"Failed to save code: {e}", exc_info=True)
        flash(f"Error saving code: {str(e)}")
        return redirect(url_for("home"))


@app.route("/save_raw", methods=["POST"])
def save_raw():
    """Save raw text files from RAW_EDIT_HTML with proper cache management."""
    print("=== SAVE_RAW FUNCTION STARTED ===")
    logger.info("=== SAVE_RAW ROUTE ENTERED ===")
    logger.info("=== SAVE_RAW ROUTE ENTERED - IMMEDIATE LOG ===")
    print("=== SAVE_RAW ROUTE ENTERED - PRINT STATEMENT ===")
    try:
        target_path = request.form.get("s3_path", "").strip()
        code_text = request.form.get("code_text", "")
        module = request.form.get("module", "dxp")
        upload_id = session.get("upload_id")
        cache_key = request.form.get("cache_key", "")
        is_ajax = (request.headers.get('X-Requested-With') == 'XMLHttpRequest') or (request.form.get('ajax') == '1')

        # Debug logging
        logger.info(f"Save Raw Debug - Target Path: {target_path}")
        logger.info(f"Save Raw Debug - Target Path Type: {type(target_path)}")
        logger.info(f"Save Raw Debug - Target Path Length: {len(target_path) if target_path else 0}")
        logger.info(f"Save Raw Debug - Module: {module}")
        logger.info(f"Save Raw Debug - Code Length: {len(code_text)}")
        logger.info(f"Save Raw Debug - Upload ID: {upload_id}")
        logger.info(f"Save Raw Debug - Cache Key: {cache_key}")
        logger.info(f"Save Raw Debug - Form Keys: {list(request.form.keys())}")
        logger.info(f"Save Raw Debug - All Form Values: {dict(request.form)}")

        if not target_path or not target_path.lower().startswith('s3://'):
            logger.error(f"Save Raw Error - Invalid S3 path: {target_path}")
            logger.error(f"Save Raw Error - Target path is empty: {not target_path}")
            logger.error(
                f"Save Raw Error - Target path starts with s3://: {target_path.lower().startswith('s3://') if target_path else False}")
            if is_ajax:
                return jsonify(ok=False, message="Please provide a valid S3 path."), 400
            flash("Please provide a valid S3 path.")
            return redirect(url_for("home"))

        # Validate allowed extensions
        # Validate allowed extensions: restrict to CSV/JSON family only
        lower = target_path.lower()
        allowed_extensions = (".csv", ".csv.gz", ".json", ".jsonl")
        allowed_ext = any(lower.endswith(ext) for ext in allowed_extensions)

        # Debug logging for extension validation
        logger.info(f"Save Raw Debug - Lower path: {lower}")
        logger.info(f"Save Raw Debug - Has extension: {'Yes' if '.' in os.path.basename(lower) else 'No'}")
        logger.info(f"Save Raw Debug - Allowed extension: {'Yes' if allowed_ext else 'No'}")
        logger.info(f"Save Raw Debug - Checking each extension:")
        for ext in allowed_extensions:
            logger.info(f"Save Raw Debug - Ends with {ext}: {lower.endswith(ext)}")

        # If file has an extension, it must be in the allowed list
        if "." in os.path.basename(lower) and not allowed_ext:
            logger.error(f"Save Raw Error - Unsupported extension: {target_path}")
            flash(
                "Unsupported file extension. Allowed: .csv, .csv.gz, .json, .jsonl or no extension")
            if is_ajax:
                return jsonify(ok=False, message=(
                    "Unsupported file extension. Allowed: .csv, .csv.gz, .json, .jsonl"
                )), 400
            flash("Unsupported file extension. Allowed: .csv, .csv.gz, .json, .jsonl")
            return redirect(url_for("home"))

        # Save path in session for convenience
        session['last_path'] = target_path

        server_log("Save Raw", Destination=target_path)
        logger.info(f"Raw content size: {len(code_text)} chars")

        # Determine encryption preference from form
        dont_encrypt_flag = request.form.get("dont_encrypt") is not None
        cse_encrypt_flag = not dont_encrypt_flag
        logger.info(f"Encryption: {'disabled' if dont_encrypt_flag else 'enabled'}")

        # Prepare content and upload with gzip/encryption handling
        if lower.endswith('.csv.gz'):
            try:
                # Convert CSV text to UTF-8 bytes
                raw_bytes = code_text.encode('utf-8')
                # Compress with gzip
                gz_bytes = gzip.compress(raw_bytes)
                logger.info(f"Gzipping for .csv.gz target: {len(raw_bytes)} -> {len(gz_bytes)} bytes")

                # Upload compressed bytes; S3Utils will encrypt bytes when cse_encrypt is True
                S3Utils(verify=False).put_object(
                    file_path=target_path,
                    content=gz_bytes,
                    format="bytes",  # Use bytes format for binary data
                    module=module,
                    cse_encrypt=cse_encrypt_flag,
                )
            except Exception as gz_err:
                logger.warning(f"Gzip failed for .csv.gz target, uploading uncompressed bytes: {gz_err}")
                # Fallback: upload uncompressed bytes
                raw_bytes = code_text.encode('utf-8')
                S3Utils(verify=False).put_object(
                    file_path=target_path,
                    content=raw_bytes,
                    format="bytes",  # Use bytes format for binary data
                    module=module,
                    cse_encrypt=cse_encrypt_flag,
                )
        else:
            # Upload as UTF-8 text for .csv/.json/.jsonl
            S3Utils(verify=False).put_object(
                file_path=target_path,
                content=code_text,
                format="text",
                module=module,
                cse_encrypt=cse_encrypt_flag,
            )

        # Clear relevant caches after successful save
        if cache_key:
            # Clear JSON cache if this was a JSON file
            if cache_key in JSON_DATA_CACHE:
                del JSON_DATA_CACHE[cache_key]
                logger.info(f"Cleared JSON data cache for {cache_key}")

            if cache_key in JSON_EDITS_CACHE:
                del JSON_EDITS_CACHE[cache_key]
                logger.info(f"Cleared JSON edits cache for {cache_key}")

            # Clear CSV cache if this was a CSV file
            if cache_key in CSV_DATA_CACHE:
                del CSV_DATA_CACHE[cache_key]
                logger.info(f"Cleared CSV data cache for {cache_key}")

            if cache_key in CSV_EDITS_CACHE:
                del CSV_EDITS_CACHE[cache_key]
                logger.info(f"Cleared CSV edits cache for {cache_key}")

        # Clean up local upload if saving to S3
        if upload_id and upload_id in LOCAL_UPLOADS and target_path.lower().startswith('s3://'):
            try:
                os.unlink(LOCAL_UPLOADS[upload_id])
                LOCAL_UPLOADS.pop(upload_id)
                session.pop("upload_id", None)
                logger.info("Cleaned up local upload after successful S3 save")
            except Exception as e:
                logger.warning(f"Failed to clean up local upload: {e}")

        encryption_status = "without encryption" if dont_encrypt_flag else f"with encryption (module: {module})"
        logger.info(f"Saved raw content to {target_path} {encryption_status}")
        if is_ajax:
            logger.info("=== SAVE_RAW SUCCESS - JSON RESPONSE ===")
            return jsonify(ok=True, redirect=url_for("home"))
        flash(f"Saved to {target_path}")
        logger.info("=== SAVE_RAW SUCCESS - REDIRECTING ===")
        return redirect(url_for("home"))

    except Exception as e:
        logger.error(f"Failed to save raw content: {e}", exc_info=True)
        logger.error(f"Exception type: {type(e)}")
        logger.error(f"Exception args: {e.args}")
        if (request.headers.get('X-Requested-With') == 'XMLHttpRequest') or (request.form.get('ajax') == '1'):
            return jsonify(ok=False, message=f"Error saving file: {str(e)}"), 500
        flash(f"Error saving file: {str(e)}")
        return redirect(url_for("home"))


@app.route("/plain-upload", methods=["POST"])
def plain_upload():
    try:
        server_log("Upload (No Encryption)")
        s3_path = request.form.get("s3_path", "").strip()
        module = request.form.get("module", "dxp")
        upload_id = session.get("upload_id")

        if not s3_path or not s3_path.lower().startswith('s3://'):
            server_log("Upload (Invalid S3 Path)", S3_Path=s3_path)
            return (
                f"""
                    <script>
                      (function(){{
                        try {{ localStorage.setItem('workbench-pending-modal-error', {"Please provide a valid S3 path starting with s3://"!r}); }} catch(e) {{}}
                        window.location = '{url_for('home')}';
                      }})();
                    </script> """,
                200,
                {"Content-Type": "text/html"},
            )

        upload = request.files.get("upload_file")
        if upload and upload.filename:
            raw_bytes = upload.read()
            tmp = tempfile.NamedTemporaryFile(delete=False)
            tmp.write(raw_bytes)
            tmp.close()
            upload_id = str(uuid.uuid4())
            LOCAL_UPLOADS[upload_id] = tmp.name
            session["upload_id"] = upload_id
            session["upload_filename"] = upload.filename

        if not upload_id or upload_id not in LOCAL_UPLOADS:
            server_log("Upload (No Local File)", Upload_Id=upload_id)
            flash("No local file selected for upload")
            return redirect(url_for("home"))

        local_file_path = LOCAL_UPLOADS[upload_id]
        with open(local_file_path, "rb") as f:
            file_content = f.read()

        # Use original selected filename for extension checks
        selected_name = session.get("upload_filename") or (
            upload.filename if upload and upload.filename else os.path.basename(local_file_path))
        selected_lower = selected_name.lower()
        ext = os.path.splitext(selected_lower)[1]
        # Enforce S3 target extension compatibility with selected file (allow only matching or non-gz -> gz upgrade)
        target_lower = s3_path.lower()

        def ext_core(name):
            if name.endswith('.csv.gz'): return ('csv', True)
            if name.endswith('.jsonl.gz'): return ('jsonl', True)
            if name.endswith('.json.gz'): return ('json', True)
            if name.endswith('.csv'): return ('csv', False)
            if name.endswith('.jsonl'): return ('jsonl', False)
            if name.endswith('.json'): return ('json', False)
            if name.endswith('.xlsx'): return ('xlsx', False)
            if name.endswith('.xls'): return ('xls', False)
            return (os.path.splitext(name)[1].lstrip('.'), False)

        sel_core, sel_gz = ext_core(selected_lower)
        tgt_core, tgt_gz = ext_core(target_lower)
        allowed = (sel_core == tgt_core and sel_gz == tgt_gz) or (sel_core == tgt_core and not sel_gz and tgt_gz)
        if not allowed:
            server_log("Upload (Type Mismatch)", Selected=selected_name, Target=s3_path,
                       Selected_Type=f"{sel_core}{'.gz' if sel_gz else ''}",
                       Target_Type=f"{tgt_core}{'.gz' if tgt_gz else ''}")
            flash(f"Selected file type does not match S3 target. Selected {selected_name} → Target {s3_path}")
            return redirect(url_for("home"))
        # For plain upload, send text for known text formats; otherwise send bytes
        is_text = ext in ['.py', '.txt', '.md', '.json', '.jsonl', '.json.gz', '.jsonl.gz', '.csv', '.csv.gz', '.html',
                          '.htm', '.js', '.css', '.sql', '.yaml', '.yml', '.toml', '.ini', '.cfg', '.conf', '.sh',
                          '.bash', '.xml', '.log', '.properties', '.dockerfile', '.gitignore', '.gitattributes',
                          '.editorconfig', '.eslintrc', '.prettierrc', '.babelrc', '.env', '.env.example', '.env.local',
                          '.env.production', '.env.development']
        if is_text:
            try:
                content = file_content.decode('utf-8')
                fmt = 'text'
            except UnicodeDecodeError:
                content = file_content
                fmt = 'str'
        elif ext in ['.xlsx', '.xls']:
            content = file_content
            fmt = 'xlsx'
        else:
            content = file_content
            fmt = 'str'

        # Perform direct S3 put for plain upload to avoid text/bytes coercion
        # Parse bucket and key from s3_path
        s3_clean = s3_path[5:]
        bucket, key = s3_clean.split('/', 1) if '/' in s3_clean else (s3_clean, os.path.basename(local_file_path))
        server_log("Upload", From=local_file_path, To=s3_path)
        s3_client = get_fresh_s3_client()
        # If target key ends with .gz and body is text/bytes, gzip before upload
        try:
            if key.lower().endswith('.gz'):
                raw_bytes = content if isinstance(content, (bytes, bytearray)) else content.encode('utf-8')
                body = gzip.compress(raw_bytes)
                logger.info(
                    f"Plain upload: gzipped content from {len(raw_bytes)} -> {len(body)} bytes due to .gz target")
            else:
                body = content if isinstance(content, (bytes, bytearray)) else content.encode('utf-8')
        except Exception as gz_err:
            logger.warning(f"Plain upload gzip failed, sending original: {gz_err}")
            body = content if isinstance(content, (bytes, bytearray)) else content.encode('utf-8')
        s3_client.put_object(Bucket=bucket, Key=key, Body=body)

        session['last_path'] = s3_path
        session['from_encrypt_upload'] = True
        session.modified = True
        flash(f"File uploaded (no encryption) to {s3_path}")
        server_log("Upload Completed (No Encryption)")
        return redirect(url_for("home"))
    except Exception as e:
        logger.error(f"Plain upload error: {e}", exc_info=True)
        flash(f"Error uploading file: {str(e)}")
        return redirect(url_for("home"))


def format_file_size(size_bytes):
    """Format file size in human readable format"""
    if size_bytes == 0:
        return "0 B"

    size_names = ["B", "KB", "MB", "GB", "TB"]
    i = 0
    while size_bytes >= 1024 and i < len(size_names) - 1:
        size_bytes /= 1024.0
        i += 1

    return f"{size_bytes:.1f} {size_names[i]}"


@app.route('/get-file-metadata', methods=['POST'])
def get_file_metadata():
    """Get file metadata including size, dates, and encryption status"""
    try:
        data = request.json or {}
        s3_path = data.get('s3_path', '').strip()
        module = data.get('module', 'dxp')
        decryption_module = data.get('decryption_module', module)

        if not s3_path:
            return jsonify({'error': 'No S3 path provided'}), 400

        logger.info(f"Getting metadata for: {s3_path}")

        # Handle local files (uploaded files)
        upload_id = session.get('upload_id')
        if upload_id and upload_id in LOCAL_UPLOADS:
            try:
                local_file_path = LOCAL_UPLOADS[upload_id]
                if os.path.exists(local_file_path):
                    # Get file stats
                    stat_info = os.stat(local_file_path)
                    size_bytes = stat_info.st_size
                    size_formatted = format_file_size(size_bytes)

                    # Get creation and modification times
                    created_time = datetime.fromtimestamp(stat_info.st_ctime)
                    modified_time = datetime.fromtimestamp(stat_info.st_mtime)

                    metadata = {
                        'size': size_formatted,
                        'created_date': created_time.isoformat() + 'Z',  # ISO format with Z for UTC
                        'last_modified': modified_time.isoformat() + 'Z'  # ISO format with Z for UTC
                    }

                    logger.info(f"Local file metadata retrieved: {local_file_path} - Size: {size_formatted}")
                    return jsonify({'metadata': metadata})
            except Exception as e:
                logger.error(f"Error getting local file metadata: {e}")

        # Handle S3 files
        if not s3_path.startswith('s3://'):
            return jsonify({'error': 'Invalid S3 path format'}), 400

        # Parse S3 path
        s3_clean = s3_path[5:]  # Remove 's3://'
        bucket, key = s3_clean.split('/', 1) if '/' in s3_clean else (s3_clean, '')

        if not bucket or not key:
            return jsonify({'error': 'Invalid S3 path'}), 400

        # Get S3 object metadata
        s3_client = get_fresh_s3_client()

        try:
            response = s3_client.head_object(Bucket=bucket, Key=key)

            # Extract metadata
            size_bytes = response.get('ContentLength', 0)
            size_formatted = format_file_size(size_bytes)

            last_modified = response.get('LastModified')
            last_modified_str = last_modified.isoformat() + 'Z' if last_modified else 'Not Available'

            metadata = {
                'size': size_formatted,
                'created_date': 'Not Available',  # S3 doesn't provide creation date
                'last_modified': last_modified_str
            }

            logger.info(f"Metadata retrieved successfully for {s3_path}")
            return jsonify({'metadata': metadata})

        except ClientError as e:
            error_code = e.response.get('Error', {}).get('Code', 'Unknown')
            if error_code == 'NoSuchKey':
                return jsonify({'error': 'File not found'}), 404
            elif error_code == 'AccessDenied':
                return jsonify({'error': 'Access denied to file'}), 403
            else:
                return jsonify({'error': f'S3 error: {error_code}'}), 500

    except Exception as e:
        logger.error(f"Error getting file metadata: {e}", exc_info=True)
        return jsonify({'error': f'Server error: {str(e)}'}), 500


@app.route('/update')
def update():
    """Update the application from git and restart"""
    try:
        # Navigate to the new repository directory
        workbench_dir = os.path.expanduser("~/ec_ainative_tools_internal/sequoia-cloud/workbench")
        original_dir = os.getcwd()
        os.chdir(workbench_dir)

        # Check if git repository exists (check in parent directory since .git is at repo root)
        git_dir = os.path.expanduser("~/ec_ainative_tools_internal/.git")
        if not os.path.exists(git_dir):
            return "Error: Not a git repository", 500

        # Change to repository root for git operations
        repo_root = os.path.expanduser("~/ec_ainative_tools_internal")
        os.chdir(repo_root)

        # Check git status first
        try:
            status_result = subprocess.run(['git', 'status', '--porcelain'],
                                           check=True,
                                           capture_output=True,
                                           text=True)

            if status_result.stdout.strip():
                # There are local changes, stash them first
                logger.info("Local changes detected, stashing them...")
                stash_result = subprocess.run(['git', 'stash'],
                                              check=True,
                                              capture_output=True,
                                              text=True)
                logger.info(f"Stashed changes: {stash_result.stdout}")

        except subprocess.CalledProcessError as status_error:
            logger.error(f"Git status error: {status_error.stderr}")
            return f"Git status check failed: {status_error.stderr}", 500

        # Update from git using subprocess
        try:
            # Fetch latest changes
            fetch_result = subprocess.run(['git', 'fetch', 'origin'],
                                          check=True,
                                          capture_output=True,
                                          text=True)
            logger.info(f"Git fetch successful: {fetch_result.stdout}")

            # Reset to origin/main (this will overwrite local changes)
            reset_result = subprocess.run(['git', 'reset', '--hard', 'origin/main'],
                                          check=True,
                                          capture_output=True,
                                          text=True)
            logger.info(f"Git reset successful: {reset_result.stdout}")

        except subprocess.CalledProcessError as git_error:
            logger.error(f"Git update error: {git_error.stderr}")
            return f"Git update failed: {git_error.stderr}", 500
        finally:
            # Restore original directory
            os.chdir(original_dir)

        # Since we're using use_reloader=True, Flask will auto-reload
        # Just return success message
        return "Update completed successfully! The app will reload automatically.", 200

    except Exception as e:
        logger.error(f"Error in update endpoint: {e}", exc_info=True)
        return f"Error during update: {e}", 500


def check_ollama_installed():
    """Check if Ollama is installed on the system"""
    try:
        # Try to run ollama command
        result = subprocess.run(['ollama', '--version'],
                                capture_output=True, text=True, timeout=10)
        return result.returncode == 0
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError, FileNotFoundError):
        return False


def install_ollama():
    """Install Ollama based on the operating system"""
    system = platform.system().lower()

    try:
        if system == 'darwin':  # macOS
            return install_ollama_mac()
        elif system == 'windows':
            return install_ollama_windows()
        else:
            return False, f"Automatic Ollama installation not supported on {system}"
    except Exception as e:
        return False, f"Error during Ollama installation: {str(e)}"


def install_ollama_mac():
    """Install Ollama on macOS using brew"""
    try:
        # First check if brew is installed
        brew_check = subprocess.run(['which', 'brew'],
                                    capture_output=True, text=True, timeout=10)

        if brew_check.returncode != 0:
            return False, "Homebrew is not installed. Please install Homebrew first: https://brew.sh"

        # Install ollama using brew
        DXP_LOGGER.info("Installing Ollama via Homebrew...")
        install_result = subprocess.run(['brew', 'install', 'ollama'],
                                        capture_output=True, text=True, timeout=300)

        if install_result.returncode == 0:
            # Start ollama service
            DXP_LOGGER.info("Starting Ollama service...")
            start_result = subprocess.run(['brew', 'services', 'start', 'ollama'],
                                          capture_output=True, text=True, timeout=30)

            if start_result.returncode == 0:
                # Wait a moment for the service to start
                time.sleep(3)
                return True, "Ollama installed and started successfully via Homebrew"
            else:
                return True, "Ollama installed via Homebrew, but failed to start service. You may need to start it manually with 'ollama serve'"
        else:
            return False, f"Failed to install Ollama via Homebrew: {install_result.stderr}"

    except subprocess.TimeoutExpired:
        return False, "Installation timed out. Please try installing Ollama manually."
    except Exception as e:
        return False, f"Error installing Ollama on macOS: {str(e)}"


def install_ollama_windows():
    """Install Ollama on Windows"""
    try:
        # Check if winget is available (Windows Package Manager)
        winget_check = subprocess.run(['winget', '--version'],
                                      capture_output=True, text=True, timeout=10)

        if winget_check.returncode == 0:
            # Try to install via winget
            DXP_LOGGER.info("Installing Ollama via winget...")
            install_result = subprocess.run(['winget', 'install', 'Ollama.Ollama'],
                                            capture_output=True, text=True, timeout=300)

            if install_result.returncode == 0:
                return True, "Ollama installed successfully via winget. Please restart your terminal and run 'ollama serve' to start the service."
            else:
                return False, f"Failed to install Ollama via winget: {install_result.stderr}"
        else:
            # Provide manual installation instructions
            return False, ("Automatic installation not available. Please install Ollama manually:\n"
                           "1. Download from: https://ollama.com/download/windows\n"
                           "2. Run the installer\n"
                           "3. Restart your terminal\n"
                           "4. Run 'ollama serve' to start the service")

    except subprocess.TimeoutExpired:
        return False, "Installation timed out. Please try installing Ollama manually."
    except Exception as e:
        return False, f"Error installing Ollama on Windows: {str(e)}"


@app.route('/chatbot-query', methods=['POST'])
def chatbot_query():
    """Handle chatbot queries using Ollama HTTP API with streaming"""
    try:
        import requests
        import json
        from flask import Response, stream_with_context

        # Parse request data
        data = request.get_json()
        question = data.get('question', '').strip()
        model = data.get('model', 'llama3.2:1b')

        if not question:
            return jsonify({'success': False, 'error': 'No question provided'})

        # Check if Ollama is running
        try:
            response = requests.get('http://localhost:11434/api/tags', timeout=5)
            if response.status_code != 200:
                # Check if Ollama is installed but not running
                if check_ollama_installed():
                    return jsonify({'success': False,
                                    'error': 'Ollama is installed but not running. Please start it with "ollama serve" command.'})
                else:
                    # Ollama is not installed, try to install it
                    DXP_LOGGER.info("Ollama not found, attempting automatic installation...")
                    success, message = install_ollama()
                    if success:
                        return jsonify({'success': True,
                                        'message': f'Ollama installation completed: {message}\n\nPlease try your question again in a few moments.'})
                    else:
                        return jsonify({'success': False, 'error': f'Ollama installation failed: {message}'})
        except requests.exceptions.RequestException:
            # Check if Ollama is installed but not running
            if check_ollama_installed():
                return jsonify({'success': False,
                                'error': 'Ollama is installed but not running. Please start it with "ollama serve" command.'})
            else:
                # Ollama is not installed, try to install it
                DXP_LOGGER.info("Ollama not found, attempting automatic installation...")
                success, message = install_ollama()
                if success:
                    return jsonify({'success': True,
                                    'message': f'Ollama installation completed: {message}\n\nPlease try your question again in a few moments.'})
                else:
                    return jsonify({'success': False, 'error': f'Ollama installation failed: {message}'})

        # Check if model exists; if not, we'll stream the download progress in the SSE generator
        models_data = response.json()
        model_names = [m['name'] for m in models_data.get('models', [])]
        needs_download = model not in model_names

        # Create prompt based on model type
        if any(x in model.lower() for x in ['code', 'qwen', 'deepseek', 'codellama']):
            prompt = f"You are a helpful coding assistant. Answer with code examples when appropriate:\n\n{question}"
        else:
            prompt = f"You are a helpful AI assistant. Please answer clearly and concisely:\n\n{question}"

        # Generate streaming response
        DXP_LOGGER.info(f"Running streaming query with model {model}: {question[:50]}...")

        def generate():
            """Generator function for streaming response"""
            api_data = {
                'model': model,
                'prompt': prompt,
                'stream': True  # Enable streaming
            }

            # If model missing, stream download progress first
            if needs_download:
                try:
                    pull_resp = requests.post(
                        'http://localhost:11434/api/pull',
                        json={'name': model},
                        stream=True,
                        timeout=600
                    )
                    if pull_resp.status_code != 200:
                        yield f"data: {json.dumps({'error': f'Failed to download model {model}'})}\n\n"
                        return
                    # Emit initial 0% so UI shows progress immediately
                    try:
                        yield f"data: {json.dumps({'download_progress': 0})}\n\n"
                    except Exception:
                        pass
                    last_pct = 0
                    for line in pull_resp.iter_lines():
                        if not line:
                            continue
                        try:
                            obj = json.loads(line)
                        except Exception:
                            continue
                        if obj.get('status') == 'success':
                            DXP_LOGGER.info(f"Model {model} downloaded successfully")
                            yield f"data: {json.dumps({'download_progress': 100})}\n\n"
                            break
                        total = obj.get('total') or obj.get('total_bytes') or 0
                        completed = obj.get('completed') or obj.get('completed_bytes') or 0
                        if isinstance(total, (int, float)) and total > 0 and isinstance(completed, (int, float)):
                            pct = int((completed / total) * 100)
                            if pct != last_pct:
                                yield f"data: {json.dumps({'download_progress': pct})}\n\n"
                                last_pct = pct
                except requests.exceptions.Timeout:
                    yield f"data: {json.dumps({'error': 'Model download timed out'})}\n\n"
                    return
                except Exception as e:
                    yield f"data: {json.dumps({'error': f'Model download failed: {str(e)}'})}\n\n"
                    return

            try:
                # Make streaming request
                with requests.post(
                        'http://localhost:11434/api/generate',
                        json=api_data,
                        stream=True,
                        timeout=120
                ) as response:

                    if response.status_code != 200:
                        yield f"data: {json.dumps({'error': f'Ollama API error: {response.status_code}'})}\n\n"
                        return

                    # Stream each chunk as Server-Sent Event
                    for line in response.iter_lines():
                        if line:
                            try:
                                chunk = json.loads(line)
                                # Send the response token
                                if 'response' in chunk:
                                    yield f"data: {json.dumps({'token': chunk['response'], 'done': chunk.get('done', False)})}\n\n"

                                # Check if generation is complete
                                if chunk.get('done', False):
                                    # Send final metadata
                                    yield f"data: {json.dumps({'done': True, 'context_length': chunk.get('context', 0), 'eval_count': chunk.get('eval_count', 0)})}\n\n"
                                    break
                            except json.JSONDecodeError:
                                continue

            except requests.exceptions.Timeout:
                yield f"data: {json.dumps({'error': 'Query timed out'})}\n\n"
            except Exception as e:
                yield f"data: {json.dumps({'error': str(e)})}\n\n"

        # Return streaming response with Server-Sent Events
        return Response(
            stream_with_context(generate()),
            mimetype='text/event-stream',
            headers={
                'Cache-Control': 'no-cache',
                'X-Accel-Buffering': 'no',  # Disable Nginx buffering
                'Connection': 'keep-alive'
            }
        )

    except Exception as e:
        DXP_LOGGER.error(f"Error in chatbot query: {e}")
        return jsonify({'success': False, 'error': str(e)})


@app.route('/json-record', methods=['POST'])
def json_record():
    """Return a single JSON record from server cache for in-page pagination."""
    try:
        payload = request.get_json(force=True)
        cache_key = payload.get('cache_key')
        record_index = int(payload.get('record', 0))

        if not cache_key or cache_key not in JSON_DATA_CACHE:
            return jsonify({'success': False, 'error': 'Cache not found'}), 400

        data_list, json_format = JSON_DATA_CACHE[cache_key]
        total = len(data_list)
        if total == 0:
            return jsonify({'success': True, 'record': {}, 'total': 0, 'record_edits': {}})

        # Clamp index
        if record_index < 0:
            record_index = 0
        if record_index >= total:
            record_index = total - 1

        current = data_list[record_index]

        # Apply cached edits if any
        record_edits = {}
        if cache_key in JSON_EDITS_CACHE and record_index in JSON_EDITS_CACHE[cache_key]:
            record_edits = JSON_EDITS_CACHE[cache_key][record_index]
            try:
                current = apply_cached_edits_to_record(current.copy(), record_edits)
            except Exception:
                pass

        return jsonify({'success': True, 'record': current, 'total': total, 'record_edits': record_edits})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500


if __name__ == "__main__":
    import os

    port = int(os.environ.get("PORT", "9000"))

    # Only open browser from the main process, not the reloader
    if os.environ.get('WERKZEUG_RUN_MAIN') != 'true':
        try:
            webbrowser.open(f"http://localhost:{port}")
        except Exception:
            pass

    app.run(debug=True, port=port, use_reloader=True)
