#!/usr/bin/env python3
"""
OBS Zoom Toggle - Triggers the zoom hotkey via WebSocket
Usage: ./obs-zoom-toggle.py [password]

If password is not provided, it will try without authentication first,
then prompt or use environment variable OBS_WEBSOCKET_PASSWORD.
"""

import sys
import os

try:
    import obsws_python as obs
except ImportError:
    print("Error: obsws_python not installed. Run: pip install obsws-python")
    sys.exit(1)

def trigger_zoom(password=None):
    try:
        # Connect to OBS WebSocket
        if password:
            cl = obs.ReqClient(host='localhost', port=4455, password=password)
        else:
            # Try without password first (if auth is disabled)
            cl = obs.ReqClient(host='localhost', port=4455, password='')
        
        # Trigger the zoom hotkey
        cl.trigger_hotkey_by_name('toggle_zoom_hotkey')
        print("Zoom toggled!")
        return True
    except Exception as e:
        error_msg = str(e)
        if 'Authentication' in error_msg or 'auth' in error_msg.lower():
            print(f"Authentication required. Please provide password.")
            return False
        elif 'Connection refused' in error_msg:
            print("Error: Cannot connect to OBS. Make sure OBS is running and WebSocket is enabled.")
            print("Go to OBS → Tools → WebSocket Server Settings → Enable WebSocket Server")
        else:
            print(f"Error: {e}")
        return False

if __name__ == '__main__':
    # Get password from argument, environment, or config file
    password = None
    
    if len(sys.argv) > 1:
        password = sys.argv[1]
    elif os.environ.get('OBS_WEBSOCKET_PASSWORD'):
        password = os.environ['OBS_WEBSOCKET_PASSWORD']
    else:
        # Try to read from config file
        config_file = os.path.expanduser('~/.config/obs-zoom-password')
        if os.path.exists(config_file):
            with open(config_file) as f:
                password = f.read().strip()
    
    if not trigger_zoom(password):
        if not password:
            print("\nTo set password, either:")
            print("1. Run: echo 'your_password' > ~/.config/obs-zoom-password")
            print("2. Or set environment variable: export OBS_WEBSOCKET_PASSWORD='your_password'")
            print("3. Or disable authentication in OBS WebSocket settings")
        sys.exit(1)
