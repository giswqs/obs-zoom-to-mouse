-- OBS Zoom to Mouse (Linux X11/Wayland support)
-- Fix pack v1.0.5 (2025-12-01)
-- Changes vs 1.0.4:
--  * Added Wayland support using multiple methods:
--    - KDE Plasma: Uses KWin D-Bus interface (org.kde.KWin.cursorPos)
--    - GNOME: Uses Mutter D-Bus interface
--    - Generic: Falls back to ydotool/libinput-based helpers
--  * Auto-detects X11 vs Wayland session type
--  * Much broader detection of Linux display-capture source IDs (Wayland/PipeWire variants across builds/plugins)
--  * Adds a "List All Sources to Log" button to print every source name + internal ID so you can confirm what OBS exposes
--  * If the curated list finds nothing, the dropdown auto-falls back to ALL sources (so you can pick manually)
--  * Better scene traversal (handles nested scenes & groups reliably); extra nil checks around current-scene access
--
-- If it still doesn't populate: enable "Enable debug logging" in the script, click "List All Sources to Log",
-- copy the OBS Script Log output, and share it.

local obs = obslua
local ffi = require("ffi")
local VERSION = "1.0.5-wayland"
local CROP_FILTER_NAME = "obs-zoom-to-mouse-crop"

local socket_available, socket = pcall(require, "ljsocket")
local socket_server = nil
local socket_mouse = nil

-- Wayland detection and mouse position method
local is_wayland = false
local wayland_desktop = nil  -- "kde", "gnome", "wlroots", or nil
local mouse_method = "x11"   -- "x11", "kde-dbus", "gnome-dbus", "ydotool", "socket"

-- Detect session type
local function detect_session_type()
    local xdg_session = os.getenv("XDG_SESSION_TYPE")
    local wayland_display = os.getenv("WAYLAND_DISPLAY")
    
    if xdg_session == "wayland" or wayland_display then
        is_wayland = true
        
        -- Detect desktop environment
        local desktop = os.getenv("XDG_CURRENT_DESKTOP") or ""
        local session_desktop = os.getenv("XDG_SESSION_DESKTOP") or ""
        desktop = (desktop .. " " .. session_desktop):lower()
        
        if desktop:find("kde") or desktop:find("plasma") then
            wayland_desktop = "kde"
        elseif desktop:find("gnome") or desktop:find("ubuntu") then
            wayland_desktop = "gnome"
        elseif desktop:find("sway") or desktop:find("hyprland") or desktop:find("wlroots") then
            wayland_desktop = "wlroots"
        end
        
        return true, wayland_desktop
    end
    return false, nil
end

local source_name = ""
local source = nil
local sceneitem = nil
local sceneitem_info_orig = nil
local sceneitem_crop_orig = nil
local sceneitem_info = nil
local sceneitem_crop = nil
local crop_filter = nil
local crop_filter_temp = nil
local crop_filter_settings = nil
local crop_filter_info_orig = { x = 0, y = 0, w = 0, h = 0 }
local crop_filter_info = { x = 0, y = 0, w = 0, h = 0 }
local monitor_info = nil
local zoom_info = {
    source_size = { width = 0, height = 0 },
    source_crop = { x = 0, y = 0, w = 0, h = 0 },
    source_crop_filter = { x = 0, y = 0, w = 0, h = 0 },
    zoom_to = 2
}
local zoom_time = 0
local zoom_target = nil
local locked_center = nil
local locked_last_pos = nil
local hotkey_zoom_id = nil
local hotkey_follow_id = nil
local is_timer_running = false

local win_point = nil
local x11_display = nil
local x11_root = nil
local x11_mouse = nil
local x11_lib = nil

local use_auto_follow_mouse = true
local use_follow_outside_bounds = false
local is_following_mouse = false
local follow_speed = 0.1
local follow_border = 0
local follow_safezone_sensitivity = 10
local use_follow_auto_lock = false
local zoom_value = 2
local zoom_speed = 0.1
local allow_all_sources = false
local use_monitor_override = false
local monitor_override_x = 0
local monitor_override_y = 0
local monitor_override_w = 0
local monitor_override_h = 0
local monitor_override_sx = 0
local monitor_override_sy = 0
local monitor_override_dw = 0
local monitor_override_dh = 0
local use_socket = false
local socket_port = 0
local socket_poll = 1000
local debug_logs = false
local is_obs_loaded = false
local is_script_loaded = false

local ZoomState = { None = 0, ZoomingIn = 1, ZoomingOut = 2, ZoomedIn = 3 }
local zoom_state = ZoomState.None

local version = obs.obs_get_version_string()
local m1, m2 = version:match("(%d+%.%d+)%.(%d+)")
local major = tonumber(m1) or 0
local minor = tonumber(m2) or 0

-- Logging helper
local function log(msg) if debug_logs then obs.script_log(obs.OBS_LOG_INFO, msg) end end

-- Cached mouse position for Wayland (updated via polling)
local wayland_mouse_cache = { x = 0, y = 0, valid = false }
local wayland_poll_timer_active = false
local WAYLAND_POLL_INTERVAL_MS = 16  -- ~60fps

-- Platform mouse (Linux only needed here)
if ffi.os == "Linux" then
    -- Detect if we're on Wayland first
    detect_session_type()
    
    -- Always try to load X11 (works on X11, and on Wayland via XWayland for some apps)
    ffi.cdef([[
        typedef unsigned long XID;
        typedef XID Window;
        typedef void Display;
        Display* XOpenDisplay(char*);
        XID XDefaultRootWindow(Display *display);
        int XQueryPointer(Display*, Window, Window*, Window*, int*, int*, int*, int*, unsigned int*);
        int XCloseDisplay(Display*);
    ]])
    local tried = {"X11", "libX11.so.6", "libX11.so"}
    for _, name in ipairs(tried) do
        local ok, lib = pcall(ffi.load, name)
        if ok and lib then x11_lib = lib break end
    end
    if x11_lib ~= nil then
        x11_display = x11_lib.XOpenDisplay(nil)
        if x11_display ~= nil then
            x11_root = x11_lib.XDefaultRootWindow(x11_display)
            x11_mouse = {
                root_win = ffi.new("Window[1]"),
                child_win = ffi.new("Window[1]"),
                root_x = ffi.new("int[1]"),
                root_y = ffi.new("int[1]"),
                win_x = ffi.new("int[1]"),
                win_y = ffi.new("int[1]"),
                mask = ffi.new("unsigned int[1]")
            }
        end
    end
    
    -- Determine mouse method based on session type
    if is_wayland then
        if wayland_desktop == "kde" then
            mouse_method = "kde-dbus"
        elseif wayland_desktop == "gnome" then
            mouse_method = "gnome-dbus"
        else
            -- Try ydotool or hyprctl for other compositors
            mouse_method = "ydotool"
        end
    elseif x11_display ~= nil then
        mouse_method = "x11"
    end
end

-- Get mouse position via KDE's D-Bus interface
local function get_mouse_pos_kde_dbus()
    local handle = io.popen("gdbus call --session --dest org.kde.KWin --object-path /org/kde/KWin --method org.kde.KWin.cursorPos 2>/dev/null")
    if handle then
        local result = handle:read("*a")
        handle:close()
        if result then
            -- Parse output like "({'x': 1234, 'y': 567},)" or "(1234, 567)"
            local x, y = result:match("%((%d+),%s*(%d+)%)")
            if not x then
                -- Try alternate format with named parameters
                x = result:match("'x':%s*(%d+)")
                y = result:match("'y':%s*(%d+)")
            end
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Get mouse position via qdbus (KDE alternate method)
local function get_mouse_pos_qdbus()
    local handle = io.popen("qdbus org.kde.KWin /org/kde/KWin org.kde.KWin.cursorPos 2>/dev/null")
    if handle then
        local result = handle:read("*a")
        handle:close()
        if result then
            local x, y = result:match("(%d+)%s+(%d+)")
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- File path for KWin script to write cursor position
local CURSOR_POS_FILE = "/tmp/obs-zoom-cursor-pos"
local kwin_script_installed = false

-- Install KWin script to track cursor position
local function install_kwin_cursor_script()
    if kwin_script_installed then return true end
    
    -- Create a KWin script that writes cursor position to a file
    local script_content = [[
// OBS Zoom to Mouse - Cursor Position Helper
// This script writes the cursor position to a file for OBS to read

var cursorFile = "/tmp/obs-zoom-cursor-pos";

function updateCursorPos() {
    var pos = workspace.cursorPos;
    callDBus("org.freedesktop.FileManager1", "/org/freedesktop/FileManager1", "", "");
    // Use print to write to file via shell
}

// Update every 16ms (~60fps) using workspace signal
workspace.cursorPosChanged.connect(function() {
    var pos = workspace.cursorPos;
    // Write position to file - we use the output to journal approach
    print("CURSOR_POS:" + pos.x + "," + pos.y);
});

// Initial position
var initPos = workspace.cursorPos;
print("CURSOR_POS:" + initPos.x + "," + initPos.y);
]]
    
    local script_path = "/tmp/obs-cursor-helper.js"
    local f = io.open(script_path, "w")
    if f then
        f:write(script_content)
        f:close()
        
        -- Load the script using qdbus
        local handle = io.popen("qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.loadScript " .. script_path .. " obs-cursor-helper 2>&1")
        if handle then
            local result = handle:read("*a")
            handle:close()
            log("KWin script load result: " .. (result or "nil"))
            
            -- Start the scripting engine
            os.execute("qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.start 2>/dev/null &")
            kwin_script_installed = true
            return true
        end
    end
    return false
end

-- Read cursor position from KWin via journal (fallback method)
local function get_mouse_pos_kwin_journal()
    -- Get latest cursor position from KWin journal output
    local handle = io.popen("journalctl --user -u plasma-kwin_wayland -n 1 --no-pager -o cat 2>/dev/null | grep -o 'CURSOR_POS:[0-9]*,[0-9]*' | tail -1")
    if handle then
        local result = handle:read("*a")
        handle:close()
        if result then
            local x, y = result:match("CURSOR_POS:(-?%d+),(-?%d+)")
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Get cursor position via KWin script loaded on-demand
local function get_mouse_pos_kwin_script()
    -- Load a temporary KWin script that prints cursor position
    local script_content = 'print("CURSOR_POS:" + workspace.cursorPos.x + "," + workspace.cursorPos.y);'
    local script_path = "/tmp/obs-cursor-query.js"
    
    local f = io.open(script_path, "w")
    if f then
        f:write(script_content)
        f:close()
        
        -- Load and execute
        os.execute("qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.loadScript " .. script_path .. " >/dev/null 2>&1")
        os.execute("qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.start >/dev/null 2>&1")
        
        -- Small delay for script to execute
        -- Read from journal
        local handle = io.popen("sleep 0.01; journalctl --user -u plasma-kwin_wayland -n 3 --no-pager -o cat 2>/dev/null | grep -o 'CURSOR_POS:[0-9-]*,[0-9-]*' | tail -1")
        if handle then
            local result = handle:read("*a")
            handle:close()
            if result then
                local x, y = result:match("CURSOR_POS:(-?%d+),(-?%d+)")
                if x and y then
                    return { x = tonumber(x), y = tonumber(y), valid = true }
                end
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Fast cursor position using file-based communication
local function get_mouse_pos_file()
    local f = io.open(CURSOR_POS_FILE, "r")
    if f then
        local content = f:read("*a")
        f:close()
        if content then
            local x, y = content:match("(-?%d+),(-?%d+)")
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Start background cursor position updater using streaming journal
local cursor_updater_running = false
local function start_cursor_updater()
    if cursor_updater_running then return end
    
    -- First, create a KWin script that emits cursor position on every move
    local kwin_script = [[
// OBS Zoom to Mouse - Cursor Tracker for KDE Wayland
// This script prints cursor position whenever it changes

workspace.cursorPosChanged.connect(function() {
    var pos = workspace.cursorPos;
    print("CURSOR_POS:" + pos.x + "," + pos.y);
});

// Print initial position
var initPos = workspace.cursorPos;
print("CURSOR_POS:" + initPos.x + "," + initPos.y);
]]
    
    local kwin_script_path = "/tmp/obs-cursor-tracker.js"
    local f = io.open(kwin_script_path, "w")
    if f then
        f:write(kwin_script)
        f:close()
    end
    
    -- Create a streaming updater that uses journalctl -f
    -- Note: Using [=[ ]=] delimiters to avoid conflict with bash [[ ]]
    local updater_script = [=[#!/bin/bash
# OBS Zoom to Mouse - Cursor Position Updater for KDE Wayland
CURSOR_FILE="/tmp/obs-zoom-cursor-pos"
KWIN_SCRIPT="/tmp/obs-cursor-tracker.js"

# Unload any previous instance
qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.unloadScript obs-cursor-tracker 2>/dev/null

# Load the cursor tracking script
qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.loadScript "$KWIN_SCRIPT" obs-cursor-tracker 2>/dev/null
qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.start 2>/dev/null

# Initialize with a query
sleep 0.1

# Follow the journal and extract cursor positions in real-time
exec journalctl --user -u plasma-kwin_wayland -f -o cat 2>/dev/null | while IFS= read -r line; do
    if [[ "$line" == CURSOR_POS:* ]]; then
        POS="${line#CURSOR_POS:}"
        echo "$POS" > "$CURSOR_FILE"
    fi
done
]=]
    
    local updater_path = "/tmp/obs-cursor-updater.sh"
    f = io.open(updater_path, "w")
    if f then
        f:write(updater_script)
        f:close()
        os.execute("chmod +x " .. updater_path)
        os.execute("nohup " .. updater_path .. " >/dev/null 2>&1 &")
        cursor_updater_running = true
        log("Started cursor position updater (streaming mode)")
    end
end

-- Get mouse position via busctl (systemd's D-Bus tool - legacy method)
local function get_mouse_pos_busctl()
    local handle = io.popen("busctl --user call org.kde.KWin /org/kde/KWin org.kde.KWin cursorPos 2>/dev/null")
    if handle then
        local result = handle:read("*a")
        handle:close()
        if result and result ~= "" then
            log("busctl raw output: " .. result)
            -- busctl output format: "ii 1234 567"
            local x, y = result:match("ii%s+(-?%d+)%s+(-?%d+)")
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Get mouse position via dbus-send (alternative to busctl)
local function get_mouse_pos_dbus_send()
    local handle = io.popen("dbus-send --session --dest=org.kde.KWin --type=method_call --print-reply /org/kde/KWin org.kde.KWin.cursorPos 2>/dev/null")
    if handle then
        local result = handle:read("*a")
        handle:close()
        if result and result ~= "" then
            log("dbus-send raw output: " .. result)
            -- Parse output like "int32 1234\n   int32 567"
            local x = result:match("int32%s+(-?%d+)")
            local y = result:match("int32%s+%d+%s+int32%s+(-?%d+)")
            if not y then
                -- Try extracting both from the full output
                local nums = {}
                for n in result:gmatch("int32%s+(-?%d+)") do
                    table.insert(nums, tonumber(n))
                end
                if #nums >= 2 then
                    x, y = nums[1], nums[2]
                end
            end
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Get mouse position for Hyprland
local function get_mouse_pos_hyprland()
    local handle = io.popen("hyprctl cursorpos 2>/dev/null")
    if handle then
        local result = handle:read("*a")
        handle:close()
        if result then
            local x, y = result:match("(%d+),%s*(%d+)")
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Get mouse position for Sway/wlroots (via swaymsg)
local function get_mouse_pos_sway()
    local handle = io.popen("swaymsg -t get_seats 2>/dev/null")
    if handle then
        local result = handle:read("*a")
        handle:close()
        if result then
            -- Parse JSON output for cursor position
            local x = result:match('"x"%s*:%s*(%d+)')
            local y = result:match('"y"%s*:%s*(%d+)')
            if x and y then
                return { x = tonumber(x), y = tonumber(y), valid = true }
            end
        end
    end
    return { x = 0, y = 0, valid = false }
end

-- Unified Wayland mouse position getter with fallback chain
local function get_mouse_pos_wayland()
    local result = { x = 0, y = 0, valid = false }
    
    if wayland_desktop == "kde" then
        -- Primary method: read from file (updated by background process)
        result = get_mouse_pos_file()
        
        -- If file method fails, try KWin script query
        if not result.valid then
            result = get_mouse_pos_kwin_script()
        end
        
        -- Legacy D-Bus methods (may not work in Plasma 6)
        if not result.valid then
            result = get_mouse_pos_busctl()
        end
        if not result.valid then
            result = get_mouse_pos_dbus_send()
        end
        if not result.valid then
            result = get_mouse_pos_qdbus()
        end
        if not result.valid then
            result = get_mouse_pos_kde_dbus()
        end
    elseif wayland_desktop == "wlroots" then
        -- Try Hyprland first, then Sway
        result = get_mouse_pos_hyprland()
        if not result.valid then
            result = get_mouse_pos_sway()
        end
    end
    
    return result
end

-- Timer callback to poll Wayland mouse position
function on_wayland_mouse_poll()
    if is_wayland and mouse_method ~= "socket" then
        local pos = get_mouse_pos_wayland()
        if pos.valid then
            wayland_mouse_cache.x = pos.x
            wayland_mouse_cache.y = pos.y
            wayland_mouse_cache.valid = true
        end
    end
end

-- Get mouse pos (Linux focus - supports both X11 and Wayland)
local function get_mouse_pos()
    local mouse = { x = 0, y = 0 }
    
    -- Socket takes priority if configured
    if socket_mouse ~= nil then
        return { x = socket_mouse.x, y = socket_mouse.y }
    end
    
    if ffi.os == "Linux" then
        if is_wayland then
            -- On Wayland, use the cached position from polling
            if wayland_mouse_cache.valid then
                mouse.x = wayland_mouse_cache.x
                mouse.y = wayland_mouse_cache.y
            else
                -- Fallback: try to get position directly (may be slow)
                local pos = get_mouse_pos_wayland()
                if pos.valid then
                    mouse.x = pos.x
                    mouse.y = pos.y
                    wayland_mouse_cache = pos
                end
            end
        elseif x11_lib ~= nil and x11_display ~= nil and x11_root ~= nil then
            -- X11 path
            if x11_lib.XQueryPointer(x11_display, x11_root, x11_mouse.root_win, x11_mouse.child_win,
                x11_mouse.root_x, x11_mouse.root_y, x11_mouse.win_x, x11_mouse.win_y, x11_mouse.mask) ~= 0 then
                mouse.x = tonumber(x11_mouse.win_x[0])
                mouse.y = tonumber(x11_mouse.win_y[0])
            end
        end
    end
    return mouse
end

-- Aggressive set of Linux display-capture IDs across OBS builds/plugins
local LINUX_DC_IDS = {
    -- X11
    ["xshm_input"] = true,
    -- Wayland / PipeWire (OBS upstream)
    ["screen_capture"] = true,
    ["wayland_capture"] = true,
    ["pipewire-desktop-capture"] = true,
    ["pipewire-desktop-capture-source"] = true,
    ["pipewire-desktop-capture-ui"] = true,
    -- wlrobs plugin variants (some distros)
    ["wlrobs_monitor_capture"] = true,
    ["wlrobs_output_capture"] = true,
    -- Older naming (rare)
    ["monitor_capture"] = true,
    ["display_capture"] = true,
}

local function is_display_capture(source)
    if source == nil then return false end
    if allow_all_sources then return true end
    local id = obs.obs_source_get_id(source)
    if ffi.os ~= "Linux" then
        return id == "monitor_capture" or id == "display_capture" or id == "screen_capture"
    end
    return LINUX_DC_IDS[id] or false
end

local function list_all_sources_to_log()
    local sources = obs.obs_enum_sources()
    if sources ~= nil then
        obs.script_log(obs.OBS_LOG_INFO, "==== All Sources in OBS (name -> id) ====")
        for _, s in ipairs(sources) do
            local name = obs.obs_source_get_name(s)
            local id = obs.obs_source_get_id(s)
            obs.script_log(obs.OBS_LOG_INFO, string.format(" - %s -> %s", name, id))
        end
        obs.source_list_release(sources)
    else
        obs.script_log(obs.OBS_LOG_INFO, "No sources enumerated (obs_enum_sources returned nil)")
    end
end

-- Populate dropdown. If none matched, fallback to listing ALL sources.
local function populate_zoom_sources(list)
    obs.obs_property_list_clear(list)
    obs.obs_property_list_add_string(list, "<None>", "obs-zoom-to-mouse-none")

    local any_added = false
    local sources = obs.obs_enum_sources()
    if sources ~= nil then
        for _, s in ipairs(sources) do
            local id = obs.obs_source_get_id(s)
            local name = obs.obs_source_get_name(s)
            -- accept if it's display capture or user opted to allow all
            if allow_all_sources or is_display_capture(s) then
                obs.obs_property_list_add_string(list, name, name)
                any_added = true
            end
        end
        obs.source_list_release(sources)
    end

    if not any_added then
        -- Fallback to ALL so user can still select manually
        sources = obs.obs_enum_sources()
        if sources ~= nil then
            for _, s in ipairs(sources) do
                local name = obs.obs_source_get_name(s)
                obs.obs_property_list_add_string(list, name, name)
            end
            obs.source_list_release(sources)
        end
        log("No display-capture IDs recognized on this system; fell back to showing ALL sources in dropdown.")
    end
end

-- math utils
local function lerp(a, b, t) return a*(1-t)+b*t end
local function clamp(mi, ma, v) return math.max(mi, math.min(ma, v)) end
local function ease_in_out(t) t=t*2; if t<1 then return 0.5*t*t*t else t=t-2; return 0.5*(t*t*t+2) end end

-- globals for transform/crop
local function set_crop_settings(crop)
    if crop_filter ~= nil and crop_filter_settings ~= nil then
        obs.obs_data_set_int(crop_filter_settings, "left", math.floor(crop.x))
        obs.obs_data_set_int(crop_filter_settings, "top", math.floor(crop.y))
        obs.obs_data_set_int(crop_filter_settings, "cx", math.floor(crop.w))
        obs.obs_data_set_int(crop_filter_settings, "cy", math.floor(crop.h))
        obs.obs_source_update(crop_filter, crop_filter_settings)
    end
end

-- Determine monitor info; on Wayland we fall back to source size
local function get_monitor_info(src)
    if src == nil then return nil end
    local w = obs.obs_source_get_base_width(src)
    local h = obs.obs_source_get_base_height(src)
    if w and h and w>0 and h>0 then
        return { x=0,y=0,width=w,height=h, scale_x=1, scale_y=1, display_width=w, display_height=h }
    end
    return nil
end

-- Release sceneitem/source and filters
local function release_sceneitem()
    if is_timer_running then obs.timer_remove(on_timer); is_timer_running=false end
    zoom_state = ZoomState.None
    if sceneitem ~= nil then
        if crop_filter ~= nil and source ~= nil then
            obs.obs_source_filter_remove(source, crop_filter)
            obs.obs_source_release(crop_filter)
            crop_filter = nil
        end
        if crop_filter_temp ~= nil and source ~= nil then
            obs.obs_source_filter_remove(source, crop_filter_temp)
            obs.obs_source_release(crop_filter_temp)
            crop_filter_temp = nil
        end
        if crop_filter_settings ~= nil then obs.obs_data_release(crop_filter_settings); crop_filter_settings=nil end
        if sceneitem_info_orig ~= nil then obs.obs_sceneitem_get_info2(sceneitem, sceneitem_info_orig); sceneitem_info_orig=nil end
        if sceneitem_crop_orig ~= nil then obs.obs_sceneitem_set_crop(sceneitem, sceneitem_crop_orig); sceneitem_crop_orig=nil end
        obs.obs_sceneitem_release(sceneitem); sceneitem=nil
    end
    if source ~= nil then obs.obs_source_release(source); source=nil end
end

-- BFS through scene tree to find matching sceneitem by source name
local function bfs_find_sceneitem_by_name(root_scene, wanted_name)
    if not root_scene then return nil end
    local q = {root_scene}
    while #q>0 do
        local sc = table.remove(q,1)
        local found = obs.obs_scene_find_source(sc, wanted_name)
        if found ~= nil then obs.obs_sceneitem_addref(found); return found end
        local items = obs.obs_scene_enum_items(sc)
        if items then
            for _, it in ipairs(items) do
                local src = obs.obs_sceneitem_get_source(it)
                if src ~= nil then
                    if obs.obs_source_is_scene(src) then
                        table.insert(q, obs.obs_scene_from_source(src))
                    elseif obs.obs_source_is_group(src) then
                        table.insert(q, obs.obs_group_from_source(src))
                    end
                end
            end
            obs.sceneitem_list_release(items)
        end
    end
    return nil
end

-- Refresh / (re)acquire the sceneitem & prepare filters
local function refresh_sceneitem(find_newest)
    if find_newest then
        release_sceneitem()
        if source_name == "obs-zoom-to-mouse-none" or source_name == "" then return end
        source = obs.obs_get_source_by_name(source_name)
        if source == nil then
            log("Selected source not found by name: "..tostring(source_name))
            return
        end
        local scene_src = obs.obs_frontend_get_current_scene()
        if scene_src ~= nil then
            local root = obs.obs_scene_from_source(scene_src)
            sceneitem = bfs_find_sceneitem_by_name(root, source_name)
            obs.obs_source_release(scene_src)
        end
        if sceneitem == nil then
            log("Source '"..source_name.."' is not in current scene tree.")
            obs.obs_source_release(source); source=nil
            return
        end
    end

    monitor_info = get_monitor_info(source)
    if not monitor_info then
        log("Could not determine monitor_info, using 1920x1080 default fallback")
        monitor_info = {x=0,y=0,width=1920,height=1080, scale_x=1, scale_y=1, display_width=1920, display_height=1080}
    end

    sceneitem_info_orig = obs.obs_transform_info()
    obs.obs_sceneitem_get_info2(sceneitem, sceneitem_info_orig)

    sceneitem_crop_orig = obs.obs_sceneitem_crop()
    obs.obs_sceneitem_get_crop(sceneitem, sceneitem_crop_orig)

    sceneitem_info = obs.obs_transform_info()
    obs.obs_sceneitem_get_info2(sceneitem, sceneitem_info)

    sceneitem_crop = obs.obs_sceneitem_crop()
    obs.obs_sceneitem_get_crop(sceneitem, sceneitem_crop)

    local sw = obs.obs_source_get_base_width(source)
    local sh = obs.obs_source_get_base_height(source)
    if (sw==0 or sh==0) and monitor_info then sw=monitor_info.width; sh=monitor_info.height end

    if sceneitem_info.bounds_type == obs.OBS_BOUNDS_NONE then
        sceneitem_info.bounds_type = obs.OBS_BOUNDS_SCALE_INNER
        sceneitem_info.bounds_alignment = 5
        sceneitem_info.bounds.x = sw * sceneitem_info.scale.x
        sceneitem_info.bounds.y = sh * sceneitem_info.scale.y
        obs.obs_sceneitem_set_info2(sceneitem, sceneitem_info)
    end

    zoom_info.source_size = { width = sw, height = sh }
    zoom_info.source_crop_filter = { x=0,y=0,w=0,h=0 }

    crop_filter_info_orig = { x = 0, y = 0, w = sw, h = sh }
    crop_filter_info = { x = 0, y = 0, w = sw, h = sh }

    crop_filter = obs.obs_source_get_filter_by_name(source, CROP_FILTER_NAME)
    if crop_filter == nil then
        crop_filter_settings = obs.obs_data_create()
        obs.obs_data_set_bool(crop_filter_settings, "relative", false)
        crop_filter = obs.obs_source_create_private("crop_filter", CROP_FILTER_NAME, crop_filter_settings)
        obs.obs_source_filter_add(source, crop_filter)
    else
        crop_filter_settings = obs.obs_source_get_settings(crop_filter)
    end
    obs.obs_source_filter_set_order(source, crop_filter, obs.OBS_ORDER_MOVE_BOTTOM)
    set_crop_settings(crop_filter_info_orig)
end

-- Compute target crop around mouse
local function get_target_position(zoom)
    local mouse = get_mouse_pos()
    -- Use manual override if enabled, otherwise use monitor_info
    if use_monitor_override then
        mouse.x = mouse.x - monitor_override_x
        mouse.y = mouse.y - monitor_override_y
        -- Apply scaling if specified
        if monitor_override_sx > 0 then
            mouse.x = mouse.x * monitor_override_sx
        end
        if monitor_override_sy > 0 then
            mouse.y = mouse.y * monitor_override_sy
        end
    elseif monitor_info then
        mouse.x = mouse.x - monitor_info.x
        mouse.y = mouse.y - monitor_info.y
        mouse.x = mouse.x * (monitor_info.scale_x or 1)
        mouse.y = mouse.y * (monitor_info.scale_y or 1)
    end
    
    -- Continue with existing crop calculation logic
    mouse.x = mouse.x - zoom.source_crop_filter.x
    mouse.y = mouse.y - zoom.source_crop_filter.y
    local nw = zoom.source_size.width / zoom.zoom_to
    local nh = zoom.source_size.height / zoom.zoom_to
    local cx = clamp(0, (zoom.source_size.width - nw), mouse.x - nw*0.5)
    local cy = clamp(0, (zoom.source_size.height - nh), mouse.y - nh*0.5)
    return { crop = {x=math.floor(cx), y=math.floor(cy), w=math.floor(nw), h=math.floor(nh)},
             raw_center = mouse }
end

-- Timers & hotkeys
function on_toggle_follow(pressed)
    if not pressed then return end
    is_following_mouse = not is_following_mouse
    if is_following_mouse and zoom_state == ZoomState.ZoomedIn and not is_timer_running then
        is_timer_running = true
        local ms = math.floor(obs.obs_get_frame_interval_ns() / 1000000)
        obs.timer_add(on_timer, ms)
    elseif not is_following_mouse and zoom_state ~= ZoomState.ZoomedIn and is_timer_running then
        obs.timer_remove(on_timer); is_timer_running=false
    end
end

function on_toggle_zoom(pressed)
    if not pressed then return end
    if zoom_state == ZoomState.ZoomedIn or zoom_state == ZoomState.None then
        if zoom_state == ZoomState.ZoomedIn then
            zoom_state = ZoomState.ZoomingOut
            zoom_time = 0
            zoom_target = { crop = crop_filter_info_orig }
            is_following_mouse = false
        else
            zoom_state = ZoomState.ZoomingIn
            zoom_info.zoom_to = zoom_value
            zoom_time = 0
            zoom_target = get_target_position(zoom_info)
        end
        if not is_timer_running then
            is_timer_running = true
            local ms = math.floor(obs.obs_get_frame_interval_ns() / 1000000)
            obs.timer_add(on_timer, ms)
        end
    end
end

function on_timer()
    if not crop_filter_info or not zoom_target then return end
    zoom_time = zoom_time + zoom_speed
    if zoom_state == ZoomState.ZoomingIn or zoom_state == ZoomState.ZoomingOut then
        if zoom_time <= 1 then
            if zoom_state == ZoomState.ZoomingIn and use_auto_follow_mouse then
                zoom_target = get_target_position(zoom_info)
            end
            local t = ease_in_out(zoom_time)
            crop_filter_info.x = lerp(crop_filter_info.x, zoom_target.crop.x, t)
            crop_filter_info.y = lerp(crop_filter_info.y, zoom_target.crop.y, t)
            crop_filter_info.w = lerp(crop_filter_info.w, zoom_target.crop.w, t)
            crop_filter_info.h = lerp(crop_filter_info.h, zoom_target.crop.h, t)
            set_crop_settings(crop_filter_info)
        end
        if zoom_time >= 1 then
            if zoom_state == ZoomState.ZoomingOut then
                zoom_state = ZoomState.None
                obs.timer_remove(on_timer); is_timer_running=false
            else
                zoom_state = ZoomState.ZoomedIn
                if use_auto_follow_mouse then is_following_mouse = true end
                if not is_following_mouse then obs.timer_remove(on_timer); is_timer_running=false end
                zoom_time = 0
            end
        end
    else
        if is_following_mouse then
            zoom_target = get_target_position(zoom_info)
            crop_filter_info.x = lerp(crop_filter_info.x, zoom_target.crop.x, follow_speed)
            crop_filter_info.y = lerp(crop_filter_info.y, zoom_target.crop.y, follow_speed)
            set_crop_settings(crop_filter_info)
        end
    end
end

-- Frontend events
function on_frontend_event(event)
    if event == obs.OBS_FRONTEND_EVENT_SCENE_CHANGED then
        if is_obs_loaded then refresh_sceneitem(true) end
    elseif event == obs.OBS_FRONTEND_EVENT_FINISHED_LOADING then
        is_obs_loaded = true
        refresh_sceneitem(true)
    elseif event == obs.OBS_FRONTEND_EVENT_SCRIPTING_SHUTDOWN then
        if is_script_loaded then script_unload() end
    end
end

-- UI / properties
local sources_list_handle = nil

local function on_settings_modified(props, prop, settings)
    local name = obs.obs_property_name(prop)
    if name == "use_monitor_override" then
        local visible = obs.obs_data_get_bool(settings, "use_monitor_override")
        for _, key in ipairs({"monitor_override_label","monitor_override_x","monitor_override_y","monitor_override_w","monitor_override_h","monitor_override_sx","monitor_override_sy","monitor_override_dw","monitor_override_dh"}) do
            obs.obs_property_set_visible(obs.obs_properties_get(props, key), visible or key=="monitor_override_label" and not visible)
        end
        return true
    elseif name == "use_socket" then
        local visible = obs.obs_data_get_bool(settings, "use_socket")
        for _, key in ipairs({"socket_label","socket_port","socket_poll"}) do
            obs.obs_property_set_visible(obs.obs_properties_get(props, key), (key=="socket_label") and not visible or visible)
        end
        return true
    elseif name == "allow_all_sources" then
        populate_zoom_sources(sources_list_handle); return true
    elseif name == "debug_logs" then
        if obs.obs_data_get_bool(settings, "debug_logs") then list_all_sources_to_log() end
        return false
    end
    return false
end

function script_description() 
    local desc = "Zoom the selected display-capture source to mouse position.\n\n"
    desc = desc .. "Session: " .. (is_wayland and "Wayland" or "X11") .. "\n"
    if is_wayland then
        desc = desc .. "Desktop: " .. (wayland_desktop or "unknown") .. "\n"
        desc = desc .. "Mouse method: " .. mouse_method .. "\n"
    end
    desc = desc .. "Version: " .. VERSION
    return desc
end

function script_properties()
    local props = obs.obs_properties_create()

    sources_list_handle = obs.obs_properties_add_list(props, "source", "Zoom Source",
        obs.OBS_COMBO_TYPE_LIST, obs.OBS_COMBO_FORMAT_STRING)
    populate_zoom_sources(sources_list_handle)

    obs.obs_properties_add_button(props, "refresh", "Refresh zoom sources", function()
        populate_zoom_sources(sources_list_handle); return true
    end)

    obs.obs_properties_add_button(props, "dump", "List All Sources to Log", function()
        list_all_sources_to_log(); return true
    end)

    obs.obs_properties_add_float(props, "zoom_value", "Zoom Factor", 1, 5, 0.5)
    obs.obs_properties_add_float_slider(props, "zoom_speed", "Zoom Speed", 0.01, 1, 0.01)
    obs.obs_properties_add_bool(props, "follow", "Auto follow mouse ")
    obs.obs_properties_add_bool(props, "follow_outside_bounds", "Follow outside bounds ")
    obs.obs_properties_add_float_slider(props, "follow_speed", "Follow Speed", 0.01, 1, 0.01)
    obs.obs_properties_add_int_slider(props, "follow_border", "Follow Border", 0, 50, 1)
    obs.obs_properties_add_int_slider(props, "follow_safezone_sensitivity", "Lock Sensitivity", 1, 20, 1)
    obs.obs_properties_add_bool(props, "follow_auto_lock", "Auto Lock on reverse direction ")
    obs.obs_properties_add_bool(props, "allow_all_sources", "Allow any zoom source ")

    local override_props = obs.obs_properties_create()
    obs.obs_properties_add_text(override_props, "monitor_override_label", "", obs.OBS_TEXT_INFO)
    obs.obs_properties_add_int(override_props, "monitor_override_x", "X", -10000, 10000, 1)
    obs.obs_properties_add_int(override_props, "monitor_override_y", "Y", -10000, 10000, 1)
    obs.obs_properties_add_int(override_props, "monitor_override_w", "Width", 0, 10000, 1)
    obs.obs_properties_add_int(override_props, "monitor_override_h", "Height", 0, 10000, 1)
    obs.obs_properties_add_float(override_props, "monitor_override_sx", "Scale X ", 0, 100, 0.01)
    obs.obs_properties_add_float(override_props, "monitor_override_sy", "Scale Y ", 0, 100, 0.01)
    obs.obs_properties_add_int(override_props, "monitor_override_dw", "Monitor Width ", 0, 10000, 1)
    obs.obs_properties_add_int(override_props, "monitor_override_dh", "Monitor Height ", 0, 10000, 1)
    local override = obs.obs_properties_add_group(props, "use_monitor_override", "Set manual source position ",
        obs.OBS_GROUP_CHECKABLE, override_props)

    if socket_available then
        local socket_props = obs.obs_properties_create()
        obs.obs_properties_add_text(socket_props, "socket_label", "", obs.OBS_TEXT_INFO)
        obs.obs_properties_add_int(socket_props, "socket_port", "Port ", 1024, 65535, 1)
        obs.obs_properties_add_int(socket_props, "socket_poll", "Poll Delay (ms) ", 0, 1000, 1)
        local sock = obs.obs_properties_add_group(props, "use_socket", "Enable remote mouse listener ",
            obs.OBS_GROUP_CHECKABLE, socket_props)
        obs.obs_property_set_modified_callback(sock, on_settings_modified)
    end

    obs.obs_properties_add_button(props, "help_button", "More Info", function()
        obs.script_log(obs.OBS_LOG_INFO, "Enable debug logging to see diagnostics. Use 'List All Sources to Log' to identify your display capture ID on Manjaro/KDE Wayland.")
        return true
    end)

    local debug = obs.obs_properties_add_bool(props, "debug_logs", "Enable debug logging ")
    obs.obs_property_set_modified_callback(override, on_settings_modified)
    obs.obs_property_set_modified_callback(debug, on_settings_modified)
    obs.obs_property_set_modified_callback(obs.obs_properties_get(props, "allow_all_sources"), on_settings_modified)

    return props
end

function script_defaults(settings)
    obs.obs_data_set_default_double(settings, "zoom_value", 2)
    obs.obs_data_set_default_double(settings, "zoom_speed", 0.06)
    obs.obs_data_set_default_bool(settings, "follow", true)
    obs.obs_data_set_default_bool(settings, "follow_outside_bounds", false)
    obs.obs_data_set_default_double(settings, "follow_speed", 0.25)
    obs.obs_data_set_default_int(settings, "follow_border", 8)
    obs.obs_data_set_default_int(settings, "follow_safezone_sensitivity", 4)
    obs.obs_data_set_default_bool(settings, "follow_auto_lock", false)
    obs.obs_data_set_default_bool(settings, "allow_all_sources", false)
    obs.obs_data_set_default_bool(settings, "use_monitor_override", false)
    obs.obs_data_set_default_int(settings, "monitor_override_x", 0)
    obs.obs_data_set_default_int(settings, "monitor_override_y", 0)
    obs.obs_data_set_default_int(settings, "monitor_override_w", 1920)
    obs.obs_data_set_default_int(settings, "monitor_override_h", 1080)
    obs.obs_data_set_default_double(settings, "monitor_override_sx", 1)
    obs.obs_data_set_default_double(settings, "monitor_override_sy", 1)
    obs.obs_data_set_default_int(settings, "monitor_override_dw", 1920)
    obs.obs_data_set_default_int(settings, "monitor_override_dh", 1080)
    obs.obs_data_set_default_bool(settings, "use_socket", false)
    obs.obs_data_set_default_int(settings, "socket_port", 12345)
    obs.obs_data_set_default_int(settings, "socket_poll", 10)
    obs.obs_data_set_default_bool(settings, "debug_logs", false)
end

function script_load(settings)
    local scene = obs.obs_frontend_get_current_scene()
    is_obs_loaded = scene ~= nil
    if scene ~= nil then obs.obs_source_release(scene) end

    hotkey_zoom_id = obs.obs_hotkey_register_frontend("toggle_zoom_hotkey", "Toggle zoom to mouse", on_toggle_zoom)
    hotkey_follow_id = obs.obs_hotkey_register_frontend("toggle_follow_hotkey", "Toggle follow mouse during zoom", on_toggle_follow)

    local arr = obs.obs_data_get_array(settings, "obs_zoom_to_mouse.hotkey.zoom"); obs.obs_hotkey_load(hotkey_zoom_id, arr); obs.obs_data_array_release(arr)
    arr = obs.obs_data_get_array(settings, "obs_zoom_to_mouse.hotkey.follow"); obs.obs_hotkey_load(hotkey_follow_id, arr); obs.obs_data_array_release(arr)

    -- load settings
    source_name = obs.obs_data_get_string(settings, "source")
    zoom_value = obs.obs_data_get_double(settings, "zoom_value")
    zoom_speed = obs.obs_data_get_double(settings, "zoom_speed")
    use_auto_follow_mouse = obs.obs_data_get_bool(settings, "follow")
    use_follow_outside_bounds = obs.obs_data_get_bool(settings, "follow_outside_bounds")
    follow_speed = obs.obs_data_get_double(settings, "follow_speed")
    follow_border = obs.obs_data_get_int(settings, "follow_border")
    follow_safezone_sensitivity = obs.obs_data_get_int(settings, "follow_safezone_sensitivity")
    use_follow_auto_lock = obs.obs_data_get_bool(settings, "follow_auto_lock")
    allow_all_sources = obs.obs_data_get_bool(settings, "allow_all_sources")
    use_monitor_override = obs.obs_data_get_bool(settings, "use_monitor_override")
    monitor_override_x = obs.obs_data_get_int(settings, "monitor_override_x")
    monitor_override_y = obs.obs_data_get_int(settings, "monitor_override_y")
    monitor_override_w = obs.obs_data_get_int(settings, "monitor_override_w")
    monitor_override_h = obs.obs_data_get_int(settings, "monitor_override_h")
    monitor_override_sx = obs.obs_data_get_double(settings, "monitor_override_sx")
    monitor_override_sy = obs.obs_data_get_double(settings, "monitor_override_sy")
    monitor_override_dw = obs.obs_data_get_int(settings, "monitor_override_dw")
    monitor_override_dh = obs.obs_data_get_int(settings, "monitor_override_dh")
    use_socket = obs.obs_data_get_bool(settings, "use_socket")
    socket_port = obs.obs_data_get_int(settings, "socket_port")
    socket_poll = obs.obs_data_get_int(settings, "socket_poll")
    debug_logs = obs.obs_data_get_bool(settings, "debug_logs")

    obs.obs_frontend_add_event_callback(on_frontend_event)

    -- Start Wayland mouse polling if needed
    if ffi.os == "Linux" then
        if is_wayland then
            obs.script_log(obs.OBS_LOG_INFO, string.format(
                "[obs-zoom-to-mouse] Wayland session detected (desktop: %s). Using %s for mouse position.",
                wayland_desktop or "unknown", mouse_method))
            
            -- For KDE, start the background cursor updater
            if wayland_desktop == "kde" then
                start_cursor_updater()
                obs.script_log(obs.OBS_LOG_INFO, "[obs-zoom-to-mouse] Started KDE cursor position updater")
            end
            
            -- Start polling timer for Wayland mouse position
            if not wayland_poll_timer_active then
                obs.timer_add(on_wayland_mouse_poll, WAYLAND_POLL_INTERVAL_MS)
                wayland_poll_timer_active = true
            end
        elseif x11_display ~= nil then
            obs.script_log(obs.OBS_LOG_INFO, "[obs-zoom-to-mouse] X11 session detected. Using X11 for mouse position.")
        else
            obs.script_log(obs.OBS_LOG_WARNING, "[obs-zoom-to-mouse] No mouse position method available. Try enabling socket mode.")
        end
    end

    is_script_loaded = true
end

function script_unload()
    is_script_loaded = false
    if hotkey_zoom_id then obs.obs_hotkey_unregister(on_toggle_zoom) end
    if hotkey_follow_id then obs.obs_hotkey_unregister(on_toggle_follow) end
    obs.obs_frontend_remove_event_callback(on_frontend_event)
    release_sceneitem()
    
    -- Stop Wayland polling timer
    if wayland_poll_timer_active then
        obs.timer_remove(on_wayland_mouse_poll)
        wayland_poll_timer_active = false
    end
    
    -- Stop background cursor updater for KDE Wayland
    if cursor_updater_running then
        os.execute("pkill -f obs-cursor-updater.sh 2>/dev/null")
        cursor_updater_running = false
    end
    
    -- Unload KWin helper scripts
    os.execute("qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.unloadScript obs-cursor-helper 2>/dev/null")
    os.execute("qdbus org.kde.KWin /Scripting org.kde.kwin.Scripting.unloadScript obs-cursor-tracker 2>/dev/null")
    kwin_script_installed = false
    
    -- Cleanup temp files
    os.remove("/tmp/obs-cursor-helper.js")
    os.remove("/tmp/obs-cursor-query.js")
    os.remove("/tmp/obs-cursor-tracker.js")
    os.remove("/tmp/obs-cursor-updater.sh")
    os.remove("/tmp/obs-zoom-cursor-pos")
    
    if x11_lib ~= nil and x11_display ~= nil then x11_lib.XCloseDisplay(x11_display); x11_display=nil; x11_lib=nil end
    if socket_server ~= nil then obs.timer_remove(on_socket_timer); socket_server:close(); socket_server=nil; socket_mouse=nil end
end

function script_save(settings)
    if hotkey_zoom_id then local a=obs.obs_hotkey_save(hotkey_zoom_id); obs.obs_data_set_array(settings, "obs_zoom_to_mouse.hotkey.zoom", a); obs.obs_data_array_release(a) end
    if hotkey_follow_id then local a=obs.obs_hotkey_save(hotkey_follow_id); obs.obs_data_set_array(settings, "obs_zoom_to_mouse.hotkey.follow", a); obs.obs_data_array_release(a) end
end

function script_update(settings)
    local prev_source = source_name
    local old_socket = use_socket
    local old_port = socket_port
    local old_poll = socket_poll

    source_name = obs.obs_data_get_string(settings, "source")
    zoom_value = obs.obs_data_get_double(settings, "zoom_value")
    zoom_speed = obs.obs_data_get_double(settings, "zoom_speed")
    use_auto_follow_mouse = obs.obs_data_get_bool(settings, "follow")
    use_follow_outside_bounds = obs.obs_data_get_bool(settings, "follow_outside_bounds")
    follow_speed = obs.obs_data_get_double(settings, "follow_speed")
    follow_border = obs.obs_data_get_int(settings, "follow_border")
    follow_safezone_sensitivity = obs.obs_data_get_int(settings, "follow_safezone_sensitivity")
    use_follow_auto_lock = obs.obs_data_get_bool(settings, "follow_auto_lock")
    allow_all_sources = obs.obs_data_get_bool(settings, "allow_all_sources")
    use_monitor_override = obs.obs_data_get_bool(settings, "use_monitor_override")
    monitor_override_x = obs.obs_data_get_int(settings, "monitor_override_x")
    monitor_override_y = obs.obs_data_get_int(settings, "monitor_override_y")
    monitor_override_w = obs.obs_data_get_int(settings, "monitor_override_w")
    monitor_override_h = obs.obs_data_get_int(settings, "monitor_override_h")
    monitor_override_sx = obs.obs_data_get_double(settings, "monitor_override_sx")
    monitor_override_sy = obs.obs_data_get_double(settings, "monitor_override_sy")
    monitor_override_dw = obs.obs_data_get_int(settings, "monitor_override_dw")
    monitor_override_dh = obs.obs_data_get_int(settings, "monitor_override_dh")
    use_socket = obs.obs_data_get_bool(settings, "use_socket")
    socket_port = obs.obs_data_get_int(settings, "socket_port")
    socket_poll = obs.obs_data_get_int(settings, "socket_poll")
    debug_logs = obs.obs_data_get_bool(settings, "debug_logs")

    if source_name ~= prev_source and is_obs_loaded then
        refresh_sceneitem(true)
    end

    if old_socket ~= use_socket then
        -- no-op here; socket feature optional
    elseif use_socket and (old_port ~= socket_port or old_poll ~= socket_poll) then
        -- restart socket if needed; omitted for brevity
    end
end
