--[[
    OPSYX PLATOBOOST USERID KEY SYSTEM - FIXED + LAUNCH CONTEXT v1

    Service ID: 31267
    Identifier: SHA-256(tostring(LocalPlayer.UserId))

    NO DEVICE/HWID/MAC/IP/PC IDENTIFIER IS USED.

    Platoboost public verification flow:
      GET https://api.platoboost.app/public/whitelist/{service}
      ?identifier=<hashed UserId>&key=<key>&nonce=<nonce>
      (api.platoboost.net is used as fallback)

    The returned integrity hash is verified as:
      SHA-256("true-" .. nonce .. "-" .. secret)

    IMPORTANT:
    - This is a CLIENT-SIDE Platoboost integration.
    - The secret is therefore visible to a capable client and should be
      rotated if it has been exposed.
    - The raw OPSYX1 URL is never fetched until authentication succeeds.
]]

if not game:IsLoaded() then
    game.Loaded:Wait()
end

--// ============================================================
--// SERVICES
--// ============================================================

local Players = game:GetService("Players")
local TweenService = game:GetService("TweenService")
local HttpService = game:GetService("HttpService")
local CoreGui = game:GetService("CoreGui")
local GuiService = game:GetService("GuiService")
local UserInputService = game:GetService("UserInputService")

local LocalPlayer = Players.LocalPlayer or Players.PlayerAdded:Wait()
local PlayerGui = LocalPlayer:WaitForChild("PlayerGui")

--// ============================================================
--// CONFIG
--// ============================================================

local SERVICE_ID = 31267
local VERSION = "2.1.0"
local PLATOBOOST_API_SECRET = "b952215a-a2ca-43b4-9841-3c090c4d51eb"

--// Current Platoboost integrations use these public API hosts.
--// Prefer .app and fall back to .net when the primary host is unavailable.
local PLATOBOOST_HOSTS = {
    "https://api.platoboost.app",
    "https://api.platoboost.net",
}

local RAW_URL = "https://raw.githubusercontent.com/projectopsyx-lang/opsyxkey/refs/heads/main/opsyxload.lua"

local DISCORD_URL = "https://discord.com/users/1529328825685508209"

local REQUEST_TIMEOUT = 12
local HOST_TIMEOUT = 7
local MAX_RETRIES = 2
local RETRY_BASE_DELAY = 0.35
local MAX_KEY_LENGTH = 256
local REDUCED_MOTION_DEFAULT = false
local SAVE_KEY = true

--// Saved key is account-scoped by Roblox UserId.
--// This is NOT a device identifier.
local SAVE_FILE = "OPSYX_SavedKey_" .. tostring(LocalPlayer.UserId) .. ".txt"
local LAST_HOST_FILE = "OPSYX_LastHost_" .. tostring(LocalPlayer.UserId) .. ".txt"

--// ============================================================
--// STATE
--// ============================================================

local userId = tostring(LocalPlayer.UserId)
local username = LocalPlayer.Name

local alive = true
local verifying = false
local authenticated = false
local hasExecuted = false
local verificationToken = 0
local keyVisible = false
local activeHost = nil
local rememberedHost = nil
local lastLatencyMs = nil
local lastHttpStatus = nil
local lastDiagnostic = "No diagnostic information yet."
local maintenanceDetected = false
local reducedMotion = REDUCED_MOTION_DEFAULT
local dragging = false

--// ============================================================
--// HTTP REQUEST RESOLVER
--// ============================================================

local cachedRequester = false
local requestResolverFinished = false

local function resolveRequestFunction()
    if requestResolverFinished then
        return cachedRequester or nil
    end

    requestResolverFinished = true

    --// Resolve once. These globals are safe to inspect directly.
    if type(syn) == "table" and type(syn.request) == "function" then
        cachedRequester = syn.request
    elseif type(request) == "function" then
        cachedRequester = request
    elseif type(http_request) == "function" then
        cachedRequester = http_request
    elseif type(syn_request) == "function" then
        cachedRequester = syn_request
    elseif type(http) == "table" and type(http.request) == "function" then
        cachedRequester = http.request
    elseif type(fluxus) == "table" and type(fluxus.request) == "function" then
        cachedRequester = fluxus.request
    end

    return cachedRequester or nil
end

--// ============================================================
--// UTILITIES
--// ============================================================

local function trim(value)
    if type(value) ~= "string" then
        return ""
    end

    return (value:gsub("^%s*(.-)%s*$", "%1"))
end

local function urlEncode(value)
    value = tostring(value)

    return value:gsub("[^%w%-%._~]", function(c)
        return string.format("%%%02X", string.byte(c))
    end)
end

local function destroyIfExists(parent, name)
    local old = parent:FindFirstChild(name)
    if old then
        old:Destroy()
    end
end

local function new(className, props, parent)
    local object = Instance.new(className)

    --// One protected property batch instead of one pcall per property.
    --// All properties in this file are known Roblox properties.
    if props then
        pcall(function()
            for property, value in pairs(props) do
                object[property] = value
            end
        end)
    end

    if parent then
        object.Parent = parent
    end

    return object
end

local function warnOPSYX(message)
    warn("[OPSYX] " .. tostring(message))
end

--// ============================================================
--// SHA256
--// ============================================================

local cachedSHA256 = false
local sha256Resolved = false

local function sha256(value)
    value = tostring(value)

    if cachedSHA256 then
        local ok, result = pcall(cachedSHA256, value)
        if ok and type(result) == "string" and #result > 0 then
            return string.lower(result)
        end
    elseif sha256Resolved then
        return nil
    end

    sha256Resolved = true

    --// Preferred executor crypto API.
    if type(crypt) == "table" and type(crypt.hash) == "function" then
        cachedSHA256 = function(input)
            return crypt.hash(input, "sha256")
        end
    elseif type(syn) == "table"
        and type(syn.crypt) == "table"
        and type(syn.crypt.hash) == "function" then
        cachedSHA256 = function(input)
            return syn.crypt.hash(input, "sha256")
        end
    else
        --// A few executors expose hash helpers differently.
        local globals = {"sha256", "sha256hex"}

        for _, name in ipairs(globals) do
            local fn = _G[name]

            if type(fn) == "function" and fn ~= sha256 then
                cachedSHA256 = fn
                break
            end
        end
    end

    if not cachedSHA256 then
        return nil
    end

    local ok, result = pcall(cachedSHA256, value)
    if ok and type(result) == "string" and #result > 0 then
        return string.lower(result)
    end

    return nil
end

local function generateNonce()
    local alphabet = "abcdefghijklmnopqrstuvwxyz"
    local result = table.create(16)

    for i = 1, 16 do
        local index = math.random(1, #alphabet)
        result[i] = alphabet:sub(index, index)
    end

    return table.concat(result)
end

local function getIdentifier()
    --// ONLY Roblox UserId is used.
    local digest = sha256(userId)

    if not digest then
        return nil, "INTEGRITY_UNAVAILABLE"
    end

    return digest, nil
end

--// ============================================================
--// REQUEST WITH TIMEOUT
--// ============================================================

local function requestWithTimeout(options, timeout, cancelCheck)
    local requester = resolveRequestFunction()

    if type(requester) ~= "function" then
        return false, nil, "HTTP_UNAVAILABLE", 0
    end

    local started = os.clock()
    local finished = false
    local requestOK = false
    local response = nil
    local requestError = nil

    task.spawn(function()
        local ok, result = pcall(function()
            return requester(options)
        end)
        requestOK = ok
        response = result
        if not ok then
            requestError = tostring(result)
        end
        finished = true
    end)

    local deadline = started + (timeout or REQUEST_TIMEOUT)

    while not finished and os.clock() < deadline do
        if cancelCheck and cancelCheck() then
            return false, nil, "CANCELLED", math.floor((os.clock() - started) * 1000 + 0.5)
        end
        task.wait()
    end

    local elapsed = math.floor((os.clock() - started) * 1000 + 0.5)

    if not finished then
        return false, nil, "TIMEOUT", elapsed
    end
    if not requestOK then
        return false, nil, requestError or "REQUEST_FAILED", elapsed
    end
    if type(response) ~= "table" then
        return false, nil, "MALFORMED_HTTP_RESPONSE", elapsed
    end
    return true, response, nil, elapsed
end

local function shouldRetryReason(reason)
    return reason == "TIMEOUT"
        or reason == "SERVICE_ERROR"
        or reason == "NETWORK"
        or reason == "REQUEST_FAILED"
end

local function waitBackoff(attempt, cancelCheck)
    local delay = RETRY_BASE_DELAY * (2 ^ math.max(0, attempt - 1))
    local endAt = os.clock() + delay
    while os.clock() < endAt do
        if cancelCheck and cancelCheck() then
            return false
        end
        task.wait()
    end
    return true
end

--// ============================================================
--// SAVE / LOAD
--// ============================================================

local function loadSavedKey()
    if not SAVE_KEY then
        return nil
    end

    if type(readfile) ~= "function" or type(isfile) ~= "function" then
        return nil
    end

    local exists = false

    pcall(function()
        exists = isfile(SAVE_FILE)
    end)

    if not exists then
        return nil
    end

    local ok, value = pcall(function()
        return readfile(SAVE_FILE)
    end)

    if not ok or type(value) ~= "string" then
        return nil
    end

    value = trim(value)

    if value == "" then
        return nil
    end

    return value
end

local function saveKey(key)
    if not SAVE_KEY or type(writefile) ~= "function" then
        return
    end

    pcall(function()
        writefile(SAVE_FILE, key)
    end)
end

local function clearSavedKey()
    if type(delfile) ~= "function" then
        return
    end

    pcall(function()
        if type(isfile) ~= "function" or isfile(SAVE_FILE) then
            delfile(SAVE_FILE)
        end
    end)
end

local function loadLastHost()
    if not SAVE_KEY or type(readfile) ~= "function" or type(isfile) ~= "function" then
        return nil
    end
    local exists = false
    pcall(function() exists = isfile(LAST_HOST_FILE) end)
    if not exists then return nil end
    local ok, value = pcall(function() return trim(readfile(LAST_HOST_FILE)) end)
    if ok and (value == PLATOBOOST_HOSTS[1] or value == PLATOBOOST_HOSTS[2]) then
        return value
    end
    return nil
end

local function saveLastHost(host)
    if not SAVE_KEY or type(writefile) ~= "function" then return end
    if host ~= PLATOBOOST_HOSTS[1] and host ~= PLATOBOOST_HOSTS[2] then return end
    pcall(function() writefile(LAST_HOST_FILE, host) end)
end

--// ============================================================
--// STARTUP CACHE / GUI SETUP
--// ============================================================

local cachedSavedKey = nil
local cachedSavedKeyReady = false

task.spawn(function()
    cachedSavedKey = loadSavedKey()
    rememberedHost = loadLastHost()
    cachedSavedKeyReady = true
end)

destroyIfExists(CoreGui, "OPSYXKeySystem")
destroyIfExists(PlayerGui, "OPSYXKeySystem")

local GuiParent = PlayerGui

local canUseCoreGui = false

pcall(function()
    local testGui = Instance.new("ScreenGui")
    testGui.Parent = CoreGui
    testGui:Destroy()
    canUseCoreGui = true
end)

if canUseCoreGui then
    GuiParent = CoreGui
end

local ScreenGui = new("ScreenGui", {
    Name = "OPSYXKeySystem",
    IgnoreGuiInset = true,
    ResetOnSpawn = false,
    ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
    DisplayOrder = 999999,
}, GuiParent)

local Background = new("Frame", {
    Size = UDim2.fromScale(1, 1),
    BackgroundTransparency = 1,
    BorderSizePixel = 0,
}, ScreenGui)

new("UIGradient", {
    Rotation = 35,
    Color = ColorSequence.new({
        ColorSequenceKeypoint.new(0, Color3.fromRGB(7, 8, 13)),
        ColorSequenceKeypoint.new(0.5, Color3.fromRGB(22, 15, 34)),
        ColorSequenceKeypoint.new(1, Color3.fromRGB(7, 8, 12)),
    }),
}, Background)

local Panel = new("Frame", {
    AnchorPoint = Vector2.new(0.5, 0.5),
    Position = UDim2.fromScale(0.5, 0.52),
    Size = UDim2.fromOffset(460, 462),
    BackgroundColor3 = Color3.fromRGB(14, 16, 24),
    BorderSizePixel = 0,
}, ScreenGui)

new("UICorner", {
    CornerRadius = UDim.new(0, 20),
}, Panel)

new("UIStroke", {
    Color = Color3.fromRGB(88, 70, 132),
    Thickness = 1.2,
    Transparency = 0.18,
}, Panel)

local PanelScale = new("UIScale", {}, Panel)

local function updateScale()
    local camera = workspace.CurrentCamera

    if not camera then
        return
    end

    local viewport = camera.ViewportSize

    PanelScale.Scale = math.clamp(
        math.min(viewport.X / 540, viewport.Y / 535),
        0.68,
        1
    )
end

updateScale()

pcall(function()
    if workspace.CurrentCamera then
        workspace.CurrentCamera:GetPropertyChangedSignal("ViewportSize"):Connect(updateScale)
    end
end)

local Accent = new("Frame", {
    Position = UDim2.fromOffset(28, 27),
    Size = UDim2.fromOffset(5, 50),
    BackgroundColor3 = Color3.fromRGB(139, 91, 245),
    BorderSizePixel = 0,
}, Panel)

new("UICorner", {
    CornerRadius = UDim.new(1, 0),
}, Accent)

new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(48, 22),
    Size = UDim2.new(1, -185, 0, 32),
    Font = Enum.Font.GothamBold,
    Text = "OPSYX KEY SYSTEM",
    TextColor3 = Color3.fromRGB(246, 243, 255),
    TextSize = 23,
    TextXAlignment = Enum.TextXAlignment.Left,
}, Panel)

new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(50, 51),
    Size = UDim2.new(1, -210, 0, 18),
    Font = Enum.Font.Gotham,
    Text = "Platoboost account authentication",
    TextColor3 = Color3.fromRGB(139, 134, 159),
    TextSize = 11,
    TextXAlignment = Enum.TextXAlignment.Left,
}, Panel)

local UserCard = new("Frame", {
    Position = UDim2.fromOffset(28, 88),
    Size = UDim2.new(1, -56, 0, 76),
    BackgroundColor3 = Color3.fromRGB(19, 21, 30),
    BorderSizePixel = 0,
}, Panel)

new("UICorner", {
    CornerRadius = UDim.new(0, 13),
}, UserCard)

new("UIStroke", {
    Color = Color3.fromRGB(46, 48, 62),
    Thickness = 1,
}, UserCard)

local Avatar = new("ImageLabel", {
    BackgroundColor3 = Color3.fromRGB(29, 31, 43),
    BackgroundTransparency = 0,
    Position = UDim2.fromOffset(10, 10),
    Size = UDim2.fromOffset(56, 56),
    Image = "",
    ScaleType = Enum.ScaleType.Crop,
}, UserCard)

new("UICorner", {
    CornerRadius = UDim.new(0, 12),
}, Avatar)

new("UIStroke", {
    Color = Color3.fromRGB(73, 64, 99),
    Thickness = 1,
}, Avatar)

local AvatarStatus = new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(78, 11),
    Size = UDim2.new(1, -92, 0, 18),
    Font = Enum.Font.Gotham,
    Text = "Looking up avatar...",
    TextColor3 = Color3.fromRGB(139, 134, 159),
    TextSize = 10,
    TextXAlignment = Enum.TextXAlignment.Left,
}, UserCard)

new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(78, 28),
    Size = UDim2.new(1, -92, 0, 22),
    Font = Enum.Font.GothamMedium,
    Text = "Welcome, " .. username,
    TextColor3 = Color3.fromRGB(231, 228, 241),
    TextSize = 14,
    TextXAlignment = Enum.TextXAlignment.Left,
}, UserCard)

new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(78, 50),
    Size = UDim2.new(1, -170, 0, 16),
    Font = Enum.Font.Code,
    Text = "User ID: " .. userId,
    TextColor3 = Color3.fromRGB(140, 136, 159),
    TextSize = 11,
    TextXAlignment = Enum.TextXAlignment.Left,
}, UserCard)

local CopyUserIdButton = new("TextButton", {
    AutoButtonColor = false,
    BackgroundColor3 = Color3.fromRGB(27, 29, 41),
    BorderSizePixel = 0,
    Position = UDim2.new(1, -72, 1, -31),
    Size = UDim2.fromOffset(60, 22),
    Font = Enum.Font.GothamBold,
    Text = "COPY ID",
    TextColor3 = Color3.fromRGB(184, 176, 202),
    TextSize = 9,
}, UserCard)
new("UICorner", { CornerRadius = UDim.new(0, 7) }, CopyUserIdButton)

local VersionLabel = new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.new(1, -140, 0, 52),
    Size = UDim2.fromOffset(120, 14),
    Font = Enum.Font.Code,
    Text = "v" .. VERSION .. " • FAST",
    TextColor3 = Color3.fromRGB(112, 104, 132),
    TextSize = 9,
    TextXAlignment = Enum.TextXAlignment.Right,
}, Panel)

local MinimizeButton = new("TextButton", {
    AutoButtonColor = false, BackgroundColor3 = Color3.fromRGB(27,29,41), BorderSizePixel = 0,
    Position = UDim2.new(1,-52,0,16), Size = UDim2.fromOffset(26,26), Font = Enum.Font.GothamBold,
    Text = "—", TextColor3 = Color3.fromRGB(190,184,202), TextSize = 13, ZIndex = 5,
}, Panel)
new("UICorner", { CornerRadius = UDim.new(1,0) }, MinimizeButton)

local MotionButton = new("TextButton", {
    AutoButtonColor = false, BackgroundColor3 = Color3.fromRGB(27,29,41), BorderSizePixel = 0,
    Position = UDim2.new(1,-86,0,16), Size = UDim2.fromOffset(26,26), Font = Enum.Font.GothamBold,
    Text = "FX", TextColor3 = reducedMotion and Color3.fromRGB(128,122,148) or Color3.fromRGB(202,192,224),
    TextSize = 9, ZIndex = 5,
}, Panel)
new("UICorner", { CornerRadius = UDim.new(1,0) }, MotionButton)

local DragHandle = new("Frame", {
    BackgroundTransparency = 1, Position = UDim2.fromOffset(18,8), Size = UDim2.new(1,-120,0,68), ZIndex = 3,
}, Panel)

local MinimizedChip = new("TextButton", {
    AnchorPoint = Vector2.new(1,1), Position = UDim2.new(1,-18,1,-18), Size = UDim2.fromOffset(92,34),
    BackgroundColor3 = Color3.fromRGB(27,29,41), BorderSizePixel = 0, Font = Enum.Font.GothamBold,
    Text = "OPSYX • OPEN", TextColor3 = Color3.fromRGB(210,202,230), TextSize = 10, Visible = false, ZIndex = 50,
}, ScreenGui)
new("UICorner", { CornerRadius = UDim.new(0,10) }, MinimizedChip)

--// ============================================================
--// ROBLOX AVATAR LOOKUP
--// ============================================================

task.spawn(function()
    local ok, content, ready = pcall(function()
        return Players:GetUserThumbnailAsync(
            LocalPlayer.UserId,
            Enum.ThumbnailType.HeadShot,
            Enum.ThumbnailSize.Size150x150
        )
    end)

    if not ok or type(content) ~= "string" or content == "" then
        AvatarStatus.Text = "Avatar unavailable"
        return
    end

    Avatar.Image = content

    if ready == false then
        AvatarStatus.Text = "Avatar loading..."
    else
        AvatarStatus.Text = "Avatar loaded"
    end
end)

new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(30, 178),
    Size = UDim2.new(1, -60, 0, 18),
    Font = Enum.Font.GothamMedium,
    Text = "Enter your key",
    TextColor3 = Color3.fromRGB(220, 217, 232),
    TextSize = 12,
    TextXAlignment = Enum.TextXAlignment.Left,
}, Panel)

local KeyFrame = new("Frame", {
    Position = UDim2.fromOffset(28, 202),
    Size = UDim2.new(1, -56, 0, 54),
    BackgroundColor3 = Color3.fromRGB(18, 20, 29),
    BorderSizePixel = 0,
}, Panel)

new("UICorner", {
    CornerRadius = UDim.new(0, 12),
}, KeyFrame)

new("UIStroke", {
    Color = Color3.fromRGB(53, 55, 72),
    Thickness = 1,
}, KeyFrame)

local KeyBox = new("TextBox", {
    BackgroundTransparency = 1,
    ClearTextOnFocus = false,
    MultiLine = false,
    Position = UDim2.fromOffset(15, 0),
    Size = UDim2.new(1, -70, 1, 0),
    Font = Enum.Font.Code,
    PlaceholderText = "Enter Platoboost key...",
    PlaceholderColor3 = Color3.fromRGB(91, 88, 105),
    Text = "",
    TextColor3 = Color3.fromRGB(238, 235, 246),
    TextSize = 14,
    TextXAlignment = Enum.TextXAlignment.Left,
    TextYAlignment = Enum.TextYAlignment.Center,
}, KeyFrame)

local Mask = new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(15, 0),
    Size = UDim2.new(1, -70, 1, 0),
    Font = Enum.Font.Code,
    Text = "",
    TextColor3 = Color3.fromRGB(238, 235, 246),
    TextSize = 17,
    TextXAlignment = Enum.TextXAlignment.Left,
    TextYAlignment = Enum.TextYAlignment.Center,
    Visible = false,
}, KeyFrame)

local Eye = new("TextButton", {
    AutoButtonColor = false,
    BackgroundTransparency = 1,
    Position = UDim2.new(1, -54, 0, 0),
    Size = UDim2.fromOffset(54, 54),
    Font = Enum.Font.GothamBold,
    Text = "👁",
    TextColor3 = Color3.fromRGB(173, 167, 193),
    TextSize = 18,
}, KeyFrame)

local Status = new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(30, 268),
    Size = UDim2.new(1, -60, 0, 47),
    Font = Enum.Font.Gotham,
    Text = "Status: Waiting for key...",
    TextColor3 = Color3.fromRGB(166, 162, 180),
    TextSize = 12,
    TextWrapped = true,
    TextXAlignment = Enum.TextXAlignment.Left,
    TextYAlignment = Enum.TextYAlignment.Center,
}, Panel)

local StatusDot = new("Frame", {
    Position = UDim2.fromOffset(30, 320),
    Size = UDim2.fromOffset(8, 8),
    BackgroundColor3 = Color3.fromRGB(116, 110, 135),
    BorderSizePixel = 0,
}, Panel)

new("UICorner", {
    CornerRadius = UDim.new(1, 0),
}, StatusDot)

local NetworkInfo = new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(46,314),
    Size = UDim2.fromOffset(215,20),
    Font = Enum.Font.Code,
    Text = "API: preflight...",
    TextColor3 = Color3.fromRGB(108,103,125),
    TextSize = 9,
    TextXAlignment = Enum.TextXAlignment.Left,
}, Panel)

local DiagnosticsButton = new("TextButton", {
    AutoButtonColor = false, BackgroundColor3 = Color3.fromRGB(27,29,41), BorderSizePixel = 0,
    Position = UDim2.new(1,-138,0,312), Size = UDim2.fromOffset(110,24), Font = Enum.Font.GothamBold,
    Text = "COPY DETAILS", TextColor3 = Color3.fromRGB(163,155,183), TextSize = 9,
}, Panel)
new("UICorner", { CornerRadius = UDim.new(0,7) }, DiagnosticsButton)

local Verify = new("TextButton", {
    AutoButtonColor = false,
    Position = UDim2.fromOffset(28, 342),
    Size = UDim2.new(1, -56, 0, 50),
    BackgroundColor3 = Color3.fromRGB(117, 77, 225),
    BorderSizePixel = 0,
    Font = Enum.Font.GothamBold,
    Text = "VERIFY KEY",
    TextColor3 = Color3.fromRGB(255, 255, 255),
    TextSize = 13,
}, Panel)

new("UICorner", {
    CornerRadius = UDim.new(0, 12),
}, Verify)

new("UIStroke", {
    Color = Color3.fromRGB(168, 132, 255),
    Thickness = 1,
    Transparency = 0.25,
}, Verify)

local KeyRatesButton = new("TextButton", {
    AutoButtonColor = false,
    Position = UDim2.fromOffset(28, 402),
    Size = UDim2.new(1, -56, 0, 44),
    BackgroundColor3 = Color3.fromRGB(27, 29, 41),
    BorderSizePixel = 0,
    Font = Enum.Font.GothamBold,
    Text = "KEY RATES",
    TextColor3 = Color3.fromRGB(214, 206, 236),
    TextSize = 12,
}, Panel)

new("UICorner", {
    CornerRadius = UDim.new(0, 11),
}, KeyRatesButton)

new("UIStroke", {
    Color = Color3.fromRGB(75, 64, 104),
    Thickness = 1,
}, KeyRatesButton)

new("TextLabel", {
    BackgroundTransparency = 1,
    Position = UDim2.fromOffset(28, 445),
    Size = UDim2.new(1, -56, 0, 16),
    Font = Enum.Font.Gotham,
    Text = "OPSYX • UserId locked",
    TextColor3 = Color3.fromRGB(88, 84, 104),
    TextSize = 11,
    TextXAlignment = Enum.TextXAlignment.Center,
}, Panel)

--// ============================================================
--// KEY RATES PANEL (LAZY-LOADED)
--// ============================================================

local RatesOverlay = nil
local RatesClose = nil
local BuyKeyButton = nil
local openDiscord

local function ensureRatesOverlay()
    if RatesOverlay and RatesOverlay.Parent then
        RatesOverlay.Visible = true
        return
    end

    RatesOverlay = new("Frame", { AnchorPoint = Vector2.new(0.5,0.5), Position = UDim2.fromScale(0.5,0.5),
        Size = UDim2.fromOffset(410,350), BackgroundColor3 = Color3.fromRGB(12,14,21), BorderSizePixel = 0,
        Visible = true, ZIndex = 20 }, Panel)
    new("UICorner", { CornerRadius = UDim.new(0,18) }, RatesOverlay)
    new("UIStroke", { Color = Color3.fromRGB(102,78,151), Thickness = 1.2, Transparency = 0.12 }, RatesOverlay)
    new("TextLabel", { BackgroundTransparency = 1, Position = UDim2.fromOffset(22,18), Size = UDim2.new(1,-44,0,28),
        Font = Enum.Font.GothamBold, Text = "KEY RATES", TextColor3 = Color3.fromRGB(246,243,255), TextSize = 20,
        TextXAlignment = Enum.TextXAlignment.Left, ZIndex = 21 }, RatesOverlay)
    new("TextLabel", { BackgroundTransparency = 1, Position = UDim2.fromOffset(22,45), Size = UDim2.new(1,-44,0,18),
        Font = Enum.Font.Gotham, Text = "Choose a key duration", TextColor3 = Color3.fromRGB(139,134,159), TextSize = 11,
        TextXAlignment = Enum.TextXAlignment.Left, ZIndex = 21 }, RatesOverlay)

    local header = new("Frame", { Position = UDim2.fromOffset(18,73), Size = UDim2.new(1,-36,0,34),
        BackgroundColor3 = Color3.fromRGB(23,25,35), BorderSizePixel = 0, ZIndex = 21 }, RatesOverlay)
    new("UICorner", { CornerRadius = UDim.new(0,9) }, header)
    new("TextLabel", { BackgroundTransparency=1, Position=UDim2.fromOffset(14,0), Size=UDim2.new(0.5,-14,1,0),
        Font=Enum.Font.GothamBold, Text="AMOUNT", TextColor3=Color3.fromRGB(177,170,196), TextSize=10,
        TextXAlignment=Enum.TextXAlignment.Left, ZIndex=22 }, header)
    new("TextLabel", { BackgroundTransparency=1, Position=UDim2.new(0.5,0,0,0), Size=UDim2.new(0.5,-14,1,0),
        Font=Enum.Font.GothamBold, Text="TIME", TextColor3=Color3.fromRGB(177,170,196), TextSize=10,
        TextXAlignment=Enum.TextXAlignment.Right, ZIndex=22 }, header)

    local function addRateRow(y,amount,duration)
        local row = new("Frame", { Position=UDim2.fromOffset(18,y), Size=UDim2.new(1,-36,0,38),
            BackgroundColor3=Color3.fromRGB(18,20,29), BorderSizePixel=0, ZIndex=21 }, RatesOverlay)
        new("UICorner", { CornerRadius=UDim.new(0,9) }, row)
        new("UIStroke", { Color=Color3.fromRGB(45,47,61), Thickness=1 }, row)
        new("TextLabel", { BackgroundTransparency=1, Position=UDim2.fromOffset(14,0), Size=UDim2.new(0.5,-14,1,0),
            Font=Enum.Font.GothamBold, Text=amount, TextColor3=Color3.fromRGB(239,235,247), TextSize=13,
            TextXAlignment=Enum.TextXAlignment.Left, ZIndex=22 }, row)
        new("TextLabel", { BackgroundTransparency=1, Position=UDim2.new(0.5,0,0,0), Size=UDim2.new(0.5,-14,1,0),
            Font=Enum.Font.GothamMedium, Text=duration, TextColor3=Color3.fromRGB(184,176,202), TextSize=12,
            TextXAlignment=Enum.TextXAlignment.Right, ZIndex=22 }, row)
    end
    addRateRow(113,"₱ 5","2 hour")
    addRateRow(157,"₱ 10","6 hour")
    addRateRow(201,"₱ 20","1 Day")

    BuyKeyButton = new("TextButton", { AutoButtonColor=false, Position=UDim2.fromOffset(18,249), Size=UDim2.new(1,-36,0,58),
        BackgroundColor3=Color3.fromRGB(117,77,225), BorderSizePixel=0, Font=Enum.Font.GothamBold,
        Text="BUY KEY? MESSAGE ME ON DISCORD", TextColor3=Color3.fromRGB(255,255,255), TextSize=12, TextWrapped=true, ZIndex=21 }, RatesOverlay)
    new("UICorner", { CornerRadius=UDim.new(0,12) }, BuyKeyButton)
    new("UIStroke", { Color=Color3.fromRGB(168,132,255), Thickness=1, Transparency=0.25 }, BuyKeyButton)
    new("TextLabel", { BackgroundTransparency=1, Position=UDim2.fromOffset(18,312), Size=UDim2.new(1,-36,0,16),
        Font=Enum.Font.Gotham, Text="Click the box to open Discord", TextColor3=Color3.fromRGB(120,114,137), TextSize=12,
        TextXAlignment=Enum.TextXAlignment.Center, ZIndex=21 }, RatesOverlay)
    RatesClose = new("TextButton", { AutoButtonColor=false, Position=UDim2.new(1,-44,0,14), Size=UDim2.fromOffset(28,28),
        BackgroundColor3=Color3.fromRGB(27,29,41), BorderSizePixel=0, Font=Enum.Font.GothamBold, Text="×",
        TextColor3=Color3.fromRGB(178,172,191), TextSize=17, ZIndex=22 }, RatesOverlay)
    new("UICorner", { CornerRadius=UDim.new(1,0) }, RatesClose)
    RatesClose.MouseButton1Click:Connect(function() RatesOverlay.Visible=false end)
    BuyKeyButton.MouseButton1Click:Connect(function() openDiscord() end)
end

--// ============================================================
--// STATUS / TOAST
--// ============================================================

local function setDiagnostic(message)
    lastDiagnostic = tostring(message or "No diagnostic information.")
end

local function setNetworkInfo(text)
    NetworkInfo.Text = "API: " .. tostring(text)
end

local function setStatus(message, kind)
    Status.Text = "Status: " .. tostring(message)

    if kind == "success" then
        Status.TextColor3 = Color3.fromRGB(169, 222, 184)
        StatusDot.BackgroundColor3 = Color3.fromRGB(72, 189, 113)
    elseif kind == "error" then
        Status.TextColor3 = Color3.fromRGB(234, 156, 165)
        StatusDot.BackgroundColor3 = Color3.fromRGB(213, 73, 88)
    elseif kind == "loading" then
        Status.TextColor3 = Color3.fromRGB(189, 175, 221)
        StatusDot.BackgroundColor3 = Color3.fromRGB(151, 106, 245)
    else
        Status.TextColor3 = Color3.fromRGB(166, 162, 180)
        StatusDot.BackgroundColor3 = Color3.fromRGB(116, 110, 135)
    end
end

local ToastContainer = new("Frame", {
    AnchorPoint = Vector2.new(1, 1),
    Position = UDim2.new(1, -18, 1, -18),
    Size = UDim2.fromOffset(320, 220),
    BackgroundTransparency = 1,
}, ScreenGui)

new("UIListLayout", {
    FillDirection = Enum.FillDirection.Vertical,
    HorizontalAlignment = Enum.HorizontalAlignment.Right,
    VerticalAlignment = Enum.VerticalAlignment.Bottom,
    Padding = UDim.new(0, 8),
}, ToastContainer)

local function toast(titleText, messageText, good)
    local card = new("Frame", {
        Size = UDim2.fromOffset(300, 64),
        BackgroundColor3 = Color3.fromRGB(18, 20, 29),
        BorderSizePixel = 0,
    }, ToastContainer)

    new("UICorner", {
        CornerRadius = UDim.new(0, 12),
    }, card)

    new("UIStroke", {
        Color = good and Color3.fromRGB(70, 145, 96) or Color3.fromRGB(85, 77, 111),
        Thickness = 1,
    }, card)

    new("Frame", {
        Size = UDim2.fromOffset(4, 64),
        BackgroundColor3 = good and Color3.fromRGB(79, 190, 116) or Color3.fromRGB(131, 89, 235),
        BorderSizePixel = 0,
    }, card)

    new("TextLabel", {
        BackgroundTransparency = 1,
        Position = UDim2.fromOffset(16, 7),
        Size = UDim2.new(1, -25, 0, 18),
        Font = Enum.Font.GothamBold,
        Text = tostring(titleText),
        TextColor3 = Color3.fromRGB(238, 235, 245),
        TextSize = 12,
        TextXAlignment = Enum.TextXAlignment.Left,
    }, card)

    new("TextLabel", {
        BackgroundTransparency = 1,
        Position = UDim2.fromOffset(16, 27),
        Size = UDim2.new(1, -25, 0, 29),
        Font = Enum.Font.Gotham,
        Text = tostring(messageText),
        TextColor3 = Color3.fromRGB(155, 151, 171),
        TextSize = 10,
        TextWrapped = true,
        TextXAlignment = Enum.TextXAlignment.Left,
        TextYAlignment = Enum.TextYAlignment.Top,
    }, card)

    task.delay(3, function()
        if not card.Parent then
            return
        end

        if reducedMotion then
            pcall(function() card:Destroy() end)
            return
        end

        local tween = TweenService:Create(
            card,
            TweenInfo.new(0.22, Enum.EasingStyle.Quad, Enum.EasingDirection.In),
            {BackgroundTransparency = 1}
        )

        tween:Play()
        tween.Completed:Wait()

        pcall(function() card:Destroy() end)
    end)
end

--// ============================================================
--// KEY MASKING
--// ============================================================

local function updateMask()
    if keyVisible then
        Mask.Visible = false
        KeyBox.TextTransparency = 0
        return
    end

    local length = #KeyBox.Text

    Mask.Text = string.rep("•", math.min(length, 80))
    Mask.Visible = length > 0

    --// Hide actual characters only while masked.
    KeyBox.TextTransparency = length > 0 and 1 or 0
end

KeyBox:GetPropertyChangedSignal("Text"):Connect(updateMask)

Eye.MouseButton1Click:Connect(function()
    keyVisible = not keyVisible
    Eye.Text = keyVisible and "🙈" or "👁"
    updateMask()
end)

--// ============================================================
--// PLATOBOOST VERIFICATION
--// ============================================================

local function classifyMessage(message)
    message = string.lower(tostring(message or ""))

    if message:find("expire") then
        return "EXPIRED"
    end

    if message:find("revok") then
        return "REVOKED"
    end

    if message:find("identifier")
        or message:find("different")
        or message:find("another account")
        or message:find("already assigned")
        or message:find("already bound") then
        return "WRONG_USER"
    end

    if message:find("invalid")
        or message:find("incorrect")
        or message:find("not found")
        or message:find("does not exist") then
        return "INVALID"
    end

    return nil
end

local function parseJSON(body)
    if type(body) ~= "string" or body == "" then
        return nil
    end

    local ok, decoded = pcall(function()
        return HttpService:JSONDecode(body)
    end)

    if not ok or type(decoded) ~= "table" then
        return nil
    end

    return decoded
end

local function verifyIntegrity(validValue, nonce, secret, returnedHash)
    if type(returnedHash) ~= "string" or returnedHash == "" then
        return false
    end

    local expectedHash = sha256(
        tostring(validValue)
            .. "-"
            .. tostring(nonce)
            .. "-"
            .. tostring(secret)
    )

    if not expectedHash then
        return false
    end

    return string.lower(returnedHash) == string.lower(expectedHash)
end

local function verifyKeyOnHost(host, identifier, key, cancelCheck)
    local function fail(reason, retryable, latency, status)
        lastLatencyMs = latency
        lastHttpStatus = status
        setNetworkInfo(host:gsub("https://", "") .. (latency and (" • " .. tostring(latency) .. "ms") or ""))
        setDiagnostic("Host: " .. host .. "\nHTTP: " .. tostring(status or "-") .. "\nLatency: " .. tostring(latency or "-") .. " ms\nReason: " .. tostring(reason))
        return false, reason, retryable
    end

    local whitelistNonce = generateNonce()
    local whitelistURL = host .. "/public/whitelist/" .. tostring(SERVICE_ID)
        .. "?identifier=" .. urlEncode(identifier) .. "&key=" .. urlEncode(key)
        .. "&nonce=" .. urlEncode(whitelistNonce)

    local requestOK, response, requestError, elapsed = requestWithTimeout({
        Url = whitelistURL, Method = "GET", Headers = { ["Accept"] = "application/json" },
    }, HOST_TIMEOUT, cancelCheck)

    if not requestOK then
        if requestError == "CANCELLED" then return false, "CANCELLED", false end
        return fail(requestError or "NETWORK", shouldRetryReason(requestError), elapsed, nil)
    end

    local statusCode = tonumber(response.StatusCode or response.status_code)
    local responseBody = response.Body or response.body
    lastLatencyMs = elapsed
    lastHttpStatus = statusCode
    setNetworkInfo(host:gsub("https://", "") .. " • " .. tostring(elapsed) .. "ms")

    if statusCode == 429 then return fail("RATE_LIMITED", false, elapsed, statusCode) end
    if statusCode ~= 200 then
        if statusCode and statusCode >= 500 then return fail("SERVICE_ERROR", true, elapsed, statusCode) end
        return fail("HTTP_" .. tostring(statusCode or "UNKNOWN"), false, elapsed, statusCode)
    end

    local decoded = parseJSON(responseBody)
    if not decoded then return fail("MALFORMED", false, elapsed, statusCode) end

    if decoded.success == true and type(decoded.data) == "table" and decoded.data.valid == true then
        if not verifyIntegrity(true, whitelistNonce, PLATOBOOST_API_SECRET, decoded.data.hash) then
            return fail("INTEGRITY", false, elapsed, statusCode)
        end
        return true, "SUCCESS", false
    end

    local message = tostring(decoded.message or decoded.error or decoded.reason or "")
    local classification = classifyMessage(message)

    if key:sub(1,4) == "KEY_" then
        local redeemNonce = generateNonce()
        local redeemURL = host .. "/public/redeem/" .. tostring(SERVICE_ID)
        local bodyOK, encodedBody = pcall(function()
            return HttpService:JSONEncode({ identifier=identifier, key=key, nonce=redeemNonce })
        end)
        if not bodyOK or type(encodedBody) ~= "string" then return fail("MALFORMED", false, elapsed, statusCode) end
        if cancelCheck and cancelCheck() then return false, "CANCELLED", false end

        local redeemOK, redeemResponse, redeemError, redeemElapsed = requestWithTimeout({
            Url=redeemURL, Method="POST",
            Headers={ ["Accept"]="application/json", ["Content-Type"]="application/json" }, Body=encodedBody,
        }, HOST_TIMEOUT, cancelCheck)
        if not redeemOK then
            if redeemError == "CANCELLED" then return false, "CANCELLED", false end
            return fail(redeemError or "NETWORK", shouldRetryReason(redeemError), redeemElapsed, nil)
        end

        local redeemStatus = tonumber(redeemResponse.StatusCode or redeemResponse.status_code)
        local redeemBody = redeemResponse.Body or redeemResponse.body
        lastLatencyMs = redeemElapsed
        lastHttpStatus = redeemStatus
        setNetworkInfo(host:gsub("https://", "") .. " • " .. tostring(redeemElapsed) .. "ms")
        if redeemStatus == 429 then return fail("RATE_LIMITED", false, redeemElapsed, redeemStatus) end
        if redeemStatus ~= 200 then
            if redeemStatus and redeemStatus >= 500 then return fail("SERVICE_ERROR", true, redeemElapsed, redeemStatus) end
            return fail("HTTP_" .. tostring(redeemStatus or "UNKNOWN"), false, redeemElapsed, redeemStatus)
        end

        local redeemDecoded = parseJSON(redeemBody)
        if not redeemDecoded then return fail("MALFORMED", false, redeemElapsed, redeemStatus) end
        if redeemDecoded.success == true and type(redeemDecoded.data) == "table" and redeemDecoded.data.valid == true then
            if not verifyIntegrity(true, redeemNonce, PLATOBOOST_API_SECRET, redeemDecoded.data.hash) then
                return fail("INTEGRITY", false, redeemElapsed, redeemStatus)
            end
            return true, "SUCCESS", false
        end
        local redeemMessage = tostring(redeemDecoded.message or redeemDecoded.error or redeemDecoded.reason or "")
        return false, classifyMessage(redeemMessage) or "INVALID", false
    end

    return false, classification or "INVALID", false
end

local function validateKeyInput(key)
    key = trim(key)
    if key == "" then return false, "EMPTY", key end
    if #key > MAX_KEY_LENGTH then return false, "TOO_LONG", key end
    if key:find("[%c]", 1) then return false, "INVALID_FORMAT", key end
    return true, nil, key
end

local function verifyPlatoboost(key, token)
    local valid, validationReason, normalizedKey = validateKeyInput(key)
    if not valid then return false, validationReason end

    key = normalizedKey
    local identifier, identifierError = getIdentifier()
    if not identifier then return false, identifierError end

    local hosts = {}
    if rememberedHost == PLATOBOOST_HOSTS[1] or rememberedHost == PLATOBOOST_HOSTS[2] then
        table.insert(hosts, rememberedHost)
    end
    for _, host in ipairs(PLATOBOOST_HOSTS) do
        if #hosts == 0 or host ~= hosts[1] then table.insert(hosts, host) end
    end

    local lastReason = "NETWORK"
    local sawNetworkFailure = false
    local serviceErrors = 0

    for _, host in ipairs(hosts) do
        local function cancelled() return not alive or token ~= verificationToken end
        local attempts = 0
        local success, reason, retryable
        repeat
            attempts += 1
            success, reason, retryable = verifyKeyOnHost(host, identifier, key, cancelled)
            if success then
                activeHost = host
                rememberedHost = host
                saveLastHost(host)
                maintenanceDetected = false
                setDiagnostic("Host: " .. host .. "\nHTTP: 200\nLatency: " .. tostring(lastLatencyMs or "-") .. " ms\nResult: SUCCESS")
                return true, "SUCCESS"
            end
            if reason == "CANCELLED" then return false, "CANCELLED" end
            lastReason = reason
            sawNetworkFailure = sawNetworkFailure or shouldRetryReason(reason)
            if reason == "SERVICE_ERROR" then serviceErrors += 1 end
            if not retryable or attempts >= MAX_RETRIES then break end
            if not waitBackoff(attempts, cancelled) then return false, "CANCELLED" end
        until success

        if reason ~= "NETWORK" and reason ~= "TIMEOUT" and reason ~= "HTTP_403"
            and reason ~= "SERVICE_ERROR" and reason ~= "REQUEST_FAILED" then
            activeHost = host
            return false, reason
        end
    end

    maintenanceDetected = serviceErrors >= #hosts and #hosts > 0
    if maintenanceDetected then return false, "MAINTENANCE" end
    if sawNetworkFailure then return false, lastReason end
    return false, lastReason
end

--// ============================================================
--// OPSYX LAUNCH CONTEXT - RELIABLE HANDOFF V2

--// A short-lived, one-use handoff is created only AFTER the first
--// Platoboost verification succeeds. The raw OPSYX script must consume
--// this context before it is allowed to initialize.
--// ============================================================
local LAUNCH_CONTEXT_NAME = "__OPSYX_KEY_LAUNCH_CONTEXT_V1"
local LAUNCH_CONTEXT_TTL = 45

local function createLaunchContext(key)
    local issuedAt = os.time()
    local expiresAt = issuedAt + LAUNCH_CONTEXT_TTL
    local nonce = generateNonce()
    local proof = sha256(
        userId .. "|" .. nonce .. "|" .. tostring(expiresAt) .. "|" .. key
    )

    if not proof then
        return nil, "INTEGRITY_UNAVAILABLE"
    end

    return {
        version   = 1,
        userId    = userId,
        key       = key,
        nonce     = nonce,
        issuedAt  = issuedAt,
        expiresAt = expiresAt,
        proof     = proof,
        used      = false,
    }
end

local function clearLaunchContext()
    pcall(function()
        if type(_G) == "table" then
            _G[LAUNCH_CONTEXT_NAME] = nil
        end
    end)
end

--// ============================================================
--// RAW OPSYX1 EXECUTION
--// ============================================================

local function executeOPSYXOnce()
    --// Absolute once-only execution guard.
    if hasExecuted then
        return false, "ALREADY_EXECUTED"
    end

    if not authenticated then
        return false, "NOT_AUTHENTICATED"
    end

    if not alive or not LocalPlayer.Parent then
        return false, "PLAYER_LEFT"
    end

    setStatus(
        "Key verified successfully.\nLaunching OPSYX...",
        "success"
    )

    toast(
        "Key verified",
        "Launching OPSYX...",
        true
    )

    local success, err = pcall(function()
        --// Prefer the same executor HTTP requester that already passed
        --// the Platoboost check. Fall back to game:HttpGet for clients
        --// where the executor requester cannot fetch raw GitHub content.
        local source = nil
        local requester = resolveRequestFunction()

        if type(requester) == "function" then
            local requestOK, response = pcall(function()
                return requester({
                    Url = RAW_URL,
                    Method = "GET",
                    Headers = { ["Accept"] = "text/plain" },
                })
            end)

            if requestOK and type(response) == "table" then
                local statusCode = tonumber(response.StatusCode or response.status_code)
                local body = response.Body or response.body
                if (not statusCode or statusCode == 200) and type(body) == "string" then
                    source = body
                elseif statusCode and statusCode ~= 200 then
                    warnOPSYX("Raw download via executor HTTP returned HTTP " .. tostring(statusCode))
                end
            end
        end

        if type(source) ~= "string" or source == "" then
            local httpOK, httpResult = pcall(function()
                return game:HttpGet(RAW_URL)
            end)

            if not httpOK then
                error("Raw script download failed: " .. tostring(httpResult))
            end

            source = httpResult
        end

        if type(source) ~= "string" or source == "" then
            error("Raw script returned an empty response.")
        end

        if type(loadstring) ~= "function" then
            error("loadstring is unavailable in this executor.")
        end

        local chunk, compileError = loadstring(source)

        if type(chunk) ~= "function" then
            error("Raw script compilation failed: " .. tostring(compileError))
        end

        --// Execute exactly once. The raw script consumes the one-use
        --// launch context before its normal initialization begins.
        chunk()
    end)

    if not success then
        setStatus(
            "Authentication succeeded, but OPSYX failed to launch.\n" .. tostring(err),
            "error"
        )

        toast(
            "Launch failed",
            tostring(err),
            false
        )

        warnOPSYX("Launch error: " .. tostring(err))
        return false, tostring(err)
    end

    --// Only mark executed after the chunk completed without raising.
    --// This allows a clean retry after a transient fetch/compile failure.
    hasExecuted = true

    setStatus("OPSYX launched successfully.", "success")

    toast(
        "OPSYX launched",
        "Authentication and execution completed.",
        true
    )

    task.delay(0.8, function()
        pcall(function()
            ScreenGui:Destroy()
        end)
    end)

    return true
end

--// ============================================================
--// AUTHENTICATION
--// ============================================================

local function copyText(textValue)
    local copied = false
    pcall(function()
        if type(setclipboard) == "function" then setclipboard(textValue); copied = true
        elseif type(toclipboard) == "function" then toclipboard(textValue); copied = true end
    end)
    return copied
end

local function runPreflight()
    local requester = resolveRequestFunction()
    local digest = sha256(userId)
    if type(requester) ~= "function" then
        setNetworkInfo("HTTP unavailable")
        setDiagnostic("Preflight failed: no supported HTTP request function.")
        return false
    end
    if not digest then
        setNetworkInfo("SHA-256 unavailable")
        setDiagnostic("Preflight failed: no supported SHA-256 implementation.")
        return false
    end
    setNetworkInfo(rememberedHost and ("ready • " .. rememberedHost:gsub("https://", "")) or "ready")
    setDiagnostic("Preflight ready. HTTP + SHA-256 available.\nPreferred host: " .. tostring(rememberedHost or PLATOBOOST_HOSTS[1]))
    return true
end

local function authenticate(key)
    if verifying then
        toast(
            "Verification busy",
            "A verification request is already running.",
            false
        )

        return
    end

    if not alive or not LocalPlayer.Parent then
        return
    end

    local keyOK, keyReason, normalizedKey = validateKeyInput(key)
    key = normalizedKey

    if not keyOK then
        if keyReason == "TOO_LONG" then
            setStatus("Key is too long.", "error")
            toast("Invalid key", "The key exceeds the maximum allowed length.", false)
        elseif keyReason == "INVALID_FORMAT" then
            setStatus("Key contains invalid characters.", "error")
            toast("Invalid key", "Remove control characters and try again.", false)
        else
            setStatus("Please enter your key.", "error")
            toast("Missing key", "Enter a Platoboost key first.", false)
        end
        return
    end

    if hasExecuted then
        return
    end

    verifying = true
    authenticated = false
    verificationToken += 1

    local token = verificationToken

    Verify.Text = "VERIFYING..."
    KeyBox.TextEditable = false
    Eye.Active = false

    setStatus("Verifying key...", "loading")

    task.spawn(function()
        local success, reason = verifyPlatoboost(key, token)

        if token ~= verificationToken or not alive then
            return
        end

        verifying = false
        KeyBox.TextEditable = true
        Eye.Active = true
        Verify.Text = "VERIFY KEY"

        if not success then
            authenticated = false

            if reason == "WRONG_USER" then
                setStatus(
                    "Access denied.\nThis key is assigned to another Roblox account.",
                    "error"
                )

                toast(
                    "Access denied",
                    "This key is assigned to another Roblox account.",
                    false
                )

            elseif reason == "INVALID" or reason == "REVOKED" then
                setStatus("Invalid or revoked key.", "error")

                toast(
                    "Invalid key",
                    "This key is invalid or has been revoked.",
                    false
                )

                clearSavedKey()

            elseif reason == "EXPIRED" then
                setStatus("This key has expired.", "error")

                toast(
                    "Expired key",
                    "Your Platoboost key has expired.",
                    false
                )

                clearSavedKey()

            elseif reason == "MAINTENANCE" or maintenanceDetected then
                setStatus("Verification service may be under maintenance.", "error")
                toast("Service unavailable", "Both verification hosts are currently returning server errors.", false)

            elseif reason == "HTTP_403" then
                setStatus(
                    "Unable to verify key.\nPlatoboost returned HTTP 403.",
                    "error"
                )

                toast(
                    "Platoboost access denied",
                    "Both current Platoboost API hosts rejected the request.",
                    false
                )

            elseif reason == "SERVICE_ERROR" then
                setStatus(
                    "Unable to verify key.\nPlatoboost service error.",
                    "error"
                )

                toast(
                    "Platoboost error",
                    "The Platoboost service returned a server error.",
                    false
                )

            elseif reason == "RATE_LIMITED" then
                setStatus(
                    "Unable to verify key.\nPlatoboost rate limit reached.",
                    "error"
                )

                toast(
                    "Rate limited",
                    "Please wait and try again.",
                    false
                )

            elseif reason == "TIMEOUT" then
                setStatus(
                    "Unable to verify key.\nRequest timed out.",
                    "error"
                )

                toast(
                    "Verification timeout",
                    "Platoboost did not respond in time.",
                    false
                )

            elseif reason == "HTTP_UNAVAILABLE" then
                setStatus(
                    "Unable to verify key.\nNo supported HTTP function found.",
                    "error"
                )

                toast(
                    "HTTP unavailable",
                    "Your executor does not expose a supported request function.",
                    false
                )

            elseif reason == "INTEGRITY_UNAVAILABLE" then
                setStatus(
                    "Unable to verify key.\nSHA-256 is unavailable.",
                    "error"
                )

                toast(
                    "Integrity unavailable",
                    "Your executor does not expose SHA-256 hashing.",
                    false
                )

            elseif reason == "INTEGRITY" then
                setStatus(
                    "Unable to verify key.\nIntegrity validation failed.",
                    "error"
                )

                toast(
                    "Integrity failed",
                    "Platoboost response integrity could not be verified.",
                    false
                )

            elseif reason == "MALFORMED" then
                setStatus(
                    "Unable to verify key.\nInvalid Platoboost response.",
                    "error"
                )

                toast(
                    "Malformed response",
                    "Platoboost returned unexpected data.",
                    false
                )

            elseif type(reason) == "string" and reason:sub(1, 5) == "HTTP_" then
                setStatus(
                    "Unable to verify key.\nServer returned " .. reason:sub(6) .. ".",
                    "error"
                )

                toast(
                    "Platoboost HTTP error",
                    "Server returned HTTP " .. reason:sub(6) .. ".",
                    false
                )

            else
                setStatus(
                    "Unable to verify key.\nPlease try again.",
                    "error"
                )

                toast(
                    "Verification failed",
                    "Platoboost verification could not be completed.",
                    false
                )
            end

            warnOPSYX("Verification error: " .. tostring(reason) .. " | " .. tostring(lastDiagnostic))
            return
        end

        --// ========================================================
        --// AUTHENTICATION SUCCESS
        --// No raw URL request occurs before this point.
        --// ========================================================

        authenticated = true

        saveKey(key)

        if not authenticated or hasExecuted then
            return
        end

        local launchContext, contextError = createLaunchContext(key)
        if not launchContext then
            authenticated = false
            setStatus(
                "Key verified, but secure launch context could not be created.",
                "error"
            )
            toast(
                "Secure launch failed",
                tostring(contextError or "INTEGRITY_UNAVAILABLE"),
                false
            )
            clearLaunchContext()
            return
        end

        --// Fresh context replaces any stale context left by an interrupted launch.
        pcall(function()
            _G[LAUNCH_CONTEXT_NAME] = launchContext
        end)

        local launchOK, launchError = executeOPSYXOnce()
        if not launchOK then
            --// The raw script owns the one-use context. Clear any leftover
            --// handoff here as a safety net after a launcher-side failure.
            clearLaunchContext()
            authenticated = false
            hasExecuted = false
            Verify.Text = "VERIFY KEY"
            KeyBox.TextEditable = true
            Eye.Active = true
            warnOPSYX("Secure launch failed: " .. tostring(launchError))
        end
    end)
end

--// ============================================================
--// KEY RATES / DISCORD EVENTS
--// ============================================================

openDiscord = function()
    local opened = false

    pcall(function()
        if type(GuiService.OpenBrowserWindow) == "function" then
            GuiService:OpenBrowserWindow(DISCORD_URL)
            opened = true
        end
    end)

    if opened then
        toast(
            "Discord",
            "Opening the Discord contact page...",
            true
        )
        return
    end

    local copied = false

    pcall(function()
        if type(setclipboard) == "function" then
            setclipboard(DISCORD_URL)
            copied = true
        elseif type(toclipboard) == "function" then
            toclipboard(DISCORD_URL)
            copied = true
        end
    end)

    if copied then
        toast(
            "Discord link copied",
            "Open Discord and paste the copied contact link.",
            true
        )
    else
        toast(
            "Discord link",
            DISCORD_URL,
            false
        )
    end
end

KeyRatesButton.MouseButton1Click:Connect(function()
    ensureRatesOverlay()
end)

CopyUserIdButton.MouseButton1Click:Connect(function()
    if copyText(userId) then
        toast("Copied", "Roblox User ID copied to clipboard.", true)
    else
        toast("Clipboard unavailable", "Copying is not supported in this environment.", false)
    end
end)

DiagnosticsButton.MouseButton1Click:Connect(function()
    local details = table.concat({
        "OPSYX Key System v" .. VERSION,
        "Host: " .. tostring(activeHost or rememberedHost or "none"),
        "HTTP: " .. tostring(lastHttpStatus or "-"),
        "Latency: " .. tostring(lastLatencyMs or "-") .. " ms",
        "Details: " .. tostring(lastDiagnostic),
    }, "\n")
    if copyText(details) then
        toast("Diagnostics copied", "Verification details copied to clipboard.", true)
    else
        warnOPSYX(details)
        toast("Clipboard unavailable", "Unable to copy diagnostics; details were logged.", false)
    end
end)

MinimizeButton.MouseButton1Click:Connect(function()
    Panel.Visible = false
    MinimizedChip.Visible = true
end)
MinimizedChip.MouseButton1Click:Connect(function()
    Panel.Visible = true
    MinimizedChip.Visible = false
end)
MotionButton.MouseButton1Click:Connect(function()
    reducedMotion = not reducedMotion
    MotionButton.TextColor3 = reducedMotion and Color3.fromRGB(128,122,148) or Color3.fromRGB(202,192,224)
    toast("Motion mode", reducedMotion and "Reduced motion enabled." or "Animations enabled.", true)
end)

--// ============================================================
--// DRAGGABLE PANEL
--// ============================================================

local dragStart = nil
local startPosition = nil
local dragInput = nil

local function updateDrag(input)
    if not dragging or not dragStart or not startPosition then return end
    local delta = input.Position - dragStart
    Panel.Position = UDim2.new(startPosition.X.Scale, startPosition.X.Offset + delta.X, startPosition.Y.Scale, startPosition.Y.Offset + delta.Y)
end

DragHandle.InputBegan:Connect(function(input)
    if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
        dragging = true
        dragStart = input.Position
        startPosition = Panel.Position
        dragInput = input
    end
end)
DragHandle.InputChanged:Connect(function(input)
    if input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch then
        dragInput = input
    end
end)
UserInputService.InputChanged:Connect(function(input)
    if input == dragInput then updateDrag(input) end
end)
UserInputService.InputEnded:Connect(function(input)
    if input == dragInput or input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
        dragging = false
        dragInput = nil
    end
end)

--// ============================================================
--// UI EVENTS
--// ============================================================

Verify.MouseButton1Click:Connect(function()
    authenticate(KeyBox.Text)
end)

KeyBox.FocusLost:Connect(function(enterPressed)
    if enterPressed and not verifying then authenticate(KeyBox.Text) end
end)

--// ============================================================
--// PLAYER LEAVE PROTECTION
--// ============================================================

Players.PlayerRemoving:Connect(function(player)
    if player == LocalPlayer then
        alive = false
        authenticated = false
        verificationToken += 1
        clearLaunchContext()

        pcall(function()
            ScreenGui:Destroy()
        end)
    end
end)

--// ============================================================
--// STARTUP ANIMATION / PREFLIGHT
--// ============================================================

if reducedMotion then
    Panel.Position = UDim2.fromScale(0.5,0.52)
    Panel.BackgroundTransparency = 0
else
    Panel.Position = UDim2.fromScale(0.5,0.57)
    Panel.BackgroundTransparency = 0.2
    TweenService:Create(Panel, TweenInfo.new(0.42, Enum.EasingStyle.Quint, Enum.EasingDirection.Out), {
        Position = UDim2.fromScale(0.5,0.52), BackgroundTransparency = 0,
    }):Play()
end

task.spawn(runPreflight)

--// ============================================================
--// INITIALIZE SAVED KEY
--// ============================================================

task.spawn(function()
    local savedKey = cachedSavedKey
    if not cachedSavedKeyReady then
        local deadline = os.clock() + 0.5
        while not cachedSavedKeyReady and os.clock() < deadline do task.wait() end
        savedKey = cachedSavedKey
    end
    if not savedKey or not alive then return end

    KeyBox.Text = savedKey
    updateMask()
    setStatus("Checking saved key...", "loading")
    toast("Saved key detected", "Re-validating your saved key...", true)
    authenticate(savedKey)
end)
