-- ForeverPlayerStatistics
-- Collects player statistics from /who searches (and from players you target or
-- mouse over) into an account-wide database and shows an overview of classes,
-- races, factions and levels.

local ADDON = "ForeverPlayerStatistics"

local defaults = {
    enabled = true,        -- false: the addon records nothing and sends no /who (statistics can still be viewed)
    whoEnabled = true,     -- false: no /who scan at all; targets / mouseover are still recorded
    minimapAngle = 235,    -- degrees around the minimap
    recordOwnWho = true,   -- also store the results of /who searches you type yourself
    recordUnits = true,    -- store players you target or mouse over
    whoCooldown = 5,       -- seconds between two /who queries of a scan
    deepSearch = false,    -- each level query also gets a random name letter (n-"k") to find other players
    autoScan = true,       -- scan keeps running until Stop is pressed
    scanPass = 0,          -- number of scan passes started
    scanQueue = {},        -- queries still to ask in the current pass (kept over /reload)
    filterFaction = "ALL", -- overview filter: ALL / Alliance / Horde
    filterRealm = false,   -- overview: only players of the current realm
    sortByName = false,    -- overview: class / race lists sorted by name instead of by count
    players = {},          -- ["Name-Realm"] = record, see StorePlayer (only while the game runs, see SavePlayers)
}

local MAX_WHO_RESULTS = 50 -- the server never returns more players than this for one query
local WHO_TIMEOUT = 10     -- seconds to wait for an answer before the query is queued again
local LEVEL_STEP = 10      -- size of the level brackets shown in the overview

local FACTION_COLORS = {
    Alliance = { 0.25, 0.5, 1 },
    Horde = { 0.9, 0.2, 0.2 },
}

local db
local panel, bar
-- queue and leaves are replaced by the saved tables when the addon loads
-- /who search paused for this session only (not saved: on again after logout / reload)
local whoPaused = false

local scan = { queue = {}, lastSend = 0, active = false, sent = 0, found = {}, foundCount = 0, new = 0, incomplete = 0 }

local RefreshPanel, UpdateScanUI

---------------------------------------------------------------------------
-- Helpers
---------------------------------------------------------------------------

local function Print(msg)
    DEFAULT_CHAT_FRAME:AddMessage("|cff33ff99" .. ADDON .. "|r: " .. msg)
end

local function OnOff(v)
    return v and "|cff00ff00ON|r" or "|cffff0000OFF|r"
end

local function SetShown(frame, shown)
    frame:SetShown(shown and true or false)
end

local function SetColor(tex, r, g, b, a)
    tex:SetColorTexture(r, g, b, a or 1)
end

local function CopyDefaults(src, dst)
    for k, v in pairs(src) do
        if type(v) == "table" then
            if type(dst[k]) ~= "table" then dst[k] = {} end
            CopyDefaults(v, dst[k])
        elseif dst[k] == nil then
            dst[k] = v
        end
    end
end

local function After(delay, fn)
    if C_Timer and C_Timer.After then C_Timer.After(delay, fn) else fn() end
end

local function Num(n)
    return BreakUpLargeNumbers and BreakUpLargeNumbers(n) or tostring(n)
end

local function Pct(n, total)
    if not total or total == 0 then return "0.0%" end
    return string.format("%.1f%%", 100 * n / total)
end

-- Name of the WoW Forever super server, exactly as the game shows it (e.g. "CAMWOWEU5Realm5PvE")
local function MyRealm()
    return (GetRealmName and GetRealmName()) or (GetNormalizedRealmName and GetNormalizedRealmName()) or "?"
end

-- Same name without spaces and dashes, the way older versions stored it
local function NormalizedRealm(realm)
    return realm and (realm:gsub("[%s%-]", "")) or nil
end

-- /who name -> name, server. WoW Forever names are "First Last" and /who only
-- lists players of your own super server.
local function SplitName(full)
    if not full or full == "" then return end
    return full, MyRealm()
end

local function MaxLevel()
    local m = (GetMaxLevelForPlayerExpansion and GetMaxLevelForPlayerExpansion())
        or (GetMaxPlayerLevel and GetMaxPlayerLevel())
    return tonumber(m) or 60
end

local IsComplete -- defined below, after the class and race lookups

-- players in the database, without records that have something unknown
local function PlayerCount()
    local n = 0
    for _, p in pairs(db.players) do
        if IsComplete(p) then n = n + 1 end
    end
    return n
end

---------------------------------------------------------------------------
-- Classes and races (localized names <-> file names)
---------------------------------------------------------------------------

local FALLBACK_CLASSES = { "WARRIOR", "PALADIN", "HUNTER", "ROGUE", "PRIEST", "SHAMAN", "MAGE", "WARLOCK", "DRUID" }
local classes = {}     -- { file = "MAGE", name = "Mage" } in game order
local classByName = {} -- lower-case localized name -> class file

local function BuildClassLookup()
    wipe(classes)
    local seen = {}
    local function add(file, name)
        if not file or seen[file] then return end
        seen[file] = true
        name = name or (LOCALIZED_CLASS_NAMES_MALE and LOCALIZED_CLASS_NAMES_MALE[file]) or file
        classes[#classes + 1] = { file = file, name = name }
        classByName[name:lower()] = file
        local female = LOCALIZED_CLASS_NAMES_FEMALE and LOCALIZED_CLASS_NAMES_FEMALE[file]
        if female then classByName[female:lower()] = file end
    end
    if GetNumClasses and GetClassInfo then
        for i = 1, GetNumClasses() do
            local ok, name, file = pcall(GetClassInfo, i)
            if ok then add(file, name) end
        end
    end
    if #classes == 0 then
        for _, file in ipairs(FALLBACK_CLASSES) do add(file) end
    end
end

-- English class names, the same for every client language
local CLASS_NAMES_EN = {
    WARRIOR = "Warrior", PALADIN = "Paladin", HUNTER = "Hunter", ROGUE = "Rogue", PRIEST = "Priest",
    SHAMAN = "Shaman", MAGE = "Mage", WARLOCK = "Warlock", DRUID = "Druid", DEATHKNIGHT = "Death Knight",
    MONK = "Monk", DEMONHUNTER = "Demon Hunter", EVOKER = "Evoker",
}

local function ClassName(file)
    if not file then return "Unknown" end
    return CLASS_NAMES_EN[file] or (file:sub(1, 1) .. file:sub(2):lower())
end

local RACE_FACTION = {
    Human = "Alliance", Dwarf = "Alliance", NightElf = "Alliance", Gnome = "Alliance",
    Draenei = "Alliance", Worgen = "Alliance",
    Orc = "Horde", Scourge = "Horde", Tauren = "Horde", Troll = "Horde",
    BloodElf = "Horde", Goblin = "Horde",
}
local RACE_NAMES = {
    Human = "Human", Dwarf = "Dwarf", NightElf = "Night Elf", Gnome = "Gnome",
    Draenei = "Draenei", Worgen = "Worgen",
    Orc = "Orc", Scourge = "Undead", Tauren = "Tauren", Troll = "Troll",
    BloodElf = "Blood Elf", Goblin = "Goblin",
    Skyborne = "Skyborne", -- WoW Forever race on both factions (Alliance: High Order, Horde: Windshapers)
}
local BASE_RACES = {
    Alliance = { "Human", "Dwarf", "NightElf", "Gnome" },
    Horde = { "Orc", "Scourge", "Tauren", "Troll" },
}
local raceByName = {} -- lower-case localized name -> race file

local function BuildRaceLookup()
    for file, name in pairs(RACE_NAMES) do raceByName[name:lower()] = file end
    -- German client names, male and female forms
    local de = {
        mensch = "Human", zwerg = "Dwarf", zwergin = "Dwarf", nachtelf = "NightElf", nachtelfe = "NightElf",
        gnom = "Gnome", gnomin = "Gnome", orc = "Orc", ork = "Orc", orcin = "Orc", untoter = "Scourge",
        untote = "Scourge", tauren = "Tauren", troll = "Troll", trollin = "Troll", blutelf = "BloodElf",
        blutelfe = "BloodElf", goblin = "Goblin", draenei = "Draenei", worgen = "Worgen",
    }
    for name, file in pairs(de) do raceByName[name] = file end

    -- whatever the client itself knows (localized names of the current language)
    if C_CreatureInfo and C_CreatureInfo.GetRaceInfo then
        for id = 1, 100 do
            local ok, info = pcall(C_CreatureInfo.GetRaceInfo, id)
            if ok and info and info.raceName and info.clientFileString then
                local file = info.clientFileString
                raceByName[info.raceName:lower()] = file
                -- names stay English: a race without English name gets its file name ("NightElf" -> "Night Elf")
                if not RACE_NAMES[file] then RACE_NAMES[file] = (file:gsub("(%l)(%u)", "%1 %2")) end
                -- Skyborne exists on both factions: its faction comes from the player, not the race
                if not RACE_FACTION[file] and file ~= "Skyborne" and C_CreatureInfo.GetFactionInfo then
                    local ok2, f = pcall(C_CreatureInfo.GetFactionInfo, id)
                    if ok2 and f and (f.groupTag == "Alliance" or f.groupTag == "Horde") then
                        RACE_FACTION[file] = f.groupTag
                    end
                end
            end
        end
    end
end

-- Localized race name from /who -> race file name ("Night Elf" -> "NightElf").
-- Unknown names are kept as they are.
-- Names with a faction suffix, e.g. "Himmelsgeborener der Windformer" (Skyborne of the Horde)
local RACE_PATTERNS = {
    { "himmelsgebor", "Skyborne" },
    { "skyborn", "Skyborne" },
}

local function ResolveRace(raceStr)
    if not raceStr or raceStr == "" then return nil end
    local lower = raceStr:lower()
    local file = raceByName[lower]
    if not file then
        for _, pat in ipairs(RACE_PATTERNS) do
            if lower:find(pat[1], 1, true) then file = pat[2]; break end
        end
    end
    return file or raceStr
end

-- English race name for display ("Scourge" -> "Undead")
local function RaceName(file)
    return RACE_NAMES[file] or file or "Unknown"
end

---------------------------------------------------------------------------
-- Zones and server type (always stored in English)
---------------------------------------------------------------------------

-- German zone names -> English. The game has no API for English names, so this
-- list covers zones, capitals, dungeons, battlegrounds and well-known places.
-- Names that are not in the list are stored as the server sends them.
local ZONE_EN = {
    -- zones
    ["Brachland"] = "The Barrens", ["Südliches Brachland"] = "Southern Barrens", ["Nördliches Brachland"] = "Northern Barrens",
    ["Tirisfal"] = "Tirisfal Glades", ["Tirisfal-Lichtung"] = "Tirisfal Glades", ["Silberwald"] = "Silverpine Forest",
    ["Vorgebirge von Hillsbrad"] = "Hillsbrad Foothills", ["Schlingendorntal"] = "Stranglethorn Vale",
    ["Arathihochland"] = "Arathi Highlands", ["Tausend Nadeln"] = "Thousand Needles", ["Sumpfland"] = "Wetlands",
    ["Steinkrallengebirge"] = "Stonetalon Mountains", ["Marschen von Dustwallow"] = "Dustwallow Marsh",
    ["Hinterland"] = "The Hinterlands", ["Ödland"] = "Badlands", ["Sümpfe des Elends"] = "Swamp of Sorrows",
    ["Dämmerwald"] = "Duskwood", ["Alteracgebirge"] = "Alterac Mountains", ["Brennende Steppe"] = "Burning Steppes",
    ["Westliche Pestländer"] = "Western Plaguelands", ["Östliche Pestländer"] = "Eastern Plaguelands",
    ["Winterquell"] = "Winterspring", ["Un'Goro-Krater"] = "Un'Goro Crater", ["Teufelswald"] = "Felwood",
    ["Rotkammgebirge"] = "Redridge Mountains", ["Verwüstete Lande"] = "Blasted Lands", ["Sengende Schlucht"] = "Searing Gorge",
    ["Wald von Elwynn"] = "Elwynn Forest", ["Mondlichtung"] = "Moonglade", ["Eschental"] = "Ashenvale",
    ["Dunkelküste"] = "Darkshore", ["Die Echoinseln"] = "Echo Isles", ["Darkspear-Inseln"] = "Echo Isles",
    -- capitals and towns
    ["Unterstadt"] = "Undercity", ["Donnerfels"] = "Thunder Bluff", ["Eisenschmiede"] = "Ironforge",
    ["Sturmwind"] = "Stormwind City", ["Tore von Ironforge"] = "Gates of Ironforge",
    ["Das Tal der Prüfungen"] = "Valley of Trials", ["Klingenhügel"] = "Razor Hill",
    ["Kaserne von Klingenhügel"] = "Razor Hill Barracks", ["Tarrens Mühle"] = "Tarren Mill",
    ["Sen'jin"] = "Sen'jin Village", ["Dorf der Bluthufe"] = "Bloodhoof Village", ["Das Grabmal"] = "The Sepulcher",
    ["Das Basislager von Grom'gol"] = "Grom'gol Base Camp", ["Sonnenfels"] = "Sun Rock Retreat",
    ["Freiwindposten"] = "Freewind Post", ["Pyrewood"] = "Pyrewood Village", ["Brackenwall"] = "Brackenwall Village",
    ["Shadowprey"] = "Shadowprey Village", ["Burg Tiragarde"] = "Tiragarde Keep", ["Burg Durnholde"] = "Durnholde Keep",
    ["Burg Stromgarde"] = "Stromgarde Keep", ["Burg Fenris"] = "Fenris Keep", ["Insel Fenris"] = "Fenris Isle",
    ["Die Feste Northwatch"] = "Northwatch Hold", ["Rathaus von Brill"] = "Brill Town Hall",
    -- dungeons, raids, battlegrounds
    ["Ragefireabgrund"] = "Ragefire Chasm", ["Die Höhlen des Wehklagens"] = "Wailing Caverns",
    ["Das Scharlachrote Kloster"] = "Scarlet Monastery", ["Burg Shadowfang"] = "Shadowfang Keep",
    ["Blackfathom-Tiefe"] = "Blackfathom Deeps", ["Der Kral von Razorfen"] = "Razorfen Kraul",
    ["Die Hügel von Razorfen"] = "Razorfen Downs", ["Die Todesminen"] = "The Deadmines", ["Das Verlies"] = "The Stockade",
    ["Der Tempel von Atal'Hakkar"] = "The Temple of Atal'Hakkar", ["Blackrocktiefen"] = "Blackrock Depths",
    ["Warsongschlucht"] = "Warsong Gulch", ["Arathibecken"] = "Arathi Basin",
    -- other places
    ["Die Händlerküste"] = "The Merchant Coast", ["Die Schimmernde Ebene"] = "The Shimmering Flats",
    ["Kolkarklippe"] = "Kolkar Crag", ["Ruinen von Lordaeron"] = "Ruins of Lordaeron",
    ["Die Ruinen von Lordaeron"] = "Ruins of Lordaeron", ["Goldstraße"] = "The Gold Road",
    ["Südliche Goldstraße"] = "Southern Gold Road", ["Agamands Mühlen"] = "Agamand Mills",
    ["Die Felder von Hillsbrad"] = "Hillsbrad Fields", ["Nachtwebergrund"] = "Nightweb's Hollow",
    ["Die Trockenen Hügel"] = "The Dry Hills", ["Taverne Zur Galgenschlinge"] = "Gallows' End Tavern",
    ["Die Blühende Oase"] = "Lushwater Oasis", ["Die Vergessenen Teiche"] = "The Forgotten Pools",
    ["Der Steinkrallengipfel"] = "Stonetalon Peak", ["Feld der Riesen"] = "Field of Giants",
    ["Die Brackige Oase"] = "The Stagnant Oasis", ["Die Anhöhe der Ältesten"] = "Elder Rise",
    ["Die Anhöhe der Jäger"] = "Hunter Rise", ["Die Anhöhe der Geister"] = "Spirit Rise",
    ["Thelgenfelsen"] = "Thelgen Rock", ["Lordamere-Internierungslager"] = "Lordamere Internment Camp",
    ["Der Lordameresee"] = "Lordamere Lake", ["Grabungsstätte von Bael'dun"] = "Bael'dun Digsite",
    ["Der Kodofriedhof"] = "Kodo Graveyard", ["Thoradinswall"] = "Thoradin's Wall",
    ["Der Greymane-Wall"] = "Greymane Wall", ["Die Ruinen von Alterac"] = "Ruins of Alterac",
    ["Strand der Darkspear"] = "Darkspear Strand", ["Die Insel Theramore"] = "Theramore Isle",
}

local function EnglishZone(zone)
    if not zone or zone == "" then return nil end
    return ZONE_EN[zone] or zone
end

---------------------------------------------------------------------------
-- Database
---------------------------------------------------------------------------

-- Stores one player. A player is identified by "Name-Realm": scanning the same
-- player again replaces the old record with the new data.
-- Record fields: name, realm, level, class (file name, e.g. "MAGE"),
-- race (file name, e.g. "NightElf"), faction, guild, zone, source ("who"/"unit"),
-- seen (time of this record), firstSeen (time the player was first recorded).
-- true if class, race, faction and level of a record are all known
IsComplete = function(p)
    if not p.class or not p.race or not p.level or p.level <= 0 then return false end
    if p.faction ~= "Alliance" and p.faction ~= "Horde" then return false end
    if not (RACE_FACTION[p.race] or RACE_NAMES[p.race]) then return false end
    for _, c in ipairs(classes) do
        if c.file == p.class then return true end
    end
    return #classes == 0 and RAID_CLASS_COLORS ~= nil and RAID_CLASS_COLORS[p.class] ~= nil
end

-- Returns nil if the record is ignored because something is unknown.
local function StorePlayer(p)
    local key = p.name .. "-" .. p.realm
    local old = db.players[key]
    if old and not p.level then p.level = old.level end -- "??" level of a much higher player
    if not IsComplete(p) then return nil, false end -- keep the old record, if any
    p.seen = time()
    p.firstSeen = old and old.firstSeen or p.seen
    db.players[key] = p
    return key, old == nil
end

-- Saving: WoW's Lua can only load about 262,000 different constants from one
-- SavedVariables file, and one table per player needs several of them (name,
-- key, guild, times ...). With 100,000+ players the file could not be loaded
-- any more ("constant table overflow"). So on logout every player becomes one
-- tab-separated line, and the lines are packed into a few large strings
-- (db.store). On login they are unpacked into db.players again.
local STORE_FIELDS = { "name", "realm", "level", "class", "race", "faction", "guild", "zone", "source", "seen", "firstSeen" }
local STORE_NUMBERS = { level = true, seen = true, firstSeen = true }
local STORE_CHUNK = 2000 -- players per saved string

local function StoreValue(v)
    if v == nil then return "" end
    return (tostring(v):gsub("[\t\n\r]", " "))
end

local function EncodePlayers(players)
    local store, lines, row = {}, {}, {}
    for _, p in pairs(players) do
        if p.name and p.realm then
            for i, field in ipairs(STORE_FIELDS) do row[i] = StoreValue(p[field]) end
            lines[#lines + 1] = table.concat(row, "\t")
            if #lines >= STORE_CHUNK then
                store[#store + 1] = table.concat(lines, "\n")
                lines = {}
            end
        end
    end
    if #lines > 0 then store[#store + 1] = table.concat(lines, "\n") end
    return store
end

local function DecodePlayers(store, players)
    for _, chunk in ipairs(store) do
        for line in chunk:gmatch("[^\n]+") do
            local p, i = {}, 0
            for value in (line .. "\t"):gmatch("([^\t]*)\t") do
                i = i + 1
                local field = STORE_FIELDS[i]
                if field and value ~= "" then
                    p[field] = STORE_NUMBERS[field] and tonumber(value) or value
                end
            end
            if p.name and p.realm then players[p.name .. "-" .. p.realm] = p end
        end
    end
end

-- after login: unpack the saved strings
local function LoadPlayers()
    if type(db.players) ~= "table" then db.players = {} end -- older versions saved the tables directly
    if type(db.store) == "table" then DecodePlayers(db.store, db.players) end
    db.store = nil
end

-- on logout / reload: pack the players into strings, only the strings are saved
local function SavePlayers()
    if not db or type(db.players) ~= "table" then return end
    local ok, store = pcall(EncodePlayers, db.players)
    if ok then
        db.store, db.storeVersion, db.players = store, 1, nil
    end
end

local refreshQueued = false
local function RequestRefresh()
    if refreshQueued then return end
    refreshQueued = true
    After(0.3, function()
        refreshQueued = false
        if RefreshPanel then RefreshPanel() end
    end)
end

---------------------------------------------------------------------------
-- /who in the background
--
-- Scan queries run without any window or chat output:
-- * SetWhoToUi(true) sends the answer to the addon instead of the chat,
-- * the Friends/Who window does not get WHO_LIST_UPDATE while our query runs,
--   so it does not open,
-- * a chat filter hides "N players total" and the who result lines meanwhile.
-- /who searches you type yourself are shown as usual.
---------------------------------------------------------------------------

local sendingOurs = false -- true while the addon itself calls SendWho

local function SendWhoQuery(text)
    sendingOurs = true
    local ok, err = pcall(C_FriendList.SendWho, text)
    sendingOurs = false
    if not ok then error(err, 0) end
end

local function SetWhoToUi(v)
    C_FriendList.SetWhoToUi(v)
end

local function GetNumWho()
    return C_FriendList.GetNumWhoResults()
end

-- name, guild, level, race, class, zone, classFile
local function GetWho(i)
    local w = C_FriendList.GetWhoInfo(i)
    if not w then return end
    return w.fullName, w.fullGuildName, w.level, w.raceStr, w.classStr, w.area, w.filename
end

local suppressedFrames = {}
local quietUntil = 0           -- chat filter and window guard are active until this time
local LATE_WAIT = 30           -- seconds a timed-out query may still be answered
local lateUntil = 0            -- a timed-out query may still be answered until this time
local socialWasOpen = false    -- the Social window was already open when our query was sent
local eventFrame               -- our own event frame (set below), never unregistered

local function InQuietTime()
    return GetTime() <= quietUntil
end

local function SuppressWhoUI()
    quietUntil = math.max(quietUntil, GetTime() + WHO_TIMEOUT + 2)
    socialWasOpen = _G.FriendsFrame and _G.FriendsFrame:IsShown() or false
    -- every frame that listens to the result, not only the Friends/Who window
    local frames
    if GetFramesRegisteredForEvent then
        frames = { GetFramesRegisteredForEvent("WHO_LIST_UPDATE") }
    else
        frames = { _G.FriendsFrame, _G.WhoFrame }
    end
    for _, frame in ipairs(frames) do
        if frame and frame ~= eventFrame and frame.IsEventRegistered and frame:IsEventRegistered("WHO_LIST_UPDATE") then
            if pcall(frame.UnregisterEvent, frame, "WHO_LIST_UPDATE") then
                suppressedFrames[#suppressedFrames + 1] = frame
            end
        end
    end
end

-- Safety net: if the client opens the Who window for our query anyway, close it again.
-- A Social window you opened yourself is left alone.
local function CloseWhoWindowIfOurs()
    if not InQuietTime() or socialWasOpen then return end
    local friends, who = _G.FriendsFrame, _G.WhoFrame
    if friends and friends:IsShown() and (not who or who:IsShown()) then
        HideUIPanel(friends)
    end
end

local function GuardWhoWindow()
    for _, frame in ipairs({ _G.FriendsFrame, _G.WhoFrame }) do
        if frame then
            -- next frame: the Who tab is selected only after the window is shown
            frame:HookScript("OnShow", function() After(0, CloseWhoWindowIfOurs) end)
        end
    end
end

local function RestoreWhoUI()
    quietUntil = GetTime() + 1
    -- a short delay so the frames do not still receive the event we are handling
    After(0.2, function()
        CloseWhoWindowIfOurs()
        for i = #suppressedFrames, 1, -1 do
            pcall(suppressedFrames[i].RegisterEvent, suppressedFrames[i], "WHO_LIST_UPDATE")
            suppressedFrames[i] = nil
        end
        SetWhoToUi(false) -- game default: small /who results go to chat
    end)
end

-- A query timed out, but the server may still answer it. If the Who window
-- listened again by then, the late answer would open it. So the window stays
-- muted for a while longer and a late answer is recorded silently.
local function WaitForLateAnswer()
    lateUntil = GetTime() + LATE_WAIT
    quietUntil = math.max(quietUntil, lateUntil)
end

-- A /who typed by the player (or sent by another addon) while we wait for a
-- late answer: give the Who window back at once so that search shows as usual.
local function OnAnySendWho()
    if sendingOurs or lateUntil == 0 then return end
    lateUntil = 0
    RestoreWhoUI()
end

-- Turns a format string from the game ("%d |4player:players; total") into a Lua pattern.
local function FormatToPattern(fmt)
    if type(fmt) ~= "string" or fmt == "" then return nil end
    local mark = string.char(1) -- placeholder for anything variable
    local p = fmt:gsub("|4[^;]*;", mark):gsub("%%%d*%$?[%-%.%d]*[sdf]", mark)
    p = p:gsub("[%^%$%(%)%%%.%[%]%*%+%-%?]", "%%%0")
    p = p:gsub(mark, ".-")
    return "^" .. p .. "$"
end

local quietPatterns = {}
for _, name in ipairs({ "WHO_NUM_RESULTS", "WHO_LIST_FORMAT", "WHO_LIST_GUILD_FORMAT" }) do
    local pattern = FormatToPattern(_G[name])
    if pattern then quietPatterns[#quietPatterns + 1] = pattern end
end

local function WhoChatFilter(_, _, msg)
    if GetTime() > quietUntil or type(msg) ~= "string" then return false end
    for _, pattern in ipairs(quietPatterns) do
        if msg:find(pattern) then return true end
    end
    return false
end

local function InstallChatFilter()
    local add = ChatFrame_AddMessageEventFilter or (ChatFrameUtil and ChatFrameUtil.AddMessageEventFilter)
    if add then add("CHAT_MSG_SYSTEM", WhoChatFilter) end
end

---------------------------------------------------------------------------
-- Recording
---------------------------------------------------------------------------

-- In some places (e.g. battlegrounds and instances) the game hands out
-- "secret values" instead of real data: an addon may not compare them or use
-- them as table keys, so those players are skipped.
local issecretvalue = _G.issecretvalue
local function HasSecret(...)
    if not issecretvalue then return false end
    for i = 1, select("#", ...) do
        if issecretvalue((select(i, ...))) then return true end
    end
    return false
end

local function RecordWhoResults(forScan)
    local num, total = GetNumWho()
    num = num or 0
    local myFaction = UnitFactionGroup("player")
    local new = 0
    for i = 1, num do
        local fullName, guild, level, raceStr, classStr, zone, classFile = GetWho(i)
        if HasSecret(fullName, guild, level, raceStr, classStr, zone, classFile) then fullName = nil end
        local name, realm = SplitName(fullName)
        if name then
            local race = ResolveRace(raceStr)
            local class = classFile
            if (not class or class == "") and classStr then class = classByName[classStr:lower()] or classStr end
            local key, isNew = StorePlayer({
                name = name,
                realm = realm,
                level = tonumber(level),
                class = class,
                race = race,
                faction = RACE_FACTION[race] or myFaction, -- /who only lists your own faction
                guild = (guild and guild ~= "") and guild or nil,
                zone = EnglishZone(zone),
                source = "who",
            })
            if isNew then new = new + 1 end
            if forScan and key and not scan.found[key] then
                scan.found[key] = true
                scan.foundCount = scan.foundCount + 1
            end
        end
    end
    if forScan then scan.new = scan.new + new end
    return num, total, new
end

local function RecordUnit(unit)
    if not (db and db.enabled and db.recordUnits) then return end
    if not (UnitExists(unit) and UnitIsPlayer(unit)) then return end
    local name, realm = UnitName(unit)
    if HasSecret(name, realm) then return end
    if not name or name == "" or name == UNKNOWNOBJECT then return end
    -- WoW Forever names are "First Last": the game returns the last name where
    -- the realm usually is. The player is always on your own super server.
    if realm and realm ~= "" then name = name .. " " .. realm end
    realm = MyRealm()
    local level = UnitLevel(unit)
    local _, classFile = UnitClass(unit)
    local _, raceFile = UnitRace(unit)
    local faction = UnitFactionGroup(unit)
    local guild = GetGuildInfo(unit)
    local zone = GetRealZoneText and GetRealZoneText() or nil
    if HasSecret(level, classFile, raceFile, faction, guild, zone) then return end
    if not level or level <= 0 then level = nil end
    StorePlayer({
        name = name,
        realm = realm,
        level = level,
        class = classFile,
        race = raceFile,
        faction = faction or RACE_FACTION[raceFile],
        guild = guild,
        zone = EnglishZone(zone),
        source = "unit",
    })
    RequestRefresh()
end

---------------------------------------------------------------------------
-- Scanning
--
-- * A pass asks every level once, without any other filter, from the highest
--   level down to level 1: 60-60, 59-59, ..., 1-1. Then the next pass starts
--   again at the highest level, until you press Stop.
-- * /who returns at most 50 players per query. A level with 50+ players online
--   is not split, so some of its players can be missed; the pass summary says
--   how many levels hit the limit.
-- * /who may only be sent from a key press or click (hardware event). The
--   automatic scan therefore sends the next query on your next key press or
--   click in the game world once the cooldown is over.
---------------------------------------------------------------------------

-- letters for the deep search
local LETTERS = {}
for c in ("abcdefghijklmnopqrstuvwxyz"):gmatch(".") do LETTERS[#LETTERS + 1] = c end

local function QueryText(q)
    local t = q.lo .. "-" .. q.hi
    if q.letter then t = t .. ' n-"' .. q.letter .. '"' end
    return t
end

-- queries from older versions of the addon (level ranges, class / race / name filters)
local function HasOldQueries(list)
    for _, q in ipairs(list) do
        if q.hi ~= q.lo or q.class or q.race then return true end
    end
    return false
end

local function StartPass()
    db.scanPass = (db.scanPass or 0) + 1
    wipe(scan.queue)
    for level = MaxLevel(), 1, -1 do
        scan.queue[#scan.queue + 1] = { lo = level, hi = level }
    end
    scan.active = true
    scan.sent = 0
    scan.found = {}
    scan.foundCount = 0
    scan.new = 0
    scan.incomplete = 0
end

local function FinishPass()
    scan.active = false
    local msg = string.format("scan pass %d done: %d queries, %s players found (%s new). Database: %s players.",
        db.scanPass, scan.sent, Num(scan.foundCount), Num(scan.new), Num(PlayerCount()))
    if scan.incomplete > 0 then
        msg = msg .. string.format(" %d level(s) had %d+ players, some of them may be missing.", scan.incomplete, MAX_WHO_RESULTS)
    end
    Print(msg)
end

-- Pauses the scan. The current pass is kept and continues on Start.
local function StopScan()
    db.autoScan = false
    Print("scan stopped. Click |cffffd100Start scan|r (or right-click the minimap button) to continue.")
    if UpdateScanUI then UpdateScanUI() end
end

local function CooldownLeft()
    return math.max(0, (db.whoCooldown or 5) - (GetTime() - scan.lastSend))
end

-- true if the addon and the /who search are switched on in the options
local function CanWho()
    return db ~= nil and db.enabled and db.whoEnabled and not whoPaused
end

-- Sends the next query. Must be called from a key press or click.
-- Sending manually also (re)starts the automatic scan.
local function ScanNext(verbose)
    if not db then return end
    if not CanWho() then
        if verbose then
            if not db.enabled then
                Print("the addon is switched off in the options (|cffffd100/fps on|r).")
            elseif not db.whoEnabled then
                Print("the /who search is switched off in the options (|cffffd100/fps who on|r).")
            else
                Print("the /who search is paused until you log out (|cffffd100/fps who resume|r).")
            end
        end
        return
    end
    if not db.autoScan then
        db.autoScan = true
        Print("scan started. It runs until you press |cffffd100Stop|r.")
    end
    if scan.pending then
        if verbose then Print("still waiting for the server's answer.") end
        return
    end
    local wait = CooldownLeft()
    if wait > 0 then
        if verbose then Print(string.format("next query in %d second(s).", math.ceil(wait))) end
        UpdateScanUI()
        return
    end
    if not scan.active or #scan.queue == 0 then StartPass() end
    -- levels in order, from the highest level down to 1
    local q = table.remove(scan.queue, 1)
    -- deep search: a random letter of the name, so busy levels show other players each pass
    if q then q.letter = db.deepSearch and LETTERS[math.random(#LETTERS)] or nil end
    if not q then return end

    q.sent = GetTime()
    scan.pending = q
    scan.lastSend = q.sent
    scan.sent = scan.sent + 1
    SuppressWhoUI()
    SetWhoToUi(true)
    local ok, err = pcall(SendWhoQuery, QueryText(q))
    if not ok then
        scan.pending = nil
        table.insert(scan.queue, 1, q)
        RestoreWhoUI()
        Print("|cffff4040could not send /who:|r " .. tostring(err))
    end
    UpdateScanUI()
end

-- Called on every key press and every click into the game world.
local function AutoScanTrigger()
    if CanWho() and db.autoScan and not scan.pending and CooldownLeft() == 0 then
        ScanNext(false)
    end
end

-- A keyboard listener that lets every key pass through to the game
-- (movement, spells, ...) and only uses the key press to send /who.
local autoTriggerReady = false
local function CreateAutoTrigger()
    if autoTriggerReady then return end
    if InCombatLockdown and InCombatLockdown() then return end -- retried after combat
    autoTriggerReady = true

    local kb = CreateFrame("Frame", "ForeverPlayerStatisticsKeyListener", UIParent)
    if kb.SetPropagateKeyboardInput then
        pcall(kb.SetPropagateKeyboardInput, kb, true)
        local passes = not kb.GetPropagateKeyboardInput or kb:GetPropagateKeyboardInput()
        if passes then
            -- never swallow keys: only listen when key presses are passed on
            kb:EnableKeyboard(true)
            kb:SetScript("OnKeyDown", AutoScanTrigger)
        end
    end
    if WorldFrame and WorldFrame.HookScript then
        WorldFrame:HookScript("OnMouseDown", AutoScanTrigger)
    end
end

local function OnWhoListUpdate()
    local q = scan.pending
    if not q and lateUntil > 0 and GetTime() <= lateUntil then
        -- late answer to a query that timed out: record it, keep the window closed
        lateUntil = 0
        if db.enabled then RecordWhoResults(true) end
        RestoreWhoUI()
        RequestRefresh()
        return
    end
    if q then lateUntil = 0 end
    if not q and not (db.enabled and db.recordOwnWho) then return end
    local num, total = RecordWhoResults(q ~= nil)
    if q then
        scan.pending = nil
        RestoreWhoUI()
        local truncated = (total and total > num) or num >= MAX_WHO_RESULTS
        local note = ""
        if truncated then
            scan.incomplete = scan.incomplete + 1
            note = " |cffff4040(50+ players, some are missing)|r"
        end
        scan.lastResult = string.format("%s: %d player%s%s", QueryText(q), num, num == 1 and "" or "s", note)
        if scan.active and #scan.queue == 0 then FinishPass() end
        UpdateScanUI()
    end
    RequestRefresh()
end

-- Requeues a query the server never answered (e.g. sent too quickly).
local function CheckTimeout()
    local q = scan.pending
    if q and GetTime() - q.sent > WHO_TIMEOUT then
        scan.pending = nil
        table.insert(scan.queue, 1, { lo = q.lo, hi = q.hi })
        scan.active = true
        WaitForLateAnswer() -- not RestoreWhoUI: a late answer would open the Who window
        scan.lastResult = "|cffff4040no answer for " .. QueryText(q) .. "|r - it will be sent again"
        UpdateScanUI()
    end
    -- no late answer came: give the Who window back
    if lateUntil > 0 and not scan.pending and GetTime() > lateUntil then
        lateUntil = 0
        RestoreWhoUI()
    end
end

---------------------------------------------------------------------------
-- Statistics
---------------------------------------------------------------------------

-- Selection in the overview: a level, class and / or race clicked by the user.
-- Each list is counted with the other two selections, so clicking level 23
-- shows the classes and races of level 23, clicking a class shows its races and
-- its players per level, and so on.
local sel = { level = nil, class = nil, race = nil }

-- race key used in the statistics: races on both factions (Skyborne) are counted
-- per faction, e.g. "Skyborne:Horde"
local function RaceKey(p)
    local r = p.race or "?"
    if RACE_NAMES[r] and not RACE_FACTION[r] and p.faction then r = r .. ":" .. p.faction end
    return r
end

local function ComputeStats()
    local s = {
        total = 0, faction = {}, factionTotal = 0,
        class = {}, classTotal = 0, race = {}, raceTotal = 0,
        level = {}, levelTotal = 0, maxLevel = 0,
    }
    local myRealm = MyRealm()
    for _, p in pairs(db.players) do
        -- records with an unknown class, race, faction or level are ignored
        if IsComplete(p) and (not db.filterRealm or p.realm == myRealm) then
            local f = p.faction or "Unknown"
            s.faction[f] = (s.faction[f] or 0) + 1
            s.factionTotal = s.factionTotal + 1
            if db.filterFaction == "ALL" or p.faction == db.filterFaction then
                local c, r, l = p.class or "?", RaceKey(p), tonumber(p.level) or 0
                local okLevel = not sel.level or l == sel.level
                local okClass = not sel.class or c == sel.class
                local okRace = not sel.race or r == sel.race
                if okLevel and okClass and okRace then s.total = s.total + 1 end
                if okLevel and okRace then
                    s.class[c] = (s.class[c] or 0) + 1
                    s.classTotal = s.classTotal + 1
                end
                if okLevel and okClass then
                    s.race[r] = (s.race[r] or 0) + 1
                    s.raceTotal = s.raceTotal + 1
                end
                if okClass and okRace and l > 0 then
                    s.level[l] = (s.level[l] or 0) + 1
                    s.levelTotal = s.levelTotal + 1
                end
                if l > s.maxLevel then s.maxLevel = l end
            end
        end
    end
    return s
end

-- counts -> sorted list; by count (default) or by the displayed name
local function Sorted(counts, nameOf)
    local list = {}
    for k, n in pairs(counts) do list[#list + 1] = { key = k, n = n } end
    table.sort(list, function(a, b)
        if db.sortByName and nameOf then
            local na, nb = nameOf(a.key), nameOf(b.key)
            if na ~= nb then return na < nb end
        elseif a.n ~= b.n then
            return a.n > b.n
        end
        return tostring(a.key) < tostring(b.key)
    end)
    return list
end

---------------------------------------------------------------------------
-- Overview panel
---------------------------------------------------------------------------

local W, H = 600, 845
local INNER_W = W - 40
local ROWS = 12
local ROW_H = 16
local ROW_BAR_W = 100
local HIST_H = 110

local function CreateCheck(parent, label, x, y, get, set)
    local cb = CreateFrame("CheckButton", nil, parent, "UICheckButtonTemplate")
    cb:SetPoint("TOPLEFT", x, y)
    cb.text = cb:CreateFontString(nil, "ARTWORK", "GameFontNormalSmall")
    cb.text:SetPoint("LEFT", cb, "RIGHT", 2, 0)
    cb.text:SetText(label)
    cb:SetScript("OnClick", function(self) set(self:GetChecked() and true or false) end)
    cb.Refresh = function(self) self:SetChecked(get()) end
    return cb
end

local function Header(parent, text, x, y)
    local fs = parent:CreateFontString(nil, "ARTWORK", "GameFontNormal")
    fs:SetPoint("TOPLEFT", x, y)
    fs:SetText(text)
    return fs
end

-- onClick(key) is called when a row is clicked
local function CreateRows(x, y, onClick)
    local rows = {}
    for i = 1, ROWS do
        local ry = y - (i - 1) * ROW_H
        local r = {}
        -- the whole row is a button: click selects / deselects this class or race
        r.btn = CreateFrame("Button", nil, panel)
        r.btn:SetPoint("TOPLEFT", x - 2, ry + 2)
        r.btn:SetSize(INNER_W / 2 - 5, ROW_H)
        r.sel = r.btn:CreateTexture(nil, "BACKGROUND")
        r.sel:SetAllPoints()
        SetColor(r.sel, 1, 0.82, 0, 0.25)
        r.hl = r.btn:CreateTexture(nil, "HIGHLIGHT")
        r.hl:SetAllPoints()
        SetColor(r.hl, 1, 1, 1, 0.08)
        r.btn:SetScript("OnClick", function() if r.key then onClick(r.key) end end)
        r.btn:SetScript("OnEnter", function(self)
            if not r.key then return end
            GameTooltip:SetOwner(self, "ANCHOR_RIGHT")
            GameTooltip:AddLine(r.label)
            GameTooltip:AddLine(r.valueText, 1, 1, 1)
            GameTooltip:AddLine(r.selected and "Click to show all again" or "Click to filter by this", 0.6, 0.6, 0.6)
            GameTooltip:Show()
        end)
        r.btn:SetScript("OnLeave", GameTooltip_Hide)

        r.name = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
        r.name:SetPoint("TOPLEFT", x, ry)
        r.name:SetSize(90, ROW_H)
        r.name:SetJustifyH("LEFT")
        r.name:SetJustifyV("TOP")
        if r.name.SetWordWrap then r.name:SetWordWrap(false) end -- long names are cut, never wrapped
        r.bg = panel:CreateTexture(nil, "BORDER")
        r.bg:SetPoint("TOPLEFT", x + 95, ry)
        r.bg:SetSize(ROW_BAR_W, 11)
        SetColor(r.bg, 0, 0, 0, 0.4)
        r.bar = panel:CreateTexture(nil, "ARTWORK")
        r.bar:SetPoint("TOPLEFT", x + 95, ry)
        r.bar:SetHeight(11)
        r.value = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
        r.value:SetPoint("TOPLEFT", x + 200, ry)
        r.value:SetSize(75, ROW_H)
        r.value:SetJustifyH("RIGHT")
        r.value:SetJustifyV("TOP")
        if r.value.SetWordWrap then r.value:SetWordWrap(false) end
        rows[i] = r
    end
    return rows
end

-- nameOf(key) -> text; colorOf(key) -> r, g, b; selected = key of the selected row
local function FillRows(rows, counts, total, nameOf, colorOf, selected)
    if selected and not counts[selected] then counts[selected] = 0 end -- keep the selection visible
    local list = Sorted(counts, nameOf)
    if selected then
        -- the selected row is always visible, also when the list is long
        for i, e in ipairs(list) do
            if e.key == selected and i >= ROWS then
                table.remove(list, i)
                table.insert(list, 1, e)
                break
            end
        end
    end
    local maxN = 1
    for _, e in ipairs(list) do maxN = math.max(maxN, e.n) end
    for i, r in ipairs(rows) do
        local e = list[i]
        if i == ROWS and #list > ROWS then
            -- last row sums up everything that does not fit
            local rest = 0
            for j = ROWS, #list do rest = rest + list[j].n end
            e = { key = false, n = rest }
        end
        local shown = e ~= nil
        SetShown(r.name, shown); SetShown(r.bg, shown); SetShown(r.bar, shown); SetShown(r.value, shown)
        SetShown(r.btn, shown)
        r.key = e and e.key or nil
        r.selected = e and e.key ~= false and e.key == selected
        SetShown(r.sel, r.selected)
        if e then
            local cr, cg, cb = 0.6, 0.6, 0.6
            if e.key then cr, cg, cb = colorOf(e.key) end
            r.label = e.key and nameOf(e.key) or "Other"
            r.valueText = Num(e.n) .. " players (" .. Pct(e.n, total) .. ")"
            r.name:SetText(r.label)
            r.name:SetTextColor(cr, cg, cb)
            SetColor(r.bar, cr, cg, cb, 0.85)
            r.bar:SetWidth(math.max(1, ROW_BAR_W * math.min(1, e.n / maxN)))
            r.value:SetText(Num(e.n) .. "  " .. Pct(e.n, total))
        end
    end
end

local function ClassColor(file)
    local c = RAID_CLASS_COLORS and RAID_CLASS_COLORS[file]
    if c then return c.r, c.g, c.b end
    return 0.7, 0.7, 0.7
end

local function RaceColor(key)
    local _, faction = key:match("^(.-):(.+)$")
    local c = FACTION_COLORS[faction or RACE_FACTION[key]]
    if c then return c[1], c[2], c[3] end
    return 0.7, 0.7, 0.7
end

local function ClassLabel(file)
    if file == "?" then return "Unknown" end
    return ClassName(file)
end

local FACTION_SHORT = { Alliance = "A", Horde = "H" }
local function RaceLabel(key)
    if key == "?" then return "Unknown" end
    local file, faction = key:match("^(.-):(.+)$")
    if file then return RaceName(file) .. " (" .. (FACTION_SHORT[faction] or faction) .. ")" end
    return RaceName(key)
end

local function RefreshFactionBar(s)
    local fb = panel.factionBar
    local a, h = s.faction.Alliance or 0, s.faction.Horde or 0
    local sum = a + h
    if sum == 0 then
        fb.a:Hide(); fb.h:Hide()
        fb.text:SetText("no players yet")
    else
        local aw = INNER_W * a / sum
        SetShown(fb.a, a > 0); SetShown(fb.h, h > 0)
        fb.a:SetWidth(math.max(1, aw))
        fb.h:SetWidth(math.max(1, INNER_W - aw))
        fb.text:SetText(string.format("Alliance %s (%s)        Horde %s (%s)", Pct(a, sum), Num(a), Pct(h, sum), Num(h)))
    end
    local unknown = s.faction.Unknown or 0
    panel.factionNote:SetText(unknown > 0 and (Num(unknown) .. " players with unknown faction are not counted here.") or
        "/who only lists your own faction; the other faction is recorded when you target or mouse over its players.")
end

local function RefreshHistogram(s)
    local hist = panel.hist
    local n = math.max(MaxLevel(), s.maxLevel)
    local bw = INNER_W / n
    local maxCount = 0
    for l = 1, n do maxCount = math.max(maxCount, s.level[l] or 0) end

    for l = 1, n do
        local b = hist.bars[l]
        if not b then
            b = CreateFrame("Frame", nil, hist)
            b:EnableMouse(true)
            b.tex = b:CreateTexture(nil, "ARTWORK")
            b.tex:SetPoint("BOTTOMLEFT")
            b.tex:SetPoint("BOTTOMRIGHT")
            b.sel = b:CreateTexture(nil, "BACKGROUND")
            b.sel:SetAllPoints()
            SetColor(b.sel, 1, 1, 1, 0.15)
            b:SetScript("OnEnter", function(self)
                SetColor(self.tex, 1, 1, 1, 1)
                GameTooltip:SetOwner(self, "ANCHOR_TOP")
                GameTooltip:AddLine("Level " .. self.level)
                GameTooltip:AddLine(string.format("%s players (%s)", Num(self.count), Pct(self.count, self.total)), 1, 1, 1)
                GameTooltip:AddLine(sel.level == self.level and "Click to show all levels again"
                    or "Click to show the classes and races of this level", 0.6, 0.6, 0.6)
                GameTooltip:Show()
            end)
            b:SetScript("OnLeave", function(self)
                SetColor(self.tex, self.cr, self.cg, self.cb, 0.9)
                GameTooltip:Hide()
            end)
            b:SetScript("OnMouseUp", function(self)
                sel.level = sel.level ~= self.level and self.level or nil
                RefreshPanel()
            end)
            hist.bars[l] = b
        end
        b:ClearAllPoints()
        b:SetPoint("BOTTOMLEFT", hist, "BOTTOMLEFT", (l - 1) * bw, 0)
        b:SetSize(math.max(1, bw > 3 and bw - 1 or bw), HIST_H)
        local c = s.level[l] or 0
        b.level, b.count, b.total = l, c, s.levelTotal
        -- bars in the color of the selected class or race, the selected level in white
        b.cr, b.cg, b.cb = 1, 0.82, 0
        if sel.level == l then
            b.cr, b.cg, b.cb = 1, 1, 1
        elseif sel.class then
            b.cr, b.cg, b.cb = ClassColor(sel.class)
        elseif sel.race then
            b.cr, b.cg, b.cb = RaceColor(sel.race)
        end
        SetColor(b.tex, b.cr, b.cg, b.cb, 0.9)
        SetShown(b.sel, sel.level == l)
        if c > 0 then
            b.tex:SetHeight(math.max(1, HIST_H * c / maxCount))
            b.tex:Show()
        else
            b.tex:Hide()
        end
        b:Show()
    end
    for l = n + 1, #hist.bars do hist.bars[l]:Hide() end

    -- axis labels: level 1 and every 10 (every 20 for very high level caps)
    local step = n > 80 and 20 or 10
    local marks = { 1 }
    for l = step, n, step do marks[#marks + 1] = l end
    for i, l in ipairs(marks) do
        local fs = hist.labels[i]
        if not fs then
            fs = hist:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
            hist.labels[i] = fs
        end
        fs:ClearAllPoints()
        fs:SetPoint("TOP", hist, "BOTTOMLEFT", (l - 0.5) * bw, -2)
        fs:SetText(tostring(l))
        fs:Show()
    end
    for i = #marks + 1, #hist.labels do hist.labels[i]:Hide() end

    hist.maxText:SetText(maxCount > 0 and ("max " .. Num(maxCount)) or "")

    -- level brackets in percent
    local parts = {}
    for lo = 1, n, LEVEL_STEP do
        local hi = math.min(lo + LEVEL_STEP - 1, n)
        local sum = 0
        for l = lo, hi do sum = sum + (s.level[l] or 0) end
        parts[#parts + 1] = string.format("|cffffd100%d-%d|r %s", lo, hi, Pct(sum, s.levelTotal))
    end
    parts[#parts + 1] = string.format("|cffffd100%d|r %s", n, Pct(s.level[n] or 0, s.levelTotal))
    panel.brackets:SetText(table.concat(parts, "   "))
end

local FACTION_FILTER_LABEL = { ALL = "All", Alliance = "|cff4080ffAlliance|r", Horde = "|cffe63333Horde|r" }

function RefreshPanel()
    if not (panel and panel:IsShown()) then return end
    for _, cb in ipairs(panel.checks) do cb:Refresh() end
    local s = ComputeStats()

    local all = PlayerCount()
    panel.summary:SetText(string.format("|cffffd100%s|r players in the database   -   |cffffd100%s|r match the filter   -   server: |cffffd100%s|r",
        Num(all), Num(s.total), MyRealm()))
    panel.factionBtn:SetText("Faction: " .. FACTION_FILTER_LABEL[db.filterFaction])

    RefreshFactionBar(s)
    FillRows(panel.classRows, s.class, s.classTotal, ClassLabel, ClassColor, sel.class)
    FillRows(panel.raceRows, s.race, s.raceTotal, RaceLabel, RaceColor, sel.race)
    RefreshHistogram(s)

    -- headers show what the lists are filtered by
    local lvl = sel.level and ("level " .. sel.level) or nil
    local function Suffix(...)
        local parts = {}
        for i = 1, select("#", ...) do
            local v = select(i, ...)
            if v then parts[#parts + 1] = v end
        end
        return #parts > 0 and ("|cffffffff - " .. table.concat(parts, ", ") .. "|r") or ""
    end
    panel.classHeader:SetText("Classes" .. Suffix(lvl, sel.race and RaceLabel(sel.race)))
    panel.raceHeader:SetText("Races" .. Suffix(lvl, sel.class and ClassLabel(sel.class)))
    panel.levelHeader:SetText("Players per level" .. Suffix(sel.class and ClassLabel(sel.class), sel.race and RaceLabel(sel.race)))
    panel.sortBtn:SetText(db.sortByName and "Sort: name" or "Sort: count")
    SetShown(panel.clearBtn, sel.level or sel.class or sel.race)
    UpdateScanUI()
end

function UpdateScanUI()
    if not (panel and panel:IsShown()) then return end
    local btn = panel.scanBtn
    local wait = CooldownLeft()
    if not CanWho() then
        btn:SetText(not db.enabled and "Addon off" or not db.whoEnabled and "/who search off" or "/who paused")
        btn:SetEnabled(false)
        panel.stopBtn:SetEnabled(false)
        if not db.enabled then
            panel.status:SetText("|cffff4040The addon is switched off:|r nothing is recorded. Turn it on below.")
        elseif not db.whoEnabled then
            panel.status:SetText("|cffff4040The /who search is switched off.|r Turn it on below to scan again.")
        else
            panel.status:SetText("|cffffd100The /who search is paused until you log out.|r Untick the pause below to scan again.")
        end
        return
    end
    if scan.pending then
        btn:SetText("Waiting...")
        btn:SetEnabled(false)
    elseif wait > 0 then
        btn:SetText(string.format("Wait %ds", math.ceil(wait)))
        btn:SetEnabled(false)
    elseif db.autoScan then
        btn:SetText("Scan now")
        btn:SetEnabled(true)
    else
        btn:SetText(scan.active and "Continue scan" or "Start scan")
        btn:SetEnabled(true)
    end
    panel.stopBtn:SetEnabled(db.autoScan)

    local status
    if db.autoScan then
        status = string.format("|cff00ff00Scanning|r - pass %d: sent |cffffffff%d|r, left |cffffffff%d|r, found |cffffffff%s|r (%s new)",
            db.scanPass or 0, scan.sent, #scan.queue + (scan.pending and 1 or 0), Num(scan.foundCount), Num(scan.new))
        if scan.pending then
            status = status .. "\nAsking the server: " .. QueryText(scan.pending)
        elseif wait <= 0 then
            status = status .. "\nNext query goes out with your next key press or click."
        elseif scan.lastResult then
            status = status .. "\nLast: " .. scan.lastResult
        end
    else
        status = "|cffff4040Scan stopped.|r Click Start to continue."
        if scan.lastResult then status = status .. "\nLast: " .. scan.lastResult end
    end
    panel.status:SetText(status)
end

local function CreatePanel()
    panel = CreateFrame("Frame", "ForeverPlayerStatisticsPanel", UIParent,
        "BackdropTemplate")
    panel:SetSize(W, H)
    panel:SetPoint("CENTER")
    if panel.SetClampedToScreen then panel:SetClampedToScreen(true) end
    panel:SetFrameStrata("DIALOG")
    panel:SetMovable(true)
    panel:EnableMouse(true)
    panel:RegisterForDrag("LeftButton")
    panel:SetScript("OnDragStart", panel.StartMoving)
    panel:SetScript("OnDragStop", panel.StopMovingOrSizing)
    if panel.SetBackdrop then
        panel:SetBackdrop({
            bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
            edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
            tile = true, tileSize = 32, edgeSize = 32,
            insets = { left = 8, right = 8, top = 8, bottom = 8 },
        })
    end
    panel:Hide()
    tinsert(UISpecialFrames, "ForeverPlayerStatisticsPanel")

    local title = panel:CreateFontString(nil, "ARTWORK", "GameFontNormalLarge")
    title:SetPoint("TOP", 0, -16)
    title:SetText("Forever Player Statistics")

    local close = CreateFrame("Button", nil, panel, "UIPanelCloseButton")
    close:SetPoint("TOPRIGHT", -4, -4)

    -- summary and filters
    panel.summary = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlight")
    panel.summary:SetPoint("TOPLEFT", 20, -42)

    panel.checks = {}
    panel.factionBtn = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    panel.factionBtn:SetSize(130, 22)
    panel.factionBtn:SetPoint("TOPLEFT", 18, -62)
    panel.factionBtn:SetScript("OnClick", function()
        local nextFilter = { ALL = "Alliance", Alliance = "Horde", Horde = "ALL" }
        db.filterFaction = nextFilter[db.filterFaction] or "ALL"
        RefreshPanel()
    end)
    panel.checks[#panel.checks + 1] = CreateCheck(panel, "Only this realm", 160, -60,
        function() return db.filterRealm end,
        function(v) db.filterRealm = v; RefreshPanel() end)

    -- sort order of the class and race lists
    panel.sortBtn = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    panel.sortBtn:SetSize(100, 22)
    panel.sortBtn:SetPoint("TOPRIGHT", -112, -62)
    panel.sortBtn:SetScript("OnClick", function()
        db.sortByName = not db.sortByName
        RefreshPanel()
    end)
    -- removes the level / class / race selection
    panel.clearBtn = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    panel.clearBtn:SetSize(90, 22)
    panel.clearBtn:SetPoint("TOPRIGHT", -18, -62)
    panel.clearBtn:SetText("Show all")
    panel.clearBtn:SetScript("OnClick", function()
        sel.level, sel.class, sel.race = nil, nil, nil
        RefreshPanel()
    end)

    -- Alliance vs Horde
    Header(panel, "Alliance vs Horde", 20, -96)
    local fb = CreateFrame("Frame", nil, panel)
    fb:SetSize(INNER_W, 18)
    fb:SetPoint("TOPLEFT", 20, -114)
    fb.bg = fb:CreateTexture(nil, "BACKGROUND")
    fb.bg:SetAllPoints()
    SetColor(fb.bg, 0, 0, 0, 0.5)
    fb.a = fb:CreateTexture(nil, "ARTWORK")
    fb.a:SetPoint("TOPLEFT"); fb.a:SetPoint("BOTTOMLEFT")
    SetColor(fb.a, FACTION_COLORS.Alliance[1], FACTION_COLORS.Alliance[2], FACTION_COLORS.Alliance[3], 0.85)
    fb.h = fb:CreateTexture(nil, "ARTWORK")
    fb.h:SetPoint("TOPRIGHT"); fb.h:SetPoint("BOTTOMRIGHT")
    SetColor(fb.h, FACTION_COLORS.Horde[1], FACTION_COLORS.Horde[2], FACTION_COLORS.Horde[3], 0.85)
    fb.text = fb:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    fb.text:SetPoint("CENTER")
    panel.factionBar = fb
    panel.factionNote = panel:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
    panel.factionNote:SetPoint("TOPLEFT", 20, -136)
    panel.factionNote:SetWidth(INNER_W)
    panel.factionNote:SetJustifyH("LEFT")

    -- classes and races
    panel.classHeader = Header(panel, "Classes", 20, -158)
    panel.raceHeader = Header(panel, "Races", 20 + INNER_W / 2 + 5, -158)
    panel.classRows = CreateRows(20, -178, function(key)
        sel.class = sel.class ~= key and key or nil
        RefreshPanel()
    end)
    panel.raceRows = CreateRows(20 + INNER_W / 2 + 5, -178, function(key)
        sel.race = sel.race ~= key and key or nil
        RefreshPanel()
    end)

    -- players per level
    local histTop = -178 - ROWS * ROW_H - 14
    panel.levelHeader = Header(panel, "Players per level", 20, histTop)
    local hintText = panel:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
    hintText:SetPoint("TOPRIGHT", -20, histTop - 2)
    hintText:SetText("click a level, class or race to filter")
    local hist = CreateFrame("Frame", nil, panel)
    hist:SetSize(INNER_W, HIST_H)
    hist:SetPoint("TOPLEFT", 20, histTop - 20)
    hist.bg = hist:CreateTexture(nil, "BACKGROUND")
    hist.bg:SetAllPoints()
    SetColor(hist.bg, 0, 0, 0, 0.4)
    hist.bars, hist.labels = {}, {}
    hist.maxText = hist:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
    hist.maxText:SetPoint("TOPLEFT", 4, -3)
    panel.hist = hist

    panel.brackets = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
    panel.brackets:SetPoint("TOPLEFT", hist, "BOTTOMLEFT", 0, -20)
    panel.brackets:SetWidth(INNER_W)
    panel.brackets:SetJustifyH("LEFT")

    -- scanning
    local scanTop = histTop - 20 - HIST_H - 58
    local sep = panel:CreateTexture(nil, "ARTWORK")
    sep:SetPoint("TOPLEFT", 20, scanTop + 8)
    sep:SetSize(INNER_W, 1)
    SetColor(sep, 1, 0.82, 0, 0.3)

    panel.scanBtn = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    panel.scanBtn:SetSize(130, 24)
    panel.scanBtn:SetPoint("TOPLEFT", 18, scanTop)
    panel.scanBtn:SetScript("OnClick", function() ScanNext(true) end)

    panel.stopBtn = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    panel.stopBtn:SetSize(60, 24)
    panel.stopBtn:SetPoint("LEFT", panel.scanBtn, "RIGHT", 4, 0)
    panel.stopBtn:SetText("Stop")
    panel.stopBtn:SetScript("OnClick", function() StopScan() end)

    panel.status = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
    panel.status:SetPoint("TOPLEFT", panel.stopBtn, "TOPRIGHT", 10, 0)
    panel.status:SetWidth(INNER_W - 204)
    panel.status:SetJustifyH("LEFT")

    panel.checks[#panel.checks + 1] = CreateCheck(panel, "Record the results of my own /who searches", 14, scanTop - 50,
        function() return db.recordOwnWho end,
        function(v) db.recordOwnWho = v end)
    panel.checks[#panel.checks + 1] = CreateCheck(panel, "Record players I target or mouse over (also the other faction)", 14, scanTop - 74,
        function() return db.recordUnits end,
        function(v) db.recordUnits = v end)
    local deep = CreateCheck(panel, "Deep search: add a random name letter to each level query (finds other players on busy levels)", 14, scanTop - 98,
        function() return db.deepSearch end,
        function(v)
            db.deepSearch = v
            Print("deep search " .. OnOff(v) .. ".")
        end)
    panel.checks[#panel.checks + 1] = deep
    panel.checks[#panel.checks + 1] = CreateCheck(panel, "Addon on (off: nothing is recorded and no /who is sent; saved permanently)", 14, scanTop - 122,
        function() return db.enabled end,
        function(v) ForeverPlayerStatistics_SetEnabled(v) end)
    panel.checks[#panel.checks + 1] = CreateCheck(panel, "/who search on (off: only targets / mouseover are recorded; saved permanently)", 14, scanTop - 146,
        function() return db.whoEnabled end,
        function(v) ForeverPlayerStatistics_SetWhoEnabled(v) end)
    panel.checks[#panel.checks + 1] = CreateCheck(panel, "Pause the /who search until I log out (not saved)", 14, scanTop - 170,
        function() return whoPaused end,
        function(v) ForeverPlayerStatistics_SetWhoPaused(v) end)

    StaticPopupDialogs["FOREVERPLAYERSTATISTICS_RESET"] = {
        text = "Delete all %s players from the ForeverPlayerStatistics database?",
        button1 = YES,
        button2 = NO,
        OnAccept = function()
            wipe(db.players)
            Print("database cleared.")
            RefreshPanel()
        end,
        timeout = 0,
        whileDead = true,
        hideOnEscape = true,
    }
    local reset = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    reset:SetSize(120, 22)
    reset:SetPoint("TOPRIGHT", -20, scanTop - 52)
    reset:SetText("Reset database")
    reset:SetScript("OnClick", function()
        StaticPopup_Show("FOREVERPLAYERSTATISTICS_RESET", Num(PlayerCount()))
    end)

    local help = panel:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
    help:SetPoint("BOTTOMLEFT", 20, 16)
    help:SetWidth(INNER_W)
    help:SetJustifyH("LEFT")
    help:SetText("The scan runs until you press Stop. The game only allows /who on a key press or click, so each query is sent with your next key press or click in the world. Scanning a player again replaces the stored data of that player.")

    panel:SetScript("OnShow", RefreshPanel)
end

local function TogglePanel()
    if panel:IsShown() then panel:Hide() else panel:Show() end
end

---------------------------------------------------------------------------
-- Entry in Esc -> Options -> AddOns
---------------------------------------------------------------------------

local function Metadata(field)
    return C_AddOns.GetAddOnMetadata(ADDON, field)
end

local function CreateInfoPanel()
    local info = CreateFrame("Frame", "ForeverPlayerStatisticsInfoPanel")
    info.name = ADDON

    local title = info:CreateFontString(nil, "ARTWORK", "GameFontNormalLarge")
    title:SetPoint("TOPLEFT", 16, -16)
    title:SetText(ADDON)

    local notes = info:CreateFontString(nil, "ARTWORK", "GameFontHighlight")
    notes:SetPoint("TOPLEFT", title, "BOTTOMLEFT", 0, -8)
    notes:SetWidth(520)
    notes:SetJustifyH("LEFT")
    notes:SetText(Metadata("Notes") or "")

    local last = notes
    for _, l in ipairs({ { "Author", Metadata("Author") }, { "Version", Metadata("Version") } }) do
        local fs = info:CreateFontString(nil, "ARTWORK", "GameFontHighlight")
        fs:SetPoint("TOPLEFT", last, "BOTTOMLEFT", 0, -12)
        fs:SetText("|cffffd100" .. l[1] .. ":|r " .. (l[2] or "?"))
        last = fs
    end

    for _, l in ipairs({ { "GitHub", Metadata("X-Source") }, { "CurseForge", Metadata("X-Website") } }) do
        local url = l[2]
        if url and url ~= "" then
            local label = info:CreateFontString(nil, "ARTWORK", "GameFontNormal")
            label:SetPoint("TOPLEFT", last, "BOTTOMLEFT", 0, -14)
            label:SetText(l[1] .. " (Ctrl+C to copy):")
            local box = CreateFrame("EditBox", nil, info, "InputBoxTemplate")
            box:SetSize(480, 20)
            box:SetPoint("TOPLEFT", label, "BOTTOMLEFT", 6, -4)
            box:SetAutoFocus(false)
            box:SetText(url)
            box:SetCursorPosition(0)
            box:SetScript("OnEditFocusLost", function(self) self:SetText(url); self:HighlightText(0, 0) end)
            box:SetScript("OnEscapePressed", box.ClearFocus)
            last = box
        end
    end

    -- permanent switches (saved in the database)
    local checks = {}
    checks[1] = CreateCheck(info, "Addon on (off: nothing is recorded and no /who is sent)", 12, -10,
        function() return db.enabled end,
        function(v) ForeverPlayerStatistics_SetEnabled(v) end)
    checks[1]:ClearAllPoints()
    checks[1]:SetPoint("TOPLEFT", last, "BOTTOMLEFT", -4, -16)
    checks[2] = CreateCheck(info, "/who search on (off: only targets / mouseover are recorded)", 12, -10,
        function() return db.whoEnabled end,
        function(v) ForeverPlayerStatistics_SetWhoEnabled(v) end)
    checks[2]:ClearAllPoints()
    checks[2]:SetPoint("TOPLEFT", checks[1], "BOTTOMLEFT", 0, -2)
    checks[3] = CreateCheck(info, "Pause the /who search until I log out (not saved)", 12, -10,
        function() return whoPaused end,
        function(v) ForeverPlayerStatistics_SetWhoPaused(v) end)
    checks[3]:ClearAllPoints()
    checks[3]:SetPoint("TOPLEFT", checks[2], "BOTTOMLEFT", 0, -2)
    info:SetScript("OnShow", function()
        for _, cb in ipairs(checks) do cb:Refresh() end
    end)
    last = checks[3]

    local open = CreateFrame("Button", nil, info, "UIPanelButtonTemplate")
    open:SetSize(160, 24)
    open:SetPoint("TOPLEFT", last, "BOTTOMLEFT", 4, -20)
    open:SetText("Open statistics")
    open:SetScript("OnClick", function()
        if HideUIPanel and GameMenuFrame then HideUIPanel(GameMenuFrame) end
        if SettingsPanel and SettingsPanel:IsShown() then HideUIPanel(SettingsPanel) end
        panel:Show()
    end)

    local category = Settings.RegisterCanvasLayoutCategory(info, ADDON)
    Settings.RegisterAddOnCategory(category)
end

---------------------------------------------------------------------------
-- Minimap button
---------------------------------------------------------------------------

local function CreateMinimapButton()
    -- Keep the button outside the minimap; WoW Forever clips minimap child frames.
    bar = CreateFrame("Button", "ForeverPlayerStatisticsMinimapButton", UIParent)
    bar:SetSize(31, 31)
    bar:SetFrameStrata("MEDIUM")
    bar:SetFrameLevel(8)
    bar:RegisterForClicks("LeftButtonUp", "RightButtonUp")
    bar:RegisterForDrag("LeftButton")

    local border = bar:CreateTexture(nil, "OVERLAY")
    border:SetTexture("Interface\\Minimap\\MiniMap-TrackingBorder")
    border:SetSize(53, 53)
    border:SetPoint("TOPLEFT")

    local icon = bar:CreateTexture(nil, "ARTWORK")
    icon:SetTexture("Interface\\Icons\\INV_Misc_Spyglass_03")
    icon:SetSize(20, 20)
    icon:SetPoint("TOPLEFT", 6, -5)
    icon:SetTexCoord(0.08, 0.92, 0.08, 0.92)
    bar.icon = icon
    if icon.SetDesaturated then icon:SetDesaturated(not db.enabled) end -- grey while the addon is off

    bar:SetHighlightTexture("Interface\\Minimap\\UI-Minimap-ZoomButton-Highlight")

    local function UpdatePosition()
        local angle = math.rad(db.minimapAngle)
        local radius = (Minimap:GetWidth() / 2) + 5
        bar:ClearAllPoints()
        bar:SetPoint("CENTER", Minimap, "CENTER", math.cos(angle) * radius, math.sin(angle) * radius)
    end
    UpdatePosition()

    bar:SetScript("OnDragStart", function(self)
        self:SetScript("OnUpdate", function()
            local mx, my = Minimap:GetCenter()
            local scale = Minimap:GetEffectiveScale()
            local cx, cy = GetCursorPosition()
            db.minimapAngle = math.deg(math.atan2(cy / scale - my, cx / scale - mx))
            UpdatePosition()
        end)
    end)
    bar:SetScript("OnDragStop", function(self) self:SetScript("OnUpdate", nil) end)

    local function ShowTooltip(self)
        local s = ComputeStats()
        local a, h = s.faction.Alliance or 0, s.faction.Horde or 0
        GameTooltip:SetOwner(self, "ANCHOR_LEFT")
        GameTooltip:AddLine("ForeverPlayerStatistics")
        GameTooltip:AddLine("Players in database: " .. Num(PlayerCount()), 1, 1, 1)
        if a + h > 0 then
            GameTooltip:AddLine(string.format("Alliance %s  -  Horde %s", Pct(a, a + h), Pct(h, a + h)), 1, 1, 1)
        end
        if not db.enabled then
            GameTooltip:AddLine("Addon |cffff4040off|r: nothing is recorded (/fps on)", 1, 1, 1)
        elseif not db.whoEnabled then
            GameTooltip:AddLine("/who search |cffff4040off|r (/fps who on)", 1, 1, 1)
        elseif whoPaused then
            GameTooltip:AddLine("/who search |cffffd100paused until logout|r (/fps who resume)", 1, 1, 1)
        elseif db.autoScan then
            GameTooltip:AddLine(string.format("Scan |cff00ff00running|r: pass %d, %d queries left, %s players found",
                db.scanPass or 0, #scan.queue, Num(scan.foundCount)), 1, 1, 1)
        else
            GameTooltip:AddLine("Scan |cffff4040stopped|r", 1, 1, 1)
        end
        GameTooltip:AddLine("Left-click: overview", 0.7, 0.7, 0.7)
        GameTooltip:AddLine("Right-click: start the scan / send the next query now", 0.7, 0.7, 0.7)
        GameTooltip:AddLine("Drag to move around the minimap.", 0.7, 0.7, 0.7)
        GameTooltip:Show()
    end

    bar:SetScript("OnClick", function(self, button)
        if button == "RightButton" then
            ScanNext(true)
            if GameTooltip:IsOwned(self) then ShowTooltip(self) end
        else
            TogglePanel()
        end
    end)
    bar:SetScript("OnEnter", ShowTooltip)
    bar:SetScript("OnLeave", GameTooltip_Hide)
end

---------------------------------------------------------------------------
-- Events
---------------------------------------------------------------------------

-- drives the scan button countdown and the timeout of unanswered queries
local ticker = CreateFrame("Frame")
local tickElapsed = 0
ticker:SetScript("OnUpdate", function(_, elapsed)
    tickElapsed = tickElapsed + elapsed
    if tickElapsed < 0.2 or not db then return end
    tickElapsed = 0
    CheckTimeout()
    UpdateScanUI()
end)

local f = CreateFrame("Frame")
eventFrame = f
f:RegisterEvent("ADDON_LOADED")
f:RegisterEvent("PLAYER_LOGIN")
f:SetScript("OnEvent", function(_, event, arg1)
    if event == "ADDON_LOADED" and arg1 == ADDON then
        ForeverPlayerStatisticsDB = ForeverPlayerStatisticsDB or {}
        db = ForeverPlayerStatisticsDB
        CopyDefaults(defaults, db)
        LoadPlayers()
        -- continue the pass that was running before logout / reload
        scan.queue = db.scanQueue
        -- data of the old class / race split scan, no longer used
        db.scanLeaves, db.lastLeaves, db.fullLevels, db.whoRaceNames = nil, nil, nil, nil
        if HasOldQueries(scan.queue) then wipe(scan.queue) end -- pass saved by an older version
        scan.active = #scan.queue > 0
        f:UnregisterEvent("ADDON_LOADED")
        f:RegisterEvent("PLAYER_LOGOUT")
    elseif event == "PLAYER_LOGOUT" then
        SavePlayers()
    elseif event == "PLAYER_LOGIN" then
        BuildClassLookup()
        BuildRaceLookup()
        -- records saved with a race name that was not recognised then (e.g. Skyborne)
        local myRealm, moved = MyRealm(), {}
        for key, p in pairs(db.players) do
            if p.race and not RACE_NAMES[p.race] then p.race = ResolveRace(p.race) end
            p.zone = EnglishZone(p.zone) -- older records kept the German zone name
            p.realmType = nil -- no longer stored
            if p.realm ~= myRealm and p.name then
                if p.realm == NormalizedRealm(myRealm) then
                    p.realm = myRealm -- older versions removed spaces and dashes
                    moved[key] = p
                elseif p.realm and not p.realm:find("%d") then
                    -- older target records stored the last name as realm
                    p.name, p.realm = p.name .. " " .. p.realm, myRealm
                    moved[key] = p
                end
            end
        end
        for oldKey, p in pairs(moved) do
            db.players[oldKey] = nil
            local newKey = p.name .. "-" .. p.realm
            local other = db.players[newKey]
            if not other or (other.seen or 0) < (p.seen or 0) then
                if other then p.firstSeen = math.min(p.firstSeen or p.seen, other.firstSeen or p.seen) end
                db.players[newKey] = p
            end
        end
        InstallChatFilter()
        GuardWhoWindow()
        if hooksecurefunc and C_FriendList and C_FriendList.SendWho then
            hooksecurefunc(C_FriendList, "SendWho", OnAnySendWho)
        end
        CreateMinimapButton()
        CreatePanel()
        CreateInfoPanel()

        f:RegisterEvent("WHO_LIST_UPDATE")
        f:RegisterEvent("PLAYER_TARGET_CHANGED")
        f:RegisterEvent("UPDATE_MOUSEOVER_UNIT")
        f:RegisterEvent("PLAYER_REGEN_ENABLED")
        CreateAutoTrigger()

        Print(string.format("loaded. %s players in the database. Click the minimap spyglass or type /fps for the overview.",
            Num(PlayerCount())))
        if not db.enabled then
            Print("|cffff4040switched off|r - nothing is recorded. /fps on (or the options) to switch it on.")
        elseif not db.whoEnabled then
            Print("/who search |cffff4040switched off|r - only targets / mouseover are recorded. /fps who on to switch it on.")
        else
        Print("player scan: " .. (db.autoScan
            and "|cff00ff00running|r - a /who query is sent with your key presses / clicks every few seconds. /fps stop to stop."
            or "|cffff4040stopped|r - right-click the minimap button or /fps start to start it."))
        end
    elseif event == "PLAYER_REGEN_ENABLED" then
        CreateAutoTrigger() -- if the login happened in combat
    elseif event == "WHO_LIST_UPDATE" then
        OnWhoListUpdate()
    elseif event == "PLAYER_TARGET_CHANGED" then
        RecordUnit("target")
    elseif event == "UPDATE_MOUSEOVER_UNIT" then
        RecordUnit("mouseover")
    end
end)

-- key bindings (Bindings.xml)
BINDING_HEADER_FOREVERPLAYERSTATISTICS = "ForeverPlayerStatistics"
BINDING_NAME_FOREVERPLAYERSTATISTICS_SCAN = "Send next /who scan query"
BINDING_NAME_FOREVERPLAYERSTATISTICS_TOGGLE = "Show / hide statistics"

function ForeverPlayerStatistics_ScanNext()
    ScanNext(false)
end

-- Switches the whole addon on / off. Saved permanently in the database.
function ForeverPlayerStatistics_SetEnabled(on)
    db.enabled = on and true or false
    if bar and bar.icon and bar.icon.SetDesaturated then bar.icon:SetDesaturated(not db.enabled) end
    Print(db.enabled and "switched |cff00ff00on|r." or "switched |cffff4040off|r: nothing is recorded and no /who is sent until you switch it on again.")
    if RefreshPanel then RefreshPanel() end
end

-- Switches the /who search on / off. Saved permanently in the database.
function ForeverPlayerStatistics_SetWhoEnabled(on)
    db.whoEnabled = on and true or false
    Print(db.whoEnabled and "/who search switched |cff00ff00on|r." or "/who search switched |cffff4040off|r: only targets / mouseover are recorded.")
    if RefreshPanel then RefreshPanel() end
end

-- Pauses the /who search until logout / reload. Not saved.
function ForeverPlayerStatistics_SetWhoPaused(on)
    whoPaused = on and true or false
    Print(whoPaused and "/who search |cffffd100paused until you log out|r." or "/who search |cff00ff00resumed|r.")
    if RefreshPanel then RefreshPanel() end
end

function ForeverPlayerStatistics_Toggle()
    if panel then TogglePanel() end
end

SLASH_FOREVERPLAYERSTATISTICS1 = "/fps"
SLASH_FOREVERPLAYERSTATISTICS2 = "/playerstats"
SlashCmdList["FOREVERPLAYERSTATISTICS"] = function(msg)
    local cmd, rest = (msg or ""):lower():match("^%s*(%S*)%s*(.-)%s*$")
    if cmd == "scan" or cmd == "start" then
        ScanNext(true)
    elseif cmd == "stop" then
        StopScan()
    elseif cmd == "debugwho" then
        -- lists every frame that reacts to /who results (to find what opens the Who window)
        local frames = GetFramesRegisteredForEvent and { GetFramesRegisteredForEvent("WHO_LIST_UPDATE") } or {}
        Print(#frames .. " frame(s) listen to WHO_LIST_UPDATE:")
        for _, frame in ipairs(frames) do
            local name = frame.GetName and frame:GetName() or "?"
            Print("  " .. tostring(name) .. (frame == eventFrame and " (this addon)" or ""))
        end
    elseif cmd == "reset" then
        StaticPopup_Show("FOREVERPLAYERSTATISTICS_RESET", Num(PlayerCount()))
    elseif cmd == "cooldown" then
        local n = tonumber(rest)
        if n and n >= 1 then db.whoCooldown = n end
        Print("seconds between /who queries: " .. db.whoCooldown .. " (change with /fps cooldown <seconds>)")
    elseif cmd == "on" or cmd == "off" then
        ForeverPlayerStatistics_SetEnabled(cmd == "on")
    elseif cmd == "who" and (rest == "on" or rest == "off") then
        ForeverPlayerStatistics_SetWhoEnabled(rest == "on")
    elseif cmd == "who" and (rest == "pause" or rest == "resume") then
        ForeverPlayerStatistics_SetWhoPaused(rest == "pause")
    elseif cmd == "deep" then
        db.deepSearch = not db.deepSearch
        Print("deep search " .. OnOff(db.deepSearch) .. ".")
        RefreshPanel()
    elseif cmd == "help" then
        Print("/fps - overview  |  /fps start - start the scan / send the next query now  |  /fps stop - stop the scan  |  /fps reset - clear the database  |  /fps cooldown <seconds>  |  /fps deep - deep search on/off  |  /fps on|off - addon on/off  |  /fps who on|off - /who search on/off  |  /fps who pause|resume - pause until logout")
        Print("Addon: " .. OnOff(db.enabled) .. "   /who search: " .. OnOff(db.whoEnabled))
        Print("Recording targets/mouseover: " .. OnOff(db.recordUnits) .. "   own /who searches: " .. OnOff(db.recordOwnWho))
    elseif panel then
        TogglePanel()
    end
end
