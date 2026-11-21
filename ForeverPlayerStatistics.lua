-- ForeverPlayerStatistics
-- Collects player statistics from /who searches (and from players you target or
-- mouse over) into an account-wide database and shows an overview of classes,
-- races, factions and levels.

local ADDON = "ForeverPlayerStatistics"

local defaults = {
    enabled = true,        -- false: the addon records nothing and sends no /who (statistics can still be viewed)
    whoEnabled = true,     -- false: no /who scan at all; targets / mouseover are still recorded
    minimapAngle = 235,    -- degrees around the minimap
    bgMinimapAngle = 205,  -- position of the battleground minimap button
    bgMinimapShown = true, -- show the battleground minimap button
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
    chatTooltip = true,    -- tooltip with the stored data when the mouse is over a player name in chat
    chatRefresh = true,    -- hovering a name in chat queues a /who refresh of that player
    bgTrack = true,        -- record every player at the end of each battleground (ForeverPlayerStatisticsBG)
    bgMap = "ALL",         -- battleground window filters
    bgBracket = "ALL",
    bgTeam = "ALL",
    listView = "count",    -- overview: class / race lists show "count" or "level" (average / median level)
    -- rangeLo, rangeHi: level range of the overview (nil = all levels)
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

-- Refresh of a single player (hovering a name in chat): lookup = { name = "First Last" }
-- is sent as /who n-"First Last" before the next scan query. lookupDone[name] =
-- { time = time(), found = true/false } for the answers of this session.
local lookup = nil
local lookupDone = {}
local LOOKUP_AGAIN = 60 -- seconds before the same player is looked up again

local RefreshPanel, UpdateScanUI, RefreshChatTooltip

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

-- Name of the WoW Forever super server, exactly as the game shows it (e.g. "CAMWOW EU5 Realm 5 PvE").
-- On some logins GetRealmName() returns an empty string. Then the last known
-- name (db.lastRealm) is used, so players are never stored without a realm.
local function MyRealm()
    local r = GetRealmName and GetRealmName()
    if r and r ~= "" then
        if db then db.lastRealm = r end
        return r
    end
    if db and db.lastRealm and db.lastRealm ~= "" then return db.lastRealm end
    r = GetNormalizedRealmName and GetNormalizedRealmName()
    if r and r ~= "" then return r end
    return "?"
end

-- true for a realm value that was stored while the realm name was unknown
local function BadRealm(realm)
    return realm == nil or realm == "" or realm == "?"
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

-- Counters for the statistics, kept up to date when a player is stored, so the
-- overview and tooltip never have to go through every player (with 100,000+
-- players that made the game stop the addon with "script ran too long").
-- cells[realm][faction][class][raceKey][level] = number of complete players
local cells = {}
local completeCount = 0

-- players in the database, without records that have something unknown
local function PlayerCount()
    return completeCount
end

---------------------------------------------------------------------------
-- Classes and races (localized names <-> file names)
---------------------------------------------------------------------------

local FALLBACK_CLASSES = { "WARRIOR", "PALADIN", "HUNTER", "ROGUE", "PRIEST", "SHAMAN", "MAGE", "WARLOCK", "DRUID" }
local classes = {}     -- { file = "MAGE", name = "Mage" } in game order
local classByName = {} -- lower-case localized name -> class file
local classSet = {}    -- class file -> true

local function BuildClassLookup()
    wipe(classes)
    wipe(classSet)
    local seen = {}
    local function add(file, name)
        if not file or seen[file] then return end
        seen[file] = true
        name = name or (LOCALIZED_CLASS_NAMES_MALE and LOCALIZED_CLASS_NAMES_MALE[file]) or file
        classes[#classes + 1] = { file = file, name = name }
        classSet[file] = true
        classByName[name:lower()] = file
        local female = LOCALIZED_CLASS_NAMES_FEMALE and LOCALIZED_CLASS_NAMES_FEMALE[file]
        if female then classByName[female:lower()] = file end
    end
    if GetNumClasses and GetClassInfo then
        -- class IDs have gaps in classic clients: the druid is ID 11, but
        -- GetNumClasses() returns fewer, so every ID up to 20 is checked
        for i = 1, math.max(GetNumClasses() or 0, 20) do
            local ok, name, file = pcall(GetClassInfo, i)
            if ok and file then add(file, name) end
        end
    end
    -- the classic classes are always known, even if the game does not list one
    for _, file in ipairs(FALLBACK_CLASSES) do add(file) end
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
    ["Warsongschlucht"] = "Warsong Gulch", ["Arathibecken"] = "Arathi Basin", ["Alteractal"] = "Alterac Valley",
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
    if classSet[p.class] then return true end
    return #classes == 0 and RAID_CLASS_COLORS ~= nil and RAID_CLASS_COLORS[p.class] ~= nil
end

-- race key used in the statistics: races on both factions (Skyborne) are counted
-- per faction, e.g. "Skyborne:Horde"
local function RaceKey(p)
    local r = p.race or "?"
    if RACE_NAMES[r] and not RACE_FACTION[r] and p.faction then r = r .. ":" .. p.faction end
    return r
end

-- adds (d = 1) or removes (d = -1) a player in the counters
local function CountPlayer(p, d)
    if not p or not IsComplete(p) then return end
    local level, realm, race = tonumber(p.level), p.realm or "?", RaceKey(p)
    local byFaction = cells[realm]
    if not byFaction then byFaction = {}; cells[realm] = byFaction end
    local byClass = byFaction[p.faction]
    if not byClass then byClass = {}; byFaction[p.faction] = byClass end
    local byRace = byClass[p.class]
    if not byRace then byRace = {}; byClass[p.class] = byRace end
    local t = byRace[race]
    if not t then t = {}; byRace[race] = t end
    t[level] = (t[level] or 0) + d
    if t[level] <= 0 then t[level] = nil end
    completeCount = completeCount + d
end

-- counts every player once (after login and after the database changed as a whole)
local function RebuildCounts()
    wipe(cells)
    completeCount = 0
    for _, p in pairs(db.players) do CountPlayer(p, 1) end
end

-- Returns nil if the record is ignored because something is unknown.
local function StorePlayer(p)
    local key = p.name .. "-" .. p.realm
    local old = db.players[key]
    if old and not p.level then p.level = old.level end -- "??" level of a much higher player
    if not IsComplete(p) then return nil, false end -- keep the old record, if any
    p.seen = time()
    p.firstSeen = old and old.firstSeen or p.seen
    CountPlayer(old, -1)
    CountPlayer(p, 1)
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
            -- players saved without realm (realm name was unknown) are kept; the realm is set after login
            if p.name then
                p.realm = p.realm or ""
                players[p.name .. "-" .. p.realm] = p
            end
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
    if q.name then return 'n-"' .. q.name .. '"' end -- refresh of one player
    local t = q.lo .. "-" .. q.hi
    if q.letter then t = t .. ' n-"' .. q.letter .. '"' end
    return t
end

-- queries from older versions of the addon (level ranges, class / race / name filters)
local function HasOldQueries(list)
    for _, q in ipairs(list) do
        if q.hi ~= q.lo or q.class or q.race or q.name then return true end
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

-- Sends one query in the background. Must be called from a key press or click.
local function SendQuery(q)
    q.sent = GetTime()
    scan.pending = q
    scan.lastSend = q.sent
    if not q.name then scan.sent = scan.sent + 1 end
    SuppressWhoUI()
    SetWhoToUi(true)
    local ok, err = pcall(SendWhoQuery, QueryText(q))
    if not ok then
        scan.pending = nil
        if q.name then
            lookup = lookup or { name = q.name }
        else
            table.insert(scan.queue, 1, q)
        end
        RestoreWhoUI()
        Print("|cffff4040could not send /who:|r " .. tostring(err))
    end
    UpdateScanUI()
    if q.name and RefreshChatTooltip then RefreshChatTooltip() end
end

-- Sends the next query. Must be called from a key press or click.
-- A player refresh (hovered name in chat) goes first.
-- Sending manually also (re)starts the automatic scan.
local function ScanNext(verbose)
    if not db then return end
    if lookup and CanWho() and not scan.pending and CooldownLeft() == 0 then
        local q = { name = lookup.name }
        lookup = nil
        SendQuery(q)
        return
    end
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
    SendQuery(q)
end

-- Called on every key press and every click into the game world.
-- A player refresh is sent even while the scan is stopped.
local function AutoScanTrigger()
    if CanWho() and (db.autoScan or lookup) and not scan.pending and CooldownLeft() == 0 then
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
    local num, total = RecordWhoResults(q ~= nil and not q.name)
    if q and q.name then
        -- answer to a player refresh: found if the player was just stored again
        scan.pending = nil
        RestoreWhoUI()
        local p = db.players[q.name .. "-" .. MyRealm()]
        local found = p ~= nil and p.source == "who" and time() - (p.seen or 0) <= 2
        lookupDone[q.name] = { time = time(), found = found }
        scan.lastResult = string.format("%s: %s", QueryText(q), found and "updated" or "not online")
        UpdateScanUI()
        RequestRefresh()
        if RefreshChatTooltip then RefreshChatTooltip() end
        return
    end
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
        if q.name then
            lookup = lookup or { name = q.name } -- player refresh: try again (unless another player was hovered since)
        else
            table.insert(scan.queue, 1, { lo = q.lo, hi = q.hi })
            scan.active = true
        end
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

-- Level range of the overview (range bar below the histogram), saved in
-- db.rangeLo / db.rangeHi. nil means "from level 1" / "up to the highest level".
local function LevelRange()
    return db.rangeLo or 1, db.rangeHi or math.huge
end

local function RangeActive()
    return db.rangeLo ~= nil or db.rangeHi ~= nil
end

-- number of players, average and median level of a { [level] = count } table,
-- only levels lo..hi are counted
local function LevelStats(hist, lo, hi)
    lo, hi = lo or 1, hi or math.huge
    local n, sum, maxL = 0, 0, 0
    for l, c in pairs(hist) do
        if l >= lo and l <= hi and c > 0 then
            n = n + c
            sum = sum + l * c
            if l > maxL then maxL = l end
        end
    end
    if n == 0 then return 0 end
    -- median: middle player (mean of the two middle players for an even count)
    local k1, k2 = math.floor((n + 1) / 2), math.floor(n / 2) + 1
    local acc, m1, m2 = 0, nil, nil
    for l = math.max(lo, 1), maxL do
        acc = acc + (hist[l] or 0)
        if not m1 and acc >= k1 then m1 = l end
        if acc >= k2 then m2 = l; break end
    end
    return n, sum / n, ((m1 or m2) + m2) / 2
end

-- "34.5" / "36" (no ".0")
local function FmtLevel(v)
    if not v then return "-" end
    if v == math.floor(v) then return tostring(v) end
    return string.format("%.1f", v)
end

-- ignoreRange: count every level (used by the minimap tooltip)
local function ComputeStats(ignoreRange)
    local s = {
        total = 0, faction = {}, factionTotal = 0,
        class = {}, classTotal = 0, race = {}, raceTotal = 0,
        level = {}, levelTotal = 0, maxLevel = 0,
        classLevels = {}, raceLevels = {}, -- [class or race][level] = count, for average / median
    }
    local myRealm = MyRealm()
    local lo, hi = 1, math.huge
    if not ignoreRange then lo, hi = LevelRange() end
    -- only complete records are counted (see CountPlayer)
    for realm, byFaction in pairs(cells) do
        if not db.filterRealm or realm == myRealm then
            for f, byClass in pairs(byFaction) do
                local showFaction = db.filterFaction == "ALL" or f == db.filterFaction
                for c, byRace in pairs(byClass) do
                    for r, byLevel in pairs(byRace) do
                        for l, n in pairs(byLevel) do
                            local inRange = l >= lo and l <= hi
                            if inRange then
                                s.faction[f] = (s.faction[f] or 0) + n
                                s.factionTotal = s.factionTotal + n
                            end
                            if showFaction then
                                local okLevel = inRange and (not sel.level or l == sel.level)
                                local okClass = not sel.class or c == sel.class
                                local okRace = not sel.race or r == sel.race
                                if okLevel and okClass and okRace then s.total = s.total + n end
                                if okLevel and okRace then
                                    s.class[c] = (s.class[c] or 0) + n
                                    s.classTotal = s.classTotal + n
                                    local h = s.classLevels[c]
                                    if not h then h = {}; s.classLevels[c] = h end
                                    h[l] = (h[l] or 0) + n
                                end
                                if okLevel and okClass then
                                    s.race[r] = (s.race[r] or 0) + n
                                    s.raceTotal = s.raceTotal + n
                                    local h = s.raceLevels[r]
                                    if not h then h = {}; s.raceLevels[r] = h end
                                    h[l] = (h[l] or 0) + n
                                end
                                if okClass and okRace and l > 0 then
                                    s.level[l] = (s.level[l] or 0) + n
                                    s.levelTotal = s.levelTotal + n
                                end
                                if l > s.maxLevel then s.maxLevel = l end
                            end
                        end
                    end
                end
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

local W, H = 600, 885
local INNER_W = W - 40
local ROWS = 12
local ROW_H = 16
local ROW_BAR_W = 100
local HIST_H = 90

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
            if r.levelText then GameTooltip:AddLine(r.levelText, 1, 1, 1) end
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

-- nameOf(key) -> text; colorOf(key) -> r, g, b; selected = key of the selected row;
-- levels[key] = { [level] = count } for the average / median level
local function FillRows(rows, counts, total, nameOf, colorOf, selected, levels)
    if selected and not counts[selected] then counts[selected] = 0 end -- keep the selection visible
    local list = Sorted(counts, nameOf)
    for _, e in ipairs(list) do
        local _, avg, med = LevelStats(levels[e.key] or {})
        e.avg, e.med = avg, med
    end
    local levelView = db.listView == "level"
    if levelView and not db.sortByName then
        -- highest average level first
        table.sort(list, function(a, b)
            if (a.avg or 0) ~= (b.avg or 0) then return (a.avg or 0) > (b.avg or 0) end
            return tostring(a.key) < tostring(b.key)
        end)
    end
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
            local rest, merged = 0, {}
            for j = ROWS, #list do
                rest = rest + list[j].n
                for l, c in pairs(levels[list[j].key] or {}) do merged[l] = (merged[l] or 0) + c end
            end
            local _, avg, med = LevelStats(merged)
            e = { key = false, n = rest, avg = avg, med = med }
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
            r.levelText = e.avg and ("Average level " .. FmtLevel(math.floor(e.avg * 10 + 0.5) / 10)
                .. ", median level " .. FmtLevel(e.med)) or nil
            r.name:SetText(r.label)
            r.name:SetTextColor(cr, cg, cb)
            SetColor(r.bar, cr, cg, cb, 0.85)
            if levelView then
                -- bar: average level compared to the highest level
                local frac = e.avg and e.avg / math.max(1, MaxLevel()) or 0
                r.bar:SetWidth(math.max(1, ROW_BAR_W * math.min(1, frac)))
                r.value:SetText(e.avg and string.format("%.1f  |cffaaaaaa%s|r", e.avg, FmtLevel(e.med)) or "-")
            else
                r.bar:SetWidth(math.max(1, ROW_BAR_W * math.min(1, e.n / maxN)))
                r.value:SetText(Num(e.n) .. "  " .. Pct(e.n, total))
            end
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
    local rangeLo, rangeHi = LevelRange()
    rangeHi = math.min(rangeHi, n)
    rangeLo = math.min(rangeLo, rangeHi)
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
                SetColor(self.tex, self.cr, self.cg, self.cb, self.alpha)
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
        -- levels outside the level range are dimmed
        b.alpha = (l >= rangeLo and l <= rangeHi) and 0.9 or 0.2
        SetColor(b.tex, b.cr, b.cg, b.cb, b.alpha)
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

    -- level range bar: handles at the first and last level of the range
    local rb = panel.rangeBar
    rb.n, rb.bw = n, bw
    rb.fill:ClearAllPoints()
    rb.fill:SetPoint("TOPLEFT", rb, "TOPLEFT", (rangeLo - 1) * bw, -4)
    rb.fill:SetSize(math.max(1, (rangeHi - rangeLo + 1) * bw), 6)
    rb.loHandle:ClearAllPoints()
    rb.loHandle:SetPoint("CENTER", rb, "LEFT", (rangeLo - 1) * bw, 0)
    rb.hiHandle:ClearAllPoints()
    rb.hiHandle:SetPoint("CENTER", rb, "LEFT", rangeHi * bw, 0)

    -- average and median level of the players in the histogram (class / race / faction filter, level range)
    local count, avg, med = LevelStats(s.level, rangeLo, rangeHi)
    local rangeText = (rangeLo <= 1 and rangeHi >= n) and "all levels"
        or string.format("levels |cffffffff%d - %d|r", rangeLo, rangeHi)
    panel.rangeText:SetText("Level range: " .. rangeText .. "  |cff888888(drag; right-click: all)|r")
    if count > 0 then
        panel.levelInfo:SetText(string.format("Average level |cffffffff%.1f|r   Median |cffffffff%s|r   (%s players)",
            avg, FmtLevel(med), Num(count)))
    else
        panel.levelInfo:SetText("no players in this range")
    end

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
    FillRows(panel.classRows, s.class, s.classTotal, ClassLabel, ClassColor, sel.class, s.classLevels)
    FillRows(panel.raceRows, s.race, s.raceTotal, RaceLabel, RaceColor, sel.race, s.raceLevels)
    RefreshHistogram(s)

    -- headers show what the lists are filtered by
    local lvl = sel.level and ("level " .. sel.level) or nil
    if not lvl and RangeActive() then
        local lo, hi = LevelRange()
        lvl = hi == math.huge and ("level " .. lo .. "+") or ("levels " .. lo .. "-" .. hi)
    end
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
    local levelView = db.listView == "level"
    panel.sortBtn:SetText(db.sortByName and "Sort: name" or (levelView and "Sort: level" or "Sort: count"))
    panel.viewBtn:SetText(levelView and "Show: level" or "Show: count")
    panel.listHint:SetText(levelView and "average  |cffaaaaaamedian|r" or "")
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
    -- class / race lists: number of players or average / median level
    panel.viewBtn = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    panel.viewBtn:SetSize(100, 22)
    panel.viewBtn:SetPoint("TOPRIGHT", -216, -62)
    panel.viewBtn:SetScript("OnClick", function()
        db.listView = db.listView == "level" and "count" or "level"
        RefreshPanel()
    end)
    panel.viewBtn:SetScript("OnEnter", function(self)
        GameTooltip:SetOwner(self, "ANCHOR_TOP")
        GameTooltip:AddLine("Class and race lists")
        GameTooltip:AddLine("count: number of players and share", 1, 1, 1)
        GameTooltip:AddLine("level: average and median level", 1, 1, 1)
        GameTooltip:Show()
    end)
    panel.viewBtn:SetScript("OnLeave", GameTooltip_Hide)
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
    panel.listHint = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
    panel.listHint:SetPoint("TOPRIGHT", -20, -160)
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

    -- level range bar: drag the handles to count only levels X to Y
    local rb = CreateFrame("Frame", nil, panel)
    rb:SetSize(INNER_W, 14)
    rb:SetPoint("TOPLEFT", hist, "BOTTOMLEFT", 0, -18)
    rb:EnableMouse(true)
    rb.bg = rb:CreateTexture(nil, "BACKGROUND")
    rb.bg:SetPoint("TOPLEFT", 0, -4)
    rb.bg:SetSize(INNER_W, 6)
    SetColor(rb.bg, 0, 0, 0, 0.5)
    rb.fill = rb:CreateTexture(nil, "ARTWORK")
    SetColor(rb.fill, 1, 0.82, 0, 0.7)
    local function Handle()
        local h = rb:CreateTexture(nil, "OVERLAY")
        h:SetSize(6, 14)
        SetColor(h, 1, 1, 1, 1)
        return h
    end
    rb.loHandle, rb.hiHandle = Handle(), Handle()
    rb.n, rb.bw = MaxLevel(), INNER_W / MaxLevel()

    -- level under the mouse, as a handle position (0 .. n): lo handle = level + 1, hi handle = level
    local function CursorPos()
        local x = GetCursorPosition() / rb:GetEffectiveScale() - rb:GetLeft()
        return math.max(0, math.min(rb.n, math.floor(x / rb.bw + 0.5)))
    end
    local function SetRange(lo, hi)
        lo = math.max(1, math.min(lo, rb.n))
        hi = math.max(lo, math.min(hi, rb.n))
        local newLo = lo > 1 and lo or nil
        local newHi = hi < rb.n and hi or nil
        if newLo == db.rangeLo and newHi == db.rangeHi then return end
        db.rangeLo, db.rangeHi = newLo, newHi
        if sel.level and (sel.level < lo or sel.level > hi) then sel.level = nil end
        RefreshPanel()
    end
    rb:SetScript("OnMouseDown", function(self, button)
        if button == "RightButton" then
            db.rangeLo, db.rangeHi = nil, nil
            RefreshPanel()
            return
        end
        -- the handle nearer to the mouse is dragged
        local pos = CursorPos()
        local lo, hi = LevelRange()
        hi = math.min(hi, self.n)
        self.dragging = math.abs(pos - (lo - 1)) <= math.abs(pos - hi) and "lo" or "hi"
        self:SetScript("OnUpdate", function()
            if not IsMouseButtonDown("LeftButton") then
                self.dragging = nil
                self:SetScript("OnUpdate", nil)
                return
            end
            local p = CursorPos()
            local curLo, curHi = LevelRange()
            curHi = math.min(curHi, self.n)
            if self.dragging == "lo" then
                SetRange(math.min(p + 1, curHi), curHi)
            else
                SetRange(curLo, math.max(p, curLo))
            end
        end)
    end)
    rb:SetScript("OnMouseUp", function(self)
        self.dragging = nil
        self:SetScript("OnUpdate", nil)
    end)
    rb:SetScript("OnEnter", function(self)
        GameTooltip:SetOwner(self, "ANCHOR_BOTTOM")
        GameTooltip:AddLine("Level range")
        GameTooltip:AddLine("Drag a handle to count only the players from level X to Y.", 1, 1, 1)
        GameTooltip:AddLine("Factions, classes, races, average and median level use the range.", 1, 1, 1)
        GameTooltip:AddLine("Right-click: all levels", 0.6, 0.6, 0.6)
        GameTooltip:Show()
    end)
    rb:SetScript("OnLeave", GameTooltip_Hide)
    panel.rangeBar = rb

    panel.rangeText = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
    panel.rangeText:SetPoint("TOPLEFT", hist, "BOTTOMLEFT", 0, -36)
    panel.levelInfo = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
    panel.levelInfo:SetPoint("TOPRIGHT", hist, "BOTTOMRIGHT", 0, -36)

    panel.brackets = panel:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
    panel.brackets:SetPoint("TOPLEFT", hist, "BOTTOMLEFT", 0, -54)
    panel.brackets:SetWidth(INNER_W)
    panel.brackets:SetJustifyH("LEFT")

    -- scanning
    local scanTop = histTop - 20 - HIST_H - 92
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
    panel.checks[#panel.checks + 1] = CreateCheck(panel, "Show the stored data when the mouse is over a player name in chat", 14, scanTop - 194,
        function() return db.chatTooltip end,
        function(v) ForeverPlayerStatistics_SetChatTooltip(v) end)

    StaticPopupDialogs["FOREVERPLAYERSTATISTICS_RESET"] = {
        text = "Delete all %s players from the ForeverPlayerStatistics database?",
        button1 = YES,
        button2 = NO,
        OnAccept = function()
            wipe(db.players)
            RebuildCounts()
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
    local bgBtn = CreateFrame("Button", nil, panel, "UIPanelButtonTemplate")
    bgBtn:SetSize(120, 22)
    bgBtn:SetPoint("TOPRIGHT", -20, scanTop - 78)
    bgBtn:SetText("Battlegrounds")
    bgBtn:SetScript("OnClick", function() if ForeverPlayerStatistics_ToggleBG then ForeverPlayerStatistics_ToggleBG() end end)

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
-- Tooltip on player names in chat
--
-- Player names in chat are links ("player:Name:lineID:chatType:..."). When the
-- mouse is over one, the stored data of that player is shown in a tooltip.
-- WoW Forever names are "First Last"; the game puts the last name where the
-- realm usually is, so the link name can be "First-Last".
---------------------------------------------------------------------------

local function Ago(t)
    local d = time() - (t or 0)
    if d < 60 then return "just now" end
    if d < 3600 then return math.floor(d / 60) .. " min ago" end
    if d < 86400 then return math.floor(d / 3600) .. " h ago" end
    local days = math.floor(d / 86400)
    return days .. (days == 1 and " day ago" or " days ago")
end

-- link name -> stored record (or nil), and the "First Last" name for a /who refresh
local function FindPlayer(linkName)
    if not (db and db.players and linkName and linkName ~= "") then return end
    local realm = MyRealm()
    -- "First-Last", "First Last" or "First-Last-Realm"
    local spaced = linkName:gsub("%-", " ", 1)
    local withoutRealm = (linkName:match("^([^%-]+%-[^%-]+)%-") or ""):gsub("%-", " ", 1)
    for _, name in ipairs({ spaced, linkName, withoutRealm }) do
        if name ~= "" then
            local p = db.players[name .. "-" .. realm]
            if p then return p, p.name end
        end
    end
    return nil, withoutRealm ~= "" and withoutRealm or spaced
end

-- Queues a /who refresh of a hovered player. Returns a reason when no refresh is possible.
local function RequestLookup(name, p)
    if not (db.chatRefresh and name and name ~= "") then return "off" end
    if not CanWho() then return "nowho" end
    local myFaction = UnitFactionGroup("player")
    if p and p.faction and myFaction and p.faction ~= myFaction then return "faction" end
    if scan.pending and scan.pending.name == name then return end
    local done = lookupDone[name]
    if done and time() - done.time < LOOKUP_AGAIN then return end
    if p and p.source == "who" and time() - (p.seen or 0) < LOOKUP_AGAIN then return end
    lookup = { name = name } -- replaces the refresh of a player hovered before
end

local DAY = 86400
local hover -- { frame, link } of the name under the mouse

local function ShowChatPlayerTooltip(frame, link)
    if not (db and db.chatTooltip) or type(link) ~= "string" then return end
    local kind, rest = link:match("^(%a+):(.+)$")
    if kind ~= "player" then return end
    local linkName = rest:match("^([^:]+)")
    if not linkName or HasSecret(linkName) then return end
    local p, name = FindPlayer(linkName)
    hover = { frame = frame, link = link }
    local reason = RequestLookup(name, p)

    GameTooltip:SetOwner(frame, "ANCHOR_CURSOR")
    if not p then
        GameTooltip:AddLine(name or linkName)
        GameTooltip:AddLine("Not in the ForeverPlayerStatistics database yet", 0.6, 0.6, 0.6)
    else
        local cr, cg, cb = ClassColor(p.class)
        GameTooltip:AddLine(p.name, cr, cg, cb)
        GameTooltip:AddLine(string.format("Level %s %s %s", tostring(p.level or "?"), RaceName(p.race), ClassName(p.class)), 1, 1, 1)
        -- how old the level is; warning after one day
        local age = time() - (p.seen or 0)
        if age > DAY then
            GameTooltip:AddLine("(!) Level from " .. Ago(p.seen) .. " - may be outdated", 1, 0.5, 0)
        elseif age > 3600 then
            GameTooltip:AddLine("Level from " .. Ago(p.seen), 1, 1, 1)
        else
            GameTooltip:AddLine("Level from " .. Ago(p.seen), 0.25, 1, 0.25)
        end
        local fc = FACTION_COLORS[p.faction]
        if fc then GameTooltip:AddLine(p.faction, fc[1], fc[2], fc[3]) end
        if p.guild then GameTooltip:AddLine("<" .. p.guild .. ">", 0.25, 1, 0.25) end
        if p.zone then GameTooltip:AddLine(p.zone, 1, 0.82, 0) end
        GameTooltip:AddLine("Source: " .. (p.source == "unit" and "target / mouseover" or "/who"), 0.7, 0.7, 0.7)
        if p.firstSeen and p.firstSeen ~= p.seen then
            GameTooltip:AddLine("First seen: " .. date("%Y-%m-%d", p.firstSeen), 0.7, 0.7, 0.7)
        end
    end

    -- state of the /who refresh of this player
    local done = lookupDone[name]
    if scan.pending and scan.pending.name == name then
        GameTooltip:AddLine("Refreshing...", 0.4, 0.8, 1)
    elseif lookup and lookup.name == name then
        local wait = CooldownLeft()
        GameTooltip:AddLine(wait > 0 and string.format("Refresh in %d s, with your next key press or click", math.ceil(wait))
            or "Refresh with your next key press or click", 0.4, 0.8, 1)
    elseif done then
        if done.found then
            GameTooltip:AddLine("Refreshed " .. Ago(done.time), 0.4, 0.8, 1)
        else
            GameTooltip:AddLine("Not online (checked " .. Ago(done.time) .. ")", 0.6, 0.6, 0.6)
        end
    elseif reason == "faction" then
        GameTooltip:AddLine("Other faction: /who cannot refresh this player", 0.6, 0.6, 0.6)
    end
    GameTooltip:Show()
end

local function HideChatPlayerTooltip(frame)
    hover = nil
    if GameTooltip:IsOwned(frame) then GameTooltip:Hide() end
end

-- shows the tooltip again when the refresh of the hovered player was sent or answered
function RefreshChatTooltip()
    if hover and GameTooltip:IsOwned(hover.frame) then
        ShowChatPlayerTooltip(hover.frame, hover.link)
    end
end

local hookedChatFrames = {}
local function HookChatFrame(frame)
    if not frame or hookedChatFrames[frame] or not frame.HookScript then return end
    hookedChatFrames[frame] = true
    frame:HookScript("OnHyperlinkEnter", ShowChatPlayerTooltip)
    frame:HookScript("OnHyperlinkLeave", HideChatPlayerTooltip)
end

local function HookAllChatFrames()
    for i = 1, (NUM_CHAT_WINDOWS or 10) do HookChatFrame(_G["ChatFrame" .. i]) end
    -- temporary windows (whispers popped out into their own tab)
    for _, name in ipairs(CHAT_FRAMES or {}) do HookChatFrame(_G[name]) end
end

local function InstallChatTooltips()
    HookAllChatFrames()
    if hooksecurefunc and FCF_OpenTemporaryWindow then
        hooksecurefunc("FCF_OpenTemporaryWindow", HookAllChatFrames)
    end
end

function ForeverPlayerStatistics_SetChatRefresh(on)
    db.chatRefresh = on and true or false
    if not db.chatRefresh then lookup = nil end
    Print("/who refresh when hovering a player name in chat " .. OnOff(db.chatRefresh) .. ".")
    if RefreshPanel then RefreshPanel() end
end

function ForeverPlayerStatistics_SetChatTooltip(on)
    db.chatTooltip = on and true or false
    Print("tooltip on player names in chat " .. OnOff(db.chatTooltip) .. ".")
    if RefreshPanel then RefreshPanel() end
end

---------------------------------------------------------------------------
-- Battleground tracker
--
-- At the end of every battleground (as soon as the game knows the winner) all
-- players of the scoreboard are stored in ForeverPlayerStatisticsBG, one entry
-- per match. The scoreboard has no levels: they are collected during the match
-- from the raid, nameplates, target and mouseover, otherwise taken from the
-- player database. Each match is saved packed into one string (see SavePlayers
-- for why).
---------------------------------------------------------------------------

local bgdb -- ForeverPlayerStatisticsBG = { version = 1, matches = { { time, map, winner, me, myLevel, realm, dur, p } } }
local bg = { active = false, match = nil, levels = {}, lastRequest = 0, warned = false }
local bgCache   -- parsed matches, rebuilt when a match is added or the data is reset
local bgPanel
local bgSel = { level = nil, class = nil, race = nil }
local RefreshBGPanel, UpdateBGIcon

local BG_FIELDS = { "name", "faction", "class", "race", "level", "kb", "hk", "deaths", "honor", "damage", "healing" }
local BG_NUMBERS = { level = true, kb = true, hk = true, deaths = true, honor = true, damage = true, healing = true }

local function InBattleground()
    local inInstance, kind = IsInInstance()
    return inInstance and kind == "pvp"
end

-- scoreboard / raid name -> "First Last" (WoW Forever names, without a realm suffix)
local function BGName(n)
    if not n or n == "" then return nil end
    if n:find(" ") then return (n:gsub("%-.*$", "")) end -- "First Last-Realm"
    n = n:match("^([^%-]+%-[^%-]+)%-") or n               -- "First-Last-Realm"
    return (n:gsub("%-", " ", 1))                          -- "First-Last"
end

local function NoteLevel(name, level)
    if name and type(level) == "number" and level > 0 then bg.levels[name] = level end
end

local function NoteUnitLevel(unit)
    if not bg.active or not UnitExists(unit) or not UnitIsPlayer(unit) then return end
    local name, realm = UnitName(unit)
    local level = UnitLevel(unit)
    if HasSecret(name, realm, level) or not name then return end
    if realm and realm ~= "" then name = name .. " " .. realm end -- last name in the realm slot
    NoteLevel(name, level)
end

local function NoteRosterLevels()
    if not bg.active or not GetRaidRosterInfo then return end
    for i = 1, (GetNumGroupMembers and GetNumGroupMembers() or 0) do
        local ok, name, _, _, level = pcall(GetRaidRosterInfo, i)
        if ok and not HasSecret(name, level) then NoteLevel(BGName(name), level) end
    end
end

-- name, faction (0 Horde / 1 Alliance), race, class, classToken, kb, hk, deaths, honor, damage, healing
local function ReadScore(i)
    if C_PvP and C_PvP.GetScoreInfo then
        local ok, info = pcall(C_PvP.GetScoreInfo, i)
        if ok and type(info) == "table" and info.name then
            return info.name, info.faction, info.raceName, info.className, info.classToken,
                info.killingBlows, info.honorableKills, info.deaths, info.honorGained, info.damageDone, info.healingDone
        end
    end
    if not GetBattlefieldScore then return end
    local r = { GetBattlefieldScore(i) }
    -- the position of race / class differs between client versions: find the class token
    for j = 7, #r do
        if type(r[j]) == "string" and classSet[r[j]] then
            return r[1], r[6], r[j - 2], r[j - 1], r[j], r[2], r[3], r[4], r[5], r[j + 1], r[j + 2]
        end
    end
    return r[1], r[6], r[8], r[9], r[10], r[2], r[3], r[4], r[5], r[11], r[12]
end

local function RecordMatch()
    if not (db and bgdb and db.enabled and db.bgTrack) then return end
    local winnerId = GetBattlefieldWinner and GetBattlefieldWinner()
    if winnerId == nil or HasSecret(winnerId) then return end
    local winner = (winnerId == 0 and "Horde") or (winnerId == 1 and "Alliance") or "Draw"
    local n = GetNumBattlefieldScores and GetNumBattlefieldScores() or 0
    if n == 0 then return end
    NoteRosterLevels()
    local realm = MyRealm()
    local lines, row, skipped = {}, {}, 0
    for i = 1, n do
        local name, faction, race, class, token, kb, hk, deaths, honor, damage, healing = ReadScore(i)
        if HasSecret(name, faction, race, class, token, kb, hk, deaths, honor, damage, healing) then
            skipped = skipped + 1
        else
            name = BGName(name)
            local raceFile = ResolveRace(race)
            local f = (faction == 0 and "Horde") or (faction == 1 and "Alliance") or RACE_FACTION[raceFile]
            local cls = (token and classSet[token]) and token or (class and classByName[class:lower()])
            if name and f and cls and raceFile then
                local stored = db.players[name .. "-" .. realm]
                local p = {
                    name = name, faction = f, class = cls, race = raceFile,
                    level = bg.levels[name] or (stored and stored.level),
                    kb = kb, hk = hk, deaths = deaths, honor = honor, damage = damage, healing = healing,
                }
                for k, field in ipairs(BG_FIELDS) do row[k] = StoreValue(p[field]) end
                lines[#lines + 1] = table.concat(row, "\t")
            else
                skipped = skipped + 1
            end
        end
    end
    if #lines == 0 then
        if not bg.warned then
            bg.warned = true
            Print("|cffff4040battleground not recorded:|r the game does not give addons the scoreboard data here.")
        end
        return
    end
    -- the scoreboard is updated a few more times after the end: the same entry is replaced
    local m = bg.match
    local isNew = m == nil
    if isNew then
        m = { time = time() }
        bgdb.matches[#bgdb.matches + 1] = m
        bg.match = m
    end
    m.map = EnglishZone(GetRealZoneText and GetRealZoneText() or nil) or "?"
    m.winner = winner
    m.me = UnitFactionGroup("player")
    m.myLevel = UnitLevel("player")
    m.realm = realm
    if GetBattlefieldInstanceRunTime then
        local ok, ms = pcall(GetBattlefieldInstanceRunTime)
        if ok and type(ms) == "number" and ms > 0 then m.dur = math.floor(ms / 1000) end
    end
    m.p = table.concat(lines, "\n")
    bgCache = nil
    if isNew then
        local result = winner == "Draw" and "draw" or (winner == m.me and "|cff00ff00won|r" or "|cffff4040lost|r")
        Print(string.format("battleground recorded: %s, %s, %d players. %d battlegrounds in the database.",
            m.map, result, #lines, #bgdb.matches))
    end
    if RefreshBGPanel then RefreshBGPanel() end
    if UpdateBGIcon then UpdateBGIcon() end
end

-- entering / leaving a battleground starts a new match
local function BG_CheckZone()
    local now = InBattleground()
    if now ~= bg.active then
        bg.active = now
        bg.match = nil
        bg.warned = false
        wipe(bg.levels)
        if now and RequestBattlefieldScoreData then RequestBattlefieldScoreData() end
    end
end

-- every 15 s in a battleground: fresh scoreboard data, the end is caught by UPDATE_BATTLEFIELD_SCORE
local function BG_Tick()
    if bg.active and RequestBattlefieldScoreData and GetTime() - bg.lastRequest > 15 then
        bg.lastRequest = GetTime()
        RequestBattlefieldScoreData()
    end
end

local function BG_OnScore()
    if bg.active then RecordMatch() end
end

local function ParseMatches()
    if bgCache then return bgCache end
    bgCache = {}
    for _, m in ipairs(bgdb.matches) do
        local players = {}
        for line in (m.p or ""):gmatch("[^\n]+") do
            local p, i = {}, 0
            for value in (line .. "\t"):gmatch("([^\t]*)\t") do
                i = i + 1
                local field = BG_FIELDS[i]
                if field and value ~= "" then p[field] = BG_NUMBERS[field] and tonumber(value) or value end
            end
            if p.name then players[#players + 1] = p end
        end
        bgCache[#bgCache + 1] = { m = m, players = players }
    end
    return bgCache
end

-- bracket of a match from your own level: "10-19", "20-29", ..., "60"
local function Bracket(level)
    level = tonumber(level)
    if not level or level <= 0 then return "?" end
    local max = MaxLevel()
    if level >= max then return tostring(max) end
    local lo = math.floor(level / 10) * 10
    return lo .. "-" .. math.min(lo + 9, max - 1)
end

local function AddWin(t, key, win)
    local e = t[key]
    if not e then e = { g = 0, w = 0 }; t[key] = e end
    e.g = e.g + 1
    if win then e.w = e.w + 1 end
end

-- per battleground: matches, wins per faction, your record and the win rate of
-- the player games that match the team / class / race / level filters
local function AddMapMatch(ms, pm)
    local m = pm.m
    ms.matches = ms.matches + 1
    ms.wins[m.winner] = (ms.wins[m.winner] or 0) + 1
    if m.winner == m.me then
        ms.myWin = ms.myWin + 1
    elseif m.winner ~= "Draw" then
        ms.myLoss = ms.myLoss + 1
    end
    if m.winner == "Draw" then return end
    for _, p in ipairs(pm.players) do
        if (db.bgTeam == "ALL" or p.faction == db.bgTeam)
            and (not bgSel.level or p.level == bgSel.level)
            and (not bgSel.class or p.class == bgSel.class)
            and (not bgSel.race or RaceKey(p) == bgSel.race) then
            ms.g = ms.g + 1
            if p.faction == m.winner then ms.w = ms.w + 1 end
        end
    end
end

local function NewMapStats()
    return { matches = 0, wins = { Alliance = 0, Horde = 0, Draw = 0 }, myWin = 0, myLoss = 0, g = 0, w = 0 }
end

local function ComputeBGStats()
    local s = {
        matches = 0, wins = { Alliance = 0, Horde = 0, Draw = 0 }, myWin = 0, myLoss = 0,
        entries = 0, noLevel = 0, class = {}, race = {}, level = {}, maps = {}, brackets = {},
        mapStats = { ALL = NewMapStats() }, -- ["Warsong Gulch"] = ..., ALL = all battlegrounds
    }
    for _, pm in ipairs(ParseMatches()) do
        local m = pm.m
        local bracket = Bracket(m.myLevel)
        s.maps[m.map or "?"] = true
        s.brackets[bracket] = true
        -- battleground list: every map, only the bracket filter applies
        if db.bgBracket == "ALL" or bracket == db.bgBracket then
            local map = m.map or "?"
            s.mapStats[map] = s.mapStats[map] or NewMapStats()
            AddMapMatch(s.mapStats[map], pm)
            AddMapMatch(s.mapStats.ALL, pm)
        end
        if (db.bgMap == "ALL" or m.map == db.bgMap) and (db.bgBracket == "ALL" or bracket == db.bgBracket) then
            s.matches = s.matches + 1
            s.wins[m.winner] = (s.wins[m.winner] or 0) + 1
            if m.winner == m.me then
                s.myWin = s.myWin + 1
            elseif m.winner ~= "Draw" then
                s.myLoss = s.myLoss + 1
            end
            if m.winner ~= "Draw" then -- draws do not count for the win rates
                for _, p in ipairs(pm.players) do
                    if db.bgTeam == "ALL" or p.faction == db.bgTeam then
                        local win = p.faction == m.winner
                        local race = RaceKey(p)
                        local okLevel = not bgSel.level or p.level == bgSel.level
                        local okClass = not bgSel.class or p.class == bgSel.class
                        local okRace = not bgSel.race or race == bgSel.race
                        if okLevel and okClass and okRace then
                            s.entries = s.entries + 1
                            if not p.level then s.noLevel = s.noLevel + 1 end
                        end
                        if okLevel and okRace then AddWin(s.class, p.class, win) end
                        if okLevel and okClass then AddWin(s.race, race, win) end
                        if okClass and okRace and p.level then AddWin(s.level, p.level, win) end
                    end
                end
            end
        end
    end
    return s
end

local function Rate(e)
    return (e and e.g > 0) and e.w / e.g or 0
end

local function RateColor(rate)
    if rate >= 0.5 then return 0.25, 0.85, 0.25 end
    return 0.9, 0.25, 0.25
end

-- class / race list with win rates; the 50 % mark is shown on every bar
local function CreateWinRows(parent, x, y, onClick)
    local rows = {}
    for i = 1, ROWS do
        local ry = y - (i - 1) * ROW_H
        local r = {}
        r.btn = CreateFrame("Button", nil, parent)
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
            GameTooltip:AddLine(r.tip, 1, 1, 1)
            GameTooltip:AddLine(r.selected and "Click to show all again" or "Click to filter by this", 0.6, 0.6, 0.6)
            GameTooltip:Show()
        end)
        r.btn:SetScript("OnLeave", GameTooltip_Hide)
        r.name = parent:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
        r.name:SetPoint("TOPLEFT", x, ry)
        r.name:SetSize(90, ROW_H)
        r.name:SetJustifyH("LEFT")
        r.name:SetJustifyV("TOP")
        if r.name.SetWordWrap then r.name:SetWordWrap(false) end
        r.bg = parent:CreateTexture(nil, "BORDER")
        r.bg:SetPoint("TOPLEFT", x + 95, ry)
        r.bg:SetSize(ROW_BAR_W, 11)
        SetColor(r.bg, 0, 0, 0, 0.4)
        r.bar = parent:CreateTexture(nil, "ARTWORK")
        r.bar:SetPoint("TOPLEFT", x + 95, ry)
        r.bar:SetHeight(11)
        r.mid = parent:CreateTexture(nil, "OVERLAY")
        r.mid:SetPoint("TOPLEFT", x + 95 + ROW_BAR_W / 2, ry + 1)
        r.mid:SetSize(1, 13)
        SetColor(r.mid, 1, 1, 1, 0.6)
        r.value = parent:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
        r.value:SetPoint("TOPLEFT", x + 200, ry)
        r.value:SetSize(75, ROW_H)
        r.value:SetJustifyH("RIGHT")
        r.value:SetJustifyV("TOP")
        if r.value.SetWordWrap then r.value:SetWordWrap(false) end
        rows[i] = r
    end
    return rows
end

local function FillWinRows(rows, stats, nameOf, colorOf, selected)
    local list = {}
    for k, e in pairs(stats) do list[#list + 1] = { key = k, g = e.g, w = e.w, rate = Rate(e) } end
    if selected and not stats[selected] then list[#list + 1] = { key = selected, g = 0, w = 0, rate = 0 } end
    table.sort(list, function(a, b)
        if db.sortByName then
            local na, nb = nameOf(a.key), nameOf(b.key)
            if na ~= nb then return na < nb end
        elseif a.rate ~= b.rate then
            return a.rate > b.rate
        end
        return tostring(a.key) < tostring(b.key)
    end)
    if selected then
        for i, e in ipairs(list) do
            if e.key == selected and i > ROWS then
                table.remove(list, i)
                table.insert(list, 1, e)
                break
            end
        end
    end
    for i, r in ipairs(rows) do
        local e = list[i]
        local shown = e ~= nil
        for _, part in ipairs({ r.name, r.bg, r.bar, r.mid, r.value, r.btn }) do SetShown(part, shown) end
        r.key = e and e.key or nil
        r.selected = e and e.key == selected
        SetShown(r.sel, r.selected)
        if e then
            local cr, cg, cb = colorOf(e.key)
            r.label = nameOf(e.key)
            r.tip = string.format("%s of %s games won (%s)", Num(e.w), Num(e.g), Pct(e.w, e.g))
            r.name:SetText(r.label)
            r.name:SetTextColor(cr, cg, cb)
            SetColor(r.bar, cr, cg, cb, 0.85)
            r.bar:SetWidth(math.max(1, ROW_BAR_W * e.rate))
            local rr, rg, rb = RateColor(e.rate)
            r.value:SetText(string.format("|cff%02x%02x%02x%s|r  %s", rr * 255, rg * 255, rb * 255, Pct(e.w, e.g), Num(e.g)))
        end
    end
end

local BG_H = 785
local BG_HIST_H = 100
local MAP_ROWS = 6 -- "All battlegrounds" + up to 5 maps

-- battleground list: one row per map, click filters the whole window by it
local function CreateMapRows(parent, y)
    local rows = {}
    for i = 1, MAP_ROWS do
        local ry = y - (i - 1) * ROW_H
        local r = {}
        r.btn = CreateFrame("Button", nil, parent)
        r.btn:SetPoint("TOPLEFT", 18, ry + 2)
        r.btn:SetSize(INNER_W + 4, ROW_H)
        r.sel = r.btn:CreateTexture(nil, "BACKGROUND")
        r.sel:SetAllPoints()
        SetColor(r.sel, 1, 0.82, 0, 0.25)
        r.hl = r.btn:CreateTexture(nil, "HIGHLIGHT")
        r.hl:SetAllPoints()
        SetColor(r.hl, 1, 1, 1, 0.08)
        r.btn:SetScript("OnClick", function()
            if not r.key then return end
            db.bgMap = (r.key == "ALL" or db.bgMap == r.key) and "ALL" or r.key
            RefreshBGPanel()
        end)
        r.btn:SetScript("OnEnter", function(self)
            if not r.key then return end
            GameTooltip:SetOwner(self, "ANCHOR_RIGHT")
            GameTooltip:AddLine(r.label)
            for _, line in ipairs(r.tips) do GameTooltip:AddLine(line, 1, 1, 1) end
            GameTooltip:AddLine(r.key == "ALL" and "Click to show all battlegrounds"
                or (r.selected and "Click to show all battlegrounds again" or "Click to show only this battleground"), 0.6, 0.6, 0.6)
            GameTooltip:Show()
        end)
        r.btn:SetScript("OnLeave", GameTooltip_Hide)
        local function Text(x, w, justify)
            local fs = parent:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
            fs:SetPoint("TOPLEFT", x, ry)
            fs:SetSize(w, ROW_H)
            fs:SetJustifyH(justify)
            fs:SetJustifyV("TOP")
            if fs.SetWordWrap then fs:SetWordWrap(false) end
            return fs
        end
        r.name = Text(20, 140, "LEFT")
        r.matches = Text(160, 50, "RIGHT")
        r.a = parent:CreateTexture(nil, "ARTWORK")
        r.a:SetPoint("TOPLEFT", 222, ry)
        r.a:SetHeight(11)
        SetColor(r.a, FACTION_COLORS.Alliance[1], FACTION_COLORS.Alliance[2], FACTION_COLORS.Alliance[3], 0.85)
        r.h = parent:CreateTexture(nil, "ARTWORK")
        r.h:SetPoint("TOPRIGHT", parent, "TOPLEFT", 222 + 120, ry)
        r.h:SetHeight(11)
        SetColor(r.h, FACTION_COLORS.Horde[1], FACTION_COLORS.Horde[2], FACTION_COLORS.Horde[3], 0.85)
        r.factionText = Text(222, 120, "CENTER")
        r.record = Text(350, 110, "RIGHT")
        r.rate = Text(470, 90, "RIGHT")
        rows[i] = r
    end
    return rows
end

local function FillMapRows(rows, mapStats)
    local list = { "ALL" }
    local maps = {}
    for map in pairs(mapStats) do if map ~= "ALL" then maps[#maps + 1] = map end end
    table.sort(maps)
    for _, map in ipairs(maps) do list[#list + 1] = map end
    for i, r in ipairs(rows) do
        local key = list[i]
        local ms = key and mapStats[key]
        local shown = ms ~= nil
        for _, part in ipairs({ r.btn, r.name, r.matches, r.a, r.h, r.factionText, r.record, r.rate }) do SetShown(part, shown) end
        r.key = key
        r.selected = key and (db.bgMap == key)
        SetShown(r.sel, r.selected)
        if ms then
            local a, h = ms.wins.Alliance or 0, ms.wins.Horde or 0
            r.label = key == "ALL" and "All battlegrounds" or key
            r.name:SetText(r.label)
            if key == "ALL" then r.name:SetTextColor(1, 0.82, 0) else r.name:SetTextColor(1, 1, 1) end
            r.matches:SetText(Num(ms.matches))
            if a + h > 0 then
                local aw = 120 * a / (a + h)
                SetShown(r.a, a > 0); SetShown(r.h, h > 0)
                r.a:SetWidth(math.max(1, aw))
                r.h:SetWidth(math.max(1, 120 - aw))
                r.factionText:SetText(Pct(a, a + h) .. " / " .. Pct(h, a + h))
            else
                r.a:Hide(); r.h:Hide()
                r.factionText:SetText("-")
            end
            r.record:SetText(string.format("|cff00ff00%d|r - |cffff4040%d|r  %s", ms.myWin, ms.myLoss, Pct(ms.myWin, ms.myWin + ms.myLoss)))
            -- without team / class / race / level filter every game has a winner and a loser: always about 50 %
            local filtered = db.bgTeam ~= "ALL" or bgSel.level or bgSel.class or bgSel.race
            local rate = ms.g > 0 and ms.w / ms.g or 0
            local cr, cg, cb = RateColor(rate)
            r.rate:SetText((filtered and ms.g > 0) and string.format("|cff%02x%02x%02x%s|r", cr * 255, cg * 255, cb * 255, Pct(ms.w, ms.g)) or "-")
            r.tips = {
                string.format("%s battlegrounds: Alliance won %s, Horde won %s%s", Num(ms.matches), Num(a), Num(h),
                    (ms.wins.Draw or 0) > 0 and (", " .. Num(ms.wins.Draw) .. " draw(s)") or ""),
                string.format("You: %d won, %d lost (%s)", ms.myWin, ms.myLoss, Pct(ms.myWin, ms.myWin + ms.myLoss)),
                string.format("Win rate of the selection: %s of %s player games (%s)", Num(ms.w), Num(ms.g), Pct(ms.w, ms.g)),
            }
        end
    end
end

local function CycleValue(current, set)
    local list = { "ALL" }
    local sorted = {}
    for k in pairs(set) do sorted[#sorted + 1] = k end
    table.sort(sorted)
    for _, k in ipairs(sorted) do list[#list + 1] = k end
    for i, v in ipairs(list) do
        if v == current then return list[i % #list + 1] end
    end
    return "ALL"
end

local function CreateBGPanel()
    local p = CreateFrame("Frame", "ForeverPlayerStatisticsBGPanel", UIParent, "BackdropTemplate")
    bgPanel = p
    p:SetSize(W, BG_H)
    p:SetPoint("CENTER", 40, -20)
    if p.SetClampedToScreen then p:SetClampedToScreen(true) end
    p:SetFrameStrata("DIALOG")
    p:SetMovable(true)
    p:EnableMouse(true)
    p:RegisterForDrag("LeftButton")
    p:SetScript("OnDragStart", p.StartMoving)
    p:SetScript("OnDragStop", p.StopMovingOrSizing)
    if p.SetBackdrop then
        p:SetBackdrop({
            bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
            edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
            tile = true, tileSize = 32, edgeSize = 32,
            insets = { left = 8, right = 8, top = 8, bottom = 8 },
        })
    end
    p:Hide()
    tinsert(UISpecialFrames, "ForeverPlayerStatisticsBGPanel")

    local title = p:CreateFontString(nil, "ARTWORK", "GameFontNormalLarge")
    title:SetPoint("TOP", 0, -16)
    title:SetText("Battleground Statistics")
    local close = CreateFrame("Button", nil, p, "UIPanelCloseButton")
    close:SetPoint("TOPRIGHT", -4, -4)

    p.summary = p:CreateFontString(nil, "ARTWORK", "GameFontHighlight")
    p.summary:SetPoint("TOPLEFT", 20, -42)

    local function Button(w, x, onClick)
        local b = CreateFrame("Button", nil, p, "UIPanelButtonTemplate")
        b:SetSize(w, 22)
        b:SetPoint("TOPLEFT", x, -62)
        b:SetScript("OnClick", onClick)
        return b
    end
    p.mapBtn = Button(170, 18, function()
        db.bgMap = CycleValue(db.bgMap, p.stats.maps)
        RefreshBGPanel()
    end)
    p.bracketBtn = Button(130, 190, function()
        db.bgBracket = CycleValue(db.bgBracket, p.stats.brackets)
        RefreshBGPanel()
    end)
    p.teamBtn = Button(120, 322, function()
        local nextTeam = { ALL = "Alliance", Alliance = "Horde", Horde = "ALL" }
        db.bgTeam = nextTeam[db.bgTeam] or "ALL"
        RefreshBGPanel()
    end)
    p.clearBtn = CreateFrame("Button", nil, p, "UIPanelButtonTemplate")
    p.clearBtn:SetSize(90, 22)
    p.clearBtn:SetPoint("TOPRIGHT", -18, -62)
    p.clearBtn:SetText("Show all")
    p.clearBtn:SetScript("OnClick", function()
        bgSel.level, bgSel.class, bgSel.race = nil, nil, nil
        RefreshBGPanel()
    end)

    -- wins per faction
    Header(p, "Wins per faction", 20, -96)
    local fb = CreateFrame("Frame", nil, p)
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
    p.factionBar = fb
    p.record = p:CreateFontString(nil, "ARTWORK", "GameFontHighlightSmall")
    p.record:SetPoint("TOPLEFT", 20, -136)
    p.record:SetWidth(INNER_W)
    p.record:SetJustifyH("LEFT")

    -- per battleground
    Header(p, "Battlegrounds", 20, -158)
    for _, col in ipairs({ { 160, 50, "RIGHT", "games" }, { 222, 120, "CENTER", "Alliance / Horde won" },
        { 350, 110, "RIGHT", "your record" }, { 470, 90, "RIGHT", "win rate (filter)" } }) do
        local fs = p:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
        fs:SetPoint("TOPLEFT", col[1], -160)
        fs:SetSize(col[2], 12)
        fs:SetJustifyH(col[3])
        fs:SetText(col[4])
    end
    p.mapRows = CreateMapRows(p, -178)

    -- win rate per class and race
    local listTop = -178 - MAP_ROWS * ROW_H - 14
    p.classHeader = Header(p, "Win rate per class", 20, listTop)
    p.raceHeader = Header(p, "Win rate per race", 20 + INNER_W / 2 + 5, listTop)
    p.classRows = CreateWinRows(p, 20, listTop - 20, function(key)
        bgSel.class = bgSel.class ~= key and key or nil
        RefreshBGPanel()
    end)
    p.raceRows = CreateWinRows(p, 20 + INNER_W / 2 + 5, listTop - 20, function(key)
        bgSel.race = bgSel.race ~= key and key or nil
        RefreshBGPanel()
    end)

    -- win rate per level
    local histTop = listTop - 20 - ROWS * ROW_H - 14
    p.levelHeader = Header(p, "Win rate per level", 20, histTop)
    local hint = p:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
    hint:SetPoint("TOPRIGHT", -20, histTop - 2)
    hint:SetText("line = 50 %, click a level, class or race to filter")
    local hist = CreateFrame("Frame", nil, p)
    hist:SetSize(INNER_W, BG_HIST_H)
    hist:SetPoint("TOPLEFT", 20, histTop - 20)
    hist.bg = hist:CreateTexture(nil, "BACKGROUND")
    hist.bg:SetAllPoints()
    SetColor(hist.bg, 0, 0, 0, 0.4)
    hist.mid = hist:CreateTexture(nil, "OVERLAY")
    hist.mid:SetPoint("LEFT", hist, "BOTTOMLEFT", 0, BG_HIST_H / 2)
    hist.mid:SetSize(INNER_W, 1)
    SetColor(hist.mid, 1, 1, 1, 0.5)
    hist.bars, hist.labels = {}, {}
    p.hist = hist

    p.note = p:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
    p.note:SetPoint("TOPLEFT", hist, "BOTTOMLEFT", 0, -20)
    p.note:SetWidth(INNER_W)
    p.note:SetJustifyH("LEFT")

    p.trackCheck = CreateCheck(p, "Record battlegrounds (all players at the end of each battleground)", 14, histTop - 20 - BG_HIST_H - 52,
        function() return db.bgTrack end,
        function(v)
            db.bgTrack = v
            Print("battleground recording " .. OnOff(v) .. ".")
            if UpdateBGIcon then UpdateBGIcon() end
        end)

    StaticPopupDialogs["FOREVERPLAYERSTATISTICS_BGRESET"] = {
        text = "Delete all %s recorded battlegrounds?",
        button1 = YES,
        button2 = NO,
        OnAccept = function()
            wipe(bgdb.matches)
            bgCache = nil
            Print("battleground data cleared.")
            RefreshBGPanel()
            if UpdateBGIcon then UpdateBGIcon() end
        end,
        timeout = 0,
        whileDead = true,
        hideOnEscape = true,
    }
    local reset = CreateFrame("Button", nil, p, "UIPanelButtonTemplate")
    reset:SetSize(150, 22)
    reset:SetPoint("TOPRIGHT", -20, histTop - 20 - BG_HIST_H - 50)
    reset:SetText("Reset battlegrounds")
    reset:SetScript("OnClick", function()
        StaticPopup_Show("FOREVERPLAYERSTATISTICS_BGRESET", Num(#bgdb.matches))
    end)

    local help = p:CreateFontString(nil, "ARTWORK", "GameFontDisableSmall")
    help:SetPoint("BOTTOMLEFT", 20, 16)
    help:SetWidth(INNER_W)
    help:SetJustifyH("LEFT")
    help:SetText("Every player of a finished battleground counts as one game: a win if their faction won. Draws are not counted. Levels are not on the scoreboard; they come from the raid, nameplates, target / mouseover or the player database.")

    p:SetScript("OnShow", function() RefreshBGPanel() end)
end

local function RefreshBGHistogram(s)
    local hist = bgPanel.hist
    local n = MaxLevel()
    for l in pairs(s.level) do if l > n then n = l end end
    local bw = INNER_W / n
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
                GameTooltip:SetOwner(self, "ANCHOR_TOP")
                GameTooltip:AddLine("Level " .. self.level)
                if self.e then
                    GameTooltip:AddLine(string.format("%s of %s games won (%s)", Num(self.e.w), Num(self.e.g), Pct(self.e.w, self.e.g)), 1, 1, 1)
                else
                    GameTooltip:AddLine("no games", 0.6, 0.6, 0.6)
                end
                GameTooltip:AddLine(bgSel.level == self.level and "Click to show all levels again"
                    or "Click to show the classes and races of this level", 0.6, 0.6, 0.6)
                GameTooltip:Show()
            end)
            b:SetScript("OnLeave", GameTooltip_Hide)
            b:SetScript("OnMouseUp", function(self)
                bgSel.level = bgSel.level ~= self.level and self.level or nil
                RefreshBGPanel()
            end)
            hist.bars[l] = b
        end
        b:ClearAllPoints()
        b:SetPoint("BOTTOMLEFT", hist, "BOTTOMLEFT", (l - 1) * bw, 0)
        b:SetSize(math.max(1, bw > 3 and bw - 1 or bw), BG_HIST_H)
        local e = s.level[l]
        b.level, b.e = l, e
        SetShown(b.sel, bgSel.level == l)
        if e and e.g > 0 then
            local rate = Rate(e)
            local cr, cg, cb = RateColor(rate)
            -- few games: paler bar
            SetColor(b.tex, cr, cg, cb, e.g >= 10 and 0.9 or 0.4)
            b.tex:SetHeight(math.max(1, BG_HIST_H * rate))
            b.tex:Show()
        else
            b.tex:Hide()
        end
        b:Show()
    end
    for l = n + 1, #hist.bars do hist.bars[l]:Hide() end
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
end

function RefreshBGPanel()
    local p = bgPanel
    if not (p and p:IsShown()) then return end
    p.trackCheck:Refresh()
    local s = ComputeBGStats()
    p.stats = s
    p.summary:SetText(string.format("|cffffd100%s|r battlegrounds recorded   -   |cffffd100%s|r match the filter",
        Num(#bgdb.matches), Num(s.matches)))
    p.mapBtn:SetText(db.bgMap == "ALL" and "All battlegrounds" or db.bgMap)
    p.bracketBtn:SetText("Bracket: " .. (db.bgBracket == "ALL" and "All" or db.bgBracket))
    p.teamBtn:SetText("Team: " .. FACTION_FILTER_LABEL[db.bgTeam])

    local a, h, d = s.wins.Alliance or 0, s.wins.Horde or 0, s.wins.Draw or 0
    local fb = p.factionBar
    if a + h == 0 then
        fb.a:Hide(); fb.h:Hide()
        fb.text:SetText("no battlegrounds yet")
    else
        local aw = INNER_W * a / (a + h)
        SetShown(fb.a, a > 0); SetShown(fb.h, h > 0)
        fb.a:SetWidth(math.max(1, aw))
        fb.h:SetWidth(math.max(1, INNER_W - aw))
        fb.text:SetText(string.format("Alliance won %s (%s)        Horde won %s (%s)", Pct(a, a + h), Num(a), Pct(h, a + h), Num(h)))
    end
    local record = string.format("Your battlegrounds: |cff00ff00%s won|r, |cffff4040%s lost|r (%s)",
        Num(s.myWin), Num(s.myLoss), Pct(s.myWin, s.myWin + s.myLoss))
    if d > 0 then record = record .. string.format("   -   %s draw(s), not counted", Num(d)) end
    p.record:SetText(record)

    FillMapRows(p.mapRows, s.mapStats)
    FillWinRows(p.classRows, s.class, ClassLabel, ClassColor, bgSel.class)
    FillWinRows(p.raceRows, s.race, RaceLabel, RaceColor, bgSel.race)
    RefreshBGHistogram(s)

    local function Suffix(...)
        local parts = {}
        for i = 1, select("#", ...) do
            local v = select(i, ...)
            if v then parts[#parts + 1] = v end
        end
        return #parts > 0 and ("|cffffffff - " .. table.concat(parts, ", ") .. "|r") or ""
    end
    local lvl = bgSel.level and ("level " .. bgSel.level) or nil
    p.classHeader:SetText("Win rate per class" .. Suffix(lvl, bgSel.race and RaceLabel(bgSel.race)))
    p.raceHeader:SetText("Win rate per race" .. Suffix(lvl, bgSel.class and ClassLabel(bgSel.class)))
    p.levelHeader:SetText("Win rate per level" .. Suffix(bgSel.class and ClassLabel(bgSel.class), bgSel.race and RaceLabel(bgSel.race)))
    SetShown(p.clearBtn, bgSel.level or bgSel.class or bgSel.race)
    p.note:SetText(string.format("%s player games match the filter, %s of them without known level (left out of the level chart). Pale bars: fewer than 10 games.",
        Num(s.entries), Num(s.noLevel)))
end

local function ToggleBGPanel()
    if not bgPanel then return end
    if bgPanel:IsShown() then bgPanel:Hide() else bgPanel:Show() end
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
    checks[4] = CreateCheck(info, "Show the stored data when the mouse is over a player name in chat", 12, -10,
        function() return db.chatTooltip end,
        function(v) ForeverPlayerStatistics_SetChatTooltip(v) end)
    checks[4]:ClearAllPoints()
    checks[4]:SetPoint("TOPLEFT", checks[3], "BOTTOMLEFT", 0, -2)
    checks[5] = CreateCheck(info, "Refresh a player with /who when the mouse is over the name in chat", 12, -10,
        function() return db.chatRefresh end,
        function(v) ForeverPlayerStatistics_SetChatRefresh(v) end)
    checks[5]:ClearAllPoints()
    checks[5]:SetPoint("TOPLEFT", checks[4], "BOTTOMLEFT", 0, -2)
    info:SetScript("OnShow", function()
        for _, cb in ipairs(checks) do cb:Refresh() end
    end)
    last = checks[5]

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

-- A round button at the edge of the minimap that can be dragged around it.
-- angleKey: field in db that holds its position in degrees.
local function CreateMinimapIcon(name, texture, angleKey)
    -- Keep the button outside the minimap; WoW Forever clips minimap child frames.
    local b = CreateFrame("Button", name, UIParent)
    b:SetSize(31, 31)
    b:SetFrameStrata("MEDIUM")
    b:SetFrameLevel(8)
    b:RegisterForClicks("LeftButtonUp", "RightButtonUp")
    b:RegisterForDrag("LeftButton")

    local border = b:CreateTexture(nil, "OVERLAY")
    border:SetTexture("Interface\\Minimap\\MiniMap-TrackingBorder")
    border:SetSize(53, 53)
    border:SetPoint("TOPLEFT")

    local icon = b:CreateTexture(nil, "ARTWORK")
    icon:SetTexture(texture)
    icon:SetSize(20, 20)
    icon:SetPoint("TOPLEFT", 6, -5)
    icon:SetTexCoord(0.08, 0.92, 0.08, 0.92)
    b.icon = icon

    b:SetHighlightTexture("Interface\\Minimap\\UI-Minimap-ZoomButton-Highlight")

    local function UpdatePosition()
        local angle = math.rad(db[angleKey])
        local radius = (Minimap:GetWidth() / 2) + 5
        b:ClearAllPoints()
        b:SetPoint("CENTER", Minimap, "CENTER", math.cos(angle) * radius, math.sin(angle) * radius)
    end
    UpdatePosition()

    b:SetScript("OnDragStart", function(self)
        self:SetScript("OnUpdate", function()
            local mx, my = Minimap:GetCenter()
            local scale = Minimap:GetEffectiveScale()
            local cx, cy = GetCursorPosition()
            db[angleKey] = math.deg(math.atan2(cy / scale - my, cx / scale - mx))
            UpdatePosition()
        end)
    end)
    b:SetScript("OnDragStop", function(self) self:SetScript("OnUpdate", nil) end)
    return b
end

-- Second minimap button: battleground statistics at a glance, click opens the window.
local bgIcon
local function ShowBGIconTooltip(self)
    GameTooltip:SetOwner(self, "ANCHOR_LEFT")
    GameTooltip:AddLine("Battleground Statistics")
    local matches = bgdb and bgdb.matches or {}
    if #matches == 0 then
        GameTooltip:AddLine("No battlegrounds recorded yet.", 1, 1, 1)
        GameTooltip:AddLine("Every finished battleground is recorded automatically.", 0.7, 0.7, 0.7)
    else
        -- your record overall and per battleground (no player data needed, so this stays fast)
        local total = { w = 0, l = 0, d = 0 }
        local maps, mapNames = {}, {}
        for _, m in ipairs(matches) do
            local map = m.map or "?"
            local t = maps[map]
            if not t then t = { w = 0, l = 0, d = 0 }; maps[map] = t; mapNames[#mapNames + 1] = map end
            local key = (m.winner == "Draw" and "d") or (m.winner == m.me and "w") or "l"
            t[key] = t[key] + 1
            total[key] = total[key] + 1
        end
        table.sort(mapNames)
        local function Line(label, t, r, g, b)
            GameTooltip:AddDoubleLine(label,
                string.format("|cff00ff00%d|r - |cffff4040%d|r   %s", t.w, t.l, Pct(t.w, t.w + t.l)), r, g, b, 1, 1, 1)
        end
        GameTooltip:AddLine(string.format("%s battlegrounds recorded", Num(#matches)), 1, 1, 1)
        Line("All battlegrounds", total, 1, 0.82, 0)
        for _, map in ipairs(mapNames) do Line(map, maps[map], 1, 1, 1) end
        -- last battleground
        local last = matches[#matches]
        local result = last.winner == "Draw" and "draw"
            or (last.winner == last.me and "|cff00ff00won|r" or "|cffff4040lost|r")
        GameTooltip:AddLine(string.format("Last: %s, %s (%s)", last.map or "?", result,
            date("%d.%m. %H:%M", last.time or time())), 0.8, 0.8, 0.8)
    end
    if bg.active then
        GameTooltip:AddLine("|cff00ff00In a battleground:|r it is recorded when it ends.", 1, 1, 1)
    end
    if not (db.enabled and db.bgTrack) then
        GameTooltip:AddLine("Recording |cffff4040off|r (/fps bg on)", 1, 1, 1)
    end
    GameTooltip:AddLine("Left-click: battleground statistics", 0.7, 0.7, 0.7)
    GameTooltip:AddLine("Right-click: player overview", 0.7, 0.7, 0.7)
    GameTooltip:AddLine("Drag to move around the minimap.", 0.7, 0.7, 0.7)
    GameTooltip:Show()
end

local function CreateBGMinimapButton()
    bgIcon = CreateMinimapIcon("ForeverPlayerStatisticsBGMinimapButton", "Interface\\Icons\\INV_BannerPVP_02", "bgMinimapAngle")
    if bgIcon.icon.SetDesaturated then bgIcon.icon:SetDesaturated(not (db.enabled and db.bgTrack)) end
    bgIcon:SetScript("OnClick", function(_, button)
        if button == "RightButton" then
            TogglePanel()
        else
            ToggleBGPanel()
        end
    end)
    bgIcon:SetScript("OnEnter", ShowBGIconTooltip)
    bgIcon:SetScript("OnLeave", GameTooltip_Hide)
    SetShown(bgIcon, db.bgMinimapShown)
end

-- grey icon while battleground recording is off; tooltip updated after a new match
function UpdateBGIcon()
    if not bgIcon then return end
    if bgIcon.icon.SetDesaturated then bgIcon.icon:SetDesaturated(not (db.enabled and db.bgTrack)) end
    if GameTooltip:IsOwned(bgIcon) then ShowBGIconTooltip(bgIcon) end
end

local function CreateMinimapButton()
    bar = CreateMinimapIcon("ForeverPlayerStatisticsMinimapButton", "Interface\\Icons\\INV_Misc_Spyglass_03", "minimapAngle")
    local icon = bar.icon
    if icon.SetDesaturated then icon:SetDesaturated(not db.enabled) end -- grey while the addon is off

    local function ShowTooltip(self)
        local s = ComputeStats(true)
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
    BG_Tick()
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
        -- battleground database (separate SavedVariable)
        ForeverPlayerStatisticsBG = ForeverPlayerStatisticsBG or {}
        bgdb = ForeverPlayerStatisticsBG
        bgdb.version = bgdb.version or 1
        if type(bgdb.matches) ~= "table" then bgdb.matches = {} end
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
        -- the realm name is not known on this login: take the realm most players are stored with
        if (not GetRealmName or GetRealmName() == "") and BadRealm(db.lastRealm) then
            local counts, best, bestN = {}, nil, 0
            for _, p in pairs(db.players) do
                if not BadRealm(p.realm) then
                    local n = (counts[p.realm] or 0) + 1
                    counts[p.realm] = n
                    if n > bestN then best, bestN = p.realm, n end
                end
            end
            db.lastRealm = best
        end
        -- records saved with a race name that was not recognised then (e.g. Skyborne)
        local myRealm, moved = MyRealm(), {}
        local realmKnown = not BadRealm(myRealm)
        for key, p in pairs(db.players) do
            if p.race and not RACE_NAMES[p.race] then p.race = ResolveRace(p.race) end
            p.zone = EnglishZone(p.zone) -- older records kept the German zone name
            p.realmType = nil -- no longer stored
            if realmKnown and p.realm ~= myRealm and p.name then
                if BadRealm(p.realm) then
                    p.realm = myRealm -- stored while the realm name was unknown
                    moved[key] = p
                elseif p.realm == NormalizedRealm(myRealm) then
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
        RebuildCounts()
        InstallChatFilter()
        GuardWhoWindow()
        InstallChatTooltips()
        if hooksecurefunc and C_FriendList and C_FriendList.SendWho then
            hooksecurefunc(C_FriendList, "SendWho", OnAnySendWho)
        end
        CreateMinimapButton()
        CreateBGMinimapButton()
        CreatePanel()
        CreateBGPanel()
        CreateInfoPanel()

        f:RegisterEvent("WHO_LIST_UPDATE")
        f:RegisterEvent("PLAYER_TARGET_CHANGED")
        f:RegisterEvent("UPDATE_MOUSEOVER_UNIT")
        f:RegisterEvent("PLAYER_REGEN_ENABLED")
        -- battleground tracker
        f:RegisterEvent("PLAYER_ENTERING_WORLD")
        f:RegisterEvent("ZONE_CHANGED_NEW_AREA")
        f:RegisterEvent("UPDATE_BATTLEFIELD_SCORE")
        f:RegisterEvent("GROUP_ROSTER_UPDATE")
        pcall(f.RegisterEvent, f, "NAME_PLATE_UNIT_ADDED")
        BG_CheckZone()
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
        NoteUnitLevel("target")
    elseif event == "UPDATE_MOUSEOVER_UNIT" then
        RecordUnit("mouseover")
        NoteUnitLevel("mouseover")
    elseif event == "PLAYER_ENTERING_WORLD" or event == "ZONE_CHANGED_NEW_AREA" then
        BG_CheckZone()
    elseif event == "UPDATE_BATTLEFIELD_SCORE" then
        BG_OnScore()
    elseif event == "GROUP_ROSTER_UPDATE" then
        NoteRosterLevels()
    elseif event == "NAME_PLATE_UNIT_ADDED" then
        NoteUnitLevel(arg1)
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
    if UpdateBGIcon then UpdateBGIcon() end
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

function ForeverPlayerStatistics_ToggleBG()
    ToggleBGPanel()
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
    elseif cmd == "chat" then
        ForeverPlayerStatistics_SetChatTooltip(not db.chatTooltip)
    elseif cmd == "bg" and (rest == "on" or rest == "off") then
        db.bgTrack = rest == "on"
        Print("battleground recording " .. OnOff(db.bgTrack) .. ".")
        if RefreshBGPanel then RefreshBGPanel() end
        UpdateBGIcon()
    elseif cmd == "bgicon" then
        db.bgMinimapShown = not db.bgMinimapShown
        if bgIcon then SetShown(bgIcon, db.bgMinimapShown) end
        Print("battleground minimap button " .. OnOff(db.bgMinimapShown) .. ".")
    elseif cmd == "bg" then
        ToggleBGPanel()
    elseif cmd == "chatwho" then
        ForeverPlayerStatistics_SetChatRefresh(not db.chatRefresh)
    elseif cmd == "help" then
        Print("/fps - overview  |  /fps start - start the scan / send the next query now  |  /fps stop - stop the scan  |  /fps reset - clear the database  |  /fps cooldown <seconds>  |  /fps deep - deep search on/off  |  /fps chat - chat name tooltip on/off  |  /fps chatwho - /who refresh on hover on/off  |  /fps bg - battleground statistics  |  /fps bg on|off - battleground recording on/off  |  /fps bgicon - battleground minimap button on/off  |  /fps on|off - addon on/off  |  /fps who on|off - /who search on/off  |  /fps who pause|resume - pause until logout")
        Print("Addon: " .. OnOff(db.enabled) .. "   /who search: " .. OnOff(db.whoEnabled))
        Print("Recording targets/mouseover: " .. OnOff(db.recordUnits) .. "   own /who searches: " .. OnOff(db.recordOwnWho))
    elseif panel then
        TogglePanel()
    end
end
