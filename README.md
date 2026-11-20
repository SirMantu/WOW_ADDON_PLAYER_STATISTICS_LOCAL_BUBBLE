# 🔭 ForeverPlayerStatistics

> Who is playing on your server? Collect players with `/who` and see classes, races, factions and levels at a glance.

**WoW Forever only** · Interface `16001` · Version `1.0.1` · by Manuel Metzger

📥 [Download on CurseForge](https://www.curseforge.com/wow/addons/foreverplayerstatistics) · 💻 [Source code on GitHub](https://github.com/SirMantu/WOW_ADDON_PLAYER_STATISTICS_LOCAL_BUBBLE)

---

## ✨ Features

- 🔎 **Continuous server scan with `/who`**: starts automatically and asks every level from the highest down to 1 in a loop until you press Stop.
- 👀 **Passive recording** of players you target or mouse over, including the other faction, and of your own `/who` searches.
- 📈 **Average and median level**, overall or per class and race ("Show: level"), and a **level range bar** to see how the faction, class and race percentages change between level X and Y.
- 💬 **Chat name tooltips**: hover over a player name in chat to see the stored level, race, class, faction, guild, zone and when the player was last seen.
- 💾 **Permanent, account-wide database**. Each player is stored once (name + realm); scanning a player again replaces the old data.
- 📊 **Overview window**: Alliance vs Horde, classes, races and a players-per-level chart, filterable by faction and realm. Click a level, class or race to filter the other lists by it (e.g. click level 23 to see the classes and races of level 23); sort the lists by count or by name.
- 🗺️ **Minimap button**: left-click for the overview, right-click to start the scan or send the next query now.

---

## 📦 Installation

Install it with the CurseForge app from the [CurseForge project page](https://www.curseforge.com/wow/addons/foreverplayerstatistics), or download it there or from [GitHub](https://github.com/SirMantu/WOW_ADDON_PLAYER_STATISTICS_LOCAL_BUBBLE) and install it by hand:

Copy the `ForeverPlayerStatistics` folder into `_forever_/Interface/AddOns/` so that the result is `.../AddOns/ForeverPlayerStatistics/ForeverPlayerStatistics.toc`, then restart the game or type `/reload`. A "Download ZIP" from GitHub unpacks to a folder named `WOW_ADDON_PLAYER_STATISTICS_LOCAL_BUBBLE-main`: rename it to `ForeverPlayerStatistics`, or the game will not load the addon.

## 🚀 How scanning works

The scan **starts automatically** and runs until you press **Stop** (in the overview, or `/fps stop`). It keeps running after `/reload` and logout.

The game only allows `/who` from a key press or mouse click, so an addon cannot send it on a timer. The addon therefore sends the next query **with your next key press or click in the game world** once the cooldown (5 s) is over. Your keys still work normally; the addon only uses the moment of the key press.

Scan queries run completely in the background: the Who window does not open and nothing is written to the chat. You do not need to open the overview window either. `/who` searches you type yourself work as usual.

How it works:

1. A pass asks **every level once, without any other filter**, from the highest level down to level 1: `60-60`, `59-59`, ... `1-1` (60 queries, about 5 minutes per pass).
2. When level 1 is done, the next pass starts again at the highest level, in a loop until you press Stop.
3. `/who` returns at most 50 players per query. A level with 50 or more players online is not split further, so some of its players can be missing; the summary after each pass says how many levels hit the limit.
4. **Deep search** (option in the overview or `/fps deep`, off by default): every level query also gets a random letter, e.g. `23-23 n-"k"`. `/who` then only lists players with that letter in their name, so busy levels with 50+ players show different players in every pass. Quiet levels return fewer players per query, so leave it off if you mainly want complete counts of quiet levels.

Limits: only players who are online during the scan are found, and `/who` only lists **your own faction**. The other faction is recorded when you target or mouse over its players, or when you scan with a character of the other faction (the database is shared by all your characters).

## ⌨️ Commands

| Command | What it does |
|---|---|
| `/fps` | Show / hide the overview |
| `/fps start` | Start the scan / send the next query now |
| `/fps stop` | Stop the scan |
| `/fps reset` | Delete the whole database (asks first) |
| `/fps cooldown <seconds>` | Time between two `/who` queries (default 5) |
| `/fps deep` | Deep search on / off |
| `/fps chat` | Tooltip on player names in chat on / off |
| `/fps on` / `/fps off` | Switch the whole addon on / off (saved permanently) |
| `/fps who on` / `/fps who off` | Switch the `/who` search on / off (saved permanently) |
| `/fps who pause` / `/fps who resume` | Pause the `/who` search until you log out (not saved) |
| `/fps help` | List the commands |

## ⚙️ Switching it off

The same switches are in the overview window and under Esc -> Options -> AddOns -> ForeverPlayerStatistics:

- **Addon on/off**: when off, nothing is recorded and no `/who` is sent; the statistics can still be viewed and the minimap icon turns grey. Saved permanently.
- **`/who` search on/off**: when off, no `/who` is sent at all; players you target or mouse over are still recorded. Saved permanently.
- **Pause the `/who` search until logout**: same as above, but only for this session; after logout or `/reload` the search runs again.

## 🛡️ Fair play and the game rules

ForeverPlayerStatistics is built to stay within the rules for addons:

- **Official addon API only.** It uses the same `/who` function every player can type. It does not change game files, read memory or run any outside program.
- **No automation of gameplay.** It never moves, fights, loots or interacts for you. It only reads the public `/who` list and the players you target or mouse over.
- **You stay in control.** The game only allows `/who` on a real key press or mouse click, and the addon follows that: no input from you, no query. It does not work around this protection.
- **Limited traffic.** At most one `/who` query every 5 seconds (raise it with `/fps cooldown <seconds>`), and never a second one while the first is still waiting for its answer. That is far below what the server allows and has no effect on the server or other players.
- **Your data stays with you.** Everything is saved locally in your SavedVariables. Nothing is sent anywhere or shared with other players.
- **Easy to switch off.** The `/who` search can be paused until logout or switched off completely (see above).

Note: this addon is not reviewed or approved by Blizzard or WoW Forever, and only they decide what their rules allow. If you want to be sure, check the rules of your server. If you publish collected data, keep in mind it contains other players' names.

## 💾 Stored data

Saved in `WTF/Account/<account>/SavedVariables/ForeverPlayerStatistics.lua`, one record per `First Last-Server`:
name (WoW Forever names are always first and last name), realm (the name of the WoW Forever super server exactly as the game shows it, e.g. `CAMWOWEU5Realm5PvE`), level, class, race, faction, guild, zone, source (`who` or `unit`), last seen, first seen.

All values are stored in English, whatever the client language: class and race as English names (`WARRIOR`, `Scourge`), faction as `Alliance` / `Horde`. Zones are translated from German with a built-in list (zones, capitals, dungeons, battlegrounds, well-known places); smaller places that are not in the list are stored as the server sends them. Guild names are kept as they are.
