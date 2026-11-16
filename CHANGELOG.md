# Changelog

## 1.0.1

- Fixed: large databases could no longer be loaded. From roughly 50,000 players on, WoW refused the saved file with "Error loading ... ForeverPlayerStatistics.lua: constant table overflow", and the addon started with an empty database. Players are now saved packed into a few text lines, so the database loads with any realistic number of players (hundreds of millions) and the file is about a third of its old size.
- The new format is written automatically at the next logout or `/reload`. Databases that are still small enough to load are converted without any action.
- A database that already hit the error cannot be loaded by the game. Keep the file (with WoW closed, make a copy of `WTF/Account/<account>/SavedVariables/ForeverPlayerStatistics.lua`) before you log in again, because the next logout replaces it with the empty database. It can then be converted outside the game.

## 1.0.0

- Initial release, for WoW Forever only.
- Continuous `/who` scan that starts automatically and runs until you press Stop, also over /reload and logout. A query is sent with your next key press or click in the game world every few seconds (the game only allows `/who` on a key press or click). Each pass asks every level once without any other filter, from the highest level down to 1 (`60-60`, `59-59`, ... `1-1`), then starts again. Optional deep search (overview checkbox or `/fps deep`) adds a random name letter to each level query (`23-23 n-"k"`) to find other players on busy levels. Scan queries run in the background: no Who window and no chat output, also when the server answers a query late (after the 10 s timeout).
- Options (overview window, Esc -> Options -> AddOns, slash commands) to switch the whole addon off or the `/who` search off permanently, or to pause the `/who` search until logout.
- Records players you target or mouse over (including the other faction) and the results of your own `/who` searches.
- Supports the Skyborne race on both factions (e.g. "Himmelsgeborener der Windformer" in German /who results). The race list shows them separately as "Skyborne (A)" and "Skyborne (H)".
- Players whose class, race, faction or level is unknown are not stored and are left out of all statistics.
- All stored values are English, whatever the client language (zones via a built-in German -> English list). Zones that are not in the list are stored as the server sends them. The realm field holds the WoW Forever super server name exactly as the game shows it.
- WoW Forever names are always stored as first and last name (for targeted players the last name was taken for the realm).
- Account-wide database (`ForeverPlayerStatisticsDB`). Each player is stored once per name and realm; seeing a player again replaces the old data.
- Overview window from the minimap spyglass or `/fps`: Alliance vs Horde, classes, races and players per level, filterable by faction and realm. Click a level bar to see the classes and races of that level, click a class or race to see its players per level and the other list for it; the selections can be combined ("Show all" clears them). Class and race lists can be sorted by count or by name.
