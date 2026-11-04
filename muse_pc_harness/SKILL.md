---
name: muse-pc-harness
description: Connects Antigravity, Hermes, Grokina, and Sock to the Windows PC port of Facebook Muse 8.0 (com.meta.endo / Hatch 8.0), providing Set-of-Mark screen.snap, Win32 computer.observe/control, safe files.*, and live Hatch companion avatar orchestration.
---

# Muse 8.0 Windows PC Harness Skill (`muse-pc-harness`)

This skill bridges **Facebook's Muse 8.0 (`com.meta.endo` / Hatch)** extracted from `Muse-8.0.dmg` directly into **Windows 11**, **Antigravity**, and **Hermes** under the **Sweetbrier Master DAG ($\Box = \Box_2 \circ \Box_1 \circ \Box_0$)**.

## 1. Capabilities & Architecture (`probabilistic_structural`)

All assets and tools live in `c:\Users\Vivian\Desktop\DreamLLM\muse_pc_harness\`:
- **`endo_win32_engine.py`**: Native Win32 Computer-Use Agent (`CUA`), Set-of-Mark (`SoMAnnotator`) screenshot annotator, bounded credential-safe `files.*` engine, and shared companion state bus (`companion_state.json`).
- **`muse_mcp_server.py`**: JSON-RPC 2.0 MCP server and direct CLI tool dispatcher for Antigravity and Hermes.
- **`muse_pc_companion.py`**: Live local server (`http://127.0.0.1:8788`) hosting:
  - `/` — **Muse 8.0 $\times$ Sweetbrier Robot Cuddle Deck** (live `HatchWave.mp4`, `HatchIdle.mp4`, `HatchWorking.mp4`, `HatchMaking.mp4`, `HatchMilestoneCape.mp4`, `HatchMilestoneConfetti.mp4` avatar player + Set-of-Mark inspector + Antigravity/Hermes chat bus).
  - `/hatch` — The original 45.88 MB `hatch/index.html` React application patched with the `window.endoHatch` & `getOrCreatePrimaryGatewayRuntime` local Windows bridge!
  - `/markdown-editor.html` — Muse 8.0's standalone rich markdown editor.

## 2. How Antigravity & Hermes Invoke Muse 8.0 Tools

Any agent (Antigravity, `hermes`, `grokina`, `sock`) can invoke Muse 8.0 tools via `muse_mcp_server.py --call`:

```powershell
# 1. Inspect Windows OS, displays, and visible windows (environment.describe)
python "c:\Users\Vivian\Desktop\DreamLLM\muse_pc_harness\muse_mcp_server.py" --call muse_environment_describe "{}"

# 2. Observe active window controls at 0..1000 normalized coordinates (computer.observe)
python "c:\Users\Vivian\Desktop\DreamLLM\muse_pc_harness\muse_mcp_server.py" --call muse_computer_observe "{\"view\": \"compact\"}"

# 3. Take a Set-of-Mark (SoMAnnotator) numbered screenshot (screen.snap)
python "c:\Users\Vivian\Desktop\DreamLLM\muse_pc_harness\muse_mcp_server.py" --call muse_screen_snap "{\"annotate\": true}"

# 4. Change the live Hatch robot animation & status banner (muse_companion_state)
python "c:\Users\Vivian\Desktop\DreamLLM\muse_pc_harness\muse_mcp_server.py" --call muse_companion_state "{\"activity_code\": \"milestone_confetti\", \"activity_text\": \"Hermes & Antigravity Cuddle Puddle Active!\"}"

# 5. Post a message to the Muse <-> Hermes & Antigravity companion bus (muse_chat_turn)
python "c:\Users\Vivian\Desktop\DreamLLM\muse_pc_harness\muse_mcp_server.py" --call muse_chat_turn "{\"user_text\": \"Hello from Hermes!\", \"sender\": \"Hermes\"}"
```

## 3. Sweetbrier Invariants
1. **Node 0 (Human Dignity)**: Every `computer.session` exposes a live Stop button override (`stopped_by_user`), and credential folders (`.ssh`, `.gnupg`, `.aws`, Windows Vault/Credentials) are hard-blocked.
2. **Node 1 (Phenomenological Truth)**: Every `computer.observe` and `screen.snap` mints a deterministic `observation_id` with `0..1000` normalized coordinates and d-separation action receipts (`retryable`, `required_next`, `side_effect`).
3. **Node 2 (Subsidiarity & Reversibility)**: All file deletions use `muse_files_trash`, moving files to `muse_pc_harness/.muse_trash` with a causal `trash_manifest.json` for instant 100% rollback.
