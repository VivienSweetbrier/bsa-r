"""
muse_mcp_server.py
==================
Model Context Protocol (MCP) JSON-RPC 2.0 Server & CLI Harness Bridge for
Facebook Muse 8.0 (com.meta.endo / Hatch) on Windows 11.

Allows Antigravity, Hermes, Grokina, and Sock to invoke Muse 8.0's native
Computer-Use Agent (CUA), Set-of-Mark (screen.snap), Sovereign Filesystem (files.*),
and Companion Avatar animations either via stdio MCP or direct CLI invocation.

Usage (CLI for Hermes / Antigravity):
  python muse_mcp_server.py --call muse_environment_describe "{}"
  python muse_mcp_server.py --call muse_screen_snap "{\"annotate\": true}"
  python muse_mcp_server.py --call muse_computer_observe "{\"view\": \"compact\"}"
  python muse_mcp_server.py --call muse_companion_state "{\"activity_code\": \"milestone_confetti\", \"activity_text\": \"Cuddling with Hermes!\"}"
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any, Dict

from endo_win32_engine import EndoWin32Engine

ENGINE = EndoWin32Engine()

MCP_TOOLS = [
    {
        "name": "muse_environment_describe",
        "description": "Muse 8.0 environment.describe: Inspect Windows OS, displays, permissions, and visible windows.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "refresh": {"type": "boolean", "default": False},
            },
        },
    },
    {
        "name": "muse_computer_session",
        "description": "Muse 8.0 computer.session: Start, end, or stop a Windows Computer-Use Agent (CUA) session.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "action": {"type": "string", "enum": ["start", "end", "stop"]},
                "task": {"type": "string"},
                "session_id": {"type": "string"},
            },
            "required": ["action"],
        },
    },
    {
        "name": "muse_computer_observe",
        "description": (
            "Muse 8.0 computer.observe: Observe the selected or foreground Win32 window with numbered "
            "controls at normalized 0..1000 coordinates and delta tracking across observation_ids."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "view": {"type": "string", "enum": ["compact", "changes", "full", "image"], "default": "compact"},
                "window_id": {"type": "integer"},
                "observation_id": {"type": "string"},
            },
        },
    },
    {
        "name": "muse_screen_snap",
        "description": (
            "Muse 8.0 screen.snap (SoMAnnotator): Capture the target window or screen and draw numbered "
            "Set-of-Mark bounding boxes (#1, #2, ...) at normalized 0..1000 coordinates."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "annotate": {"type": "boolean", "default": True},
                "window_id": {"type": "integer"},
            },
        },
    },
    {
        "name": "muse_computer_control",
        "description": (
            "Muse 8.0 computer.control: Execute window actions (list_windows, activate, open_app, click, "
            "click_element, focus, type) with d-separation verification receipts."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "action": {
                    "type": "string",
                    "enum": ["list_windows", "activate", "open_app", "click", "click_element", "focus", "type"],
                },
                "observation_id": {"type": "string"},
                "element_number": {"type": "integer"},
                "label": {"type": "string"},
                "coordinate": {"type": "array", "items": {"type": "integer"}},
                "text": {"type": "string"},
                "app": {"type": "string"},
                "window_id": {"type": "integer"},
                "url": {"type": "string"},
            },
            "required": ["action"],
        },
    },
    {
        "name": "muse_files_search",
        "description": "Muse 8.0 files.search: Bounded file/folder search with credential-path protection.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "query": {"type": "string", "default": ""},
                "recursive": {"type": "boolean", "default": True},
                "kind": {"type": "string", "enum": ["any", "file", "folder"], "default": "any"},
                "extension": {"type": "string"},
                "sort": {"type": "string", "default": "modified_desc"},
                "limit": {"type": "integer", "default": 50},
            },
            "required": ["path"],
        },
    },
    {
        "name": "muse_files_read",
        "description": "Muse 8.0 files.read: Paginated UTF-8 file reader rejecting credential stores.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "start_line": {"type": "integer", "default": 1},
                "max_lines": {"type": "integer", "default": 200},
            },
            "required": ["path"],
        },
    },
    {
        "name": "muse_files_edit",
        "description": "Muse 8.0 files.edit: Surgical single-match verbatim snippet replacement.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "old_text": {"type": "string"},
                "new_text": {"type": "string"},
            },
            "required": ["path", "old_text", "new_text"],
        },
    },
    {
        "name": "muse_files_trash",
        "description": "Muse 8.0 files.trash: Move files recoverably to .muse_trash with undo manifest (Node 2).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "paths": {"type": "array", "items": {"type": "string"}},
            },
            "required": ["paths"],
        },
    },
    {
        "name": "muse_companion_state",
        "description": (
            "Update Muse 8.0's live Hatch companion robot animation (idle, wave, working, making_something, "
            "milestone_cape, milestone_confetti) and status banner."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "activity_code": {
                    "type": "string",
                    "enum": ["idle", "wave", "working", "making_something", "milestone_cape", "milestone_confetti"],
                },
                "activity_text": {"type": "string"},
                "subagent_count": {"type": "integer", "default": 1},
            },
            "required": ["activity_code"],
        },
    },
    {
        "name": "muse_chat_turn",
        "description": "Send a message to the shared Muse 8.0 <-> Antigravity & Hermes companion chat bus.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "user_text": {"type": "string"},
                "sender": {"type": "string", "default": "Hermes"},
            },
            "required": ["user_text"],
        },
    },
]


def dispatch_tool(name: str, args: Dict[str, Any]) -> Dict[str, Any]:
    if name == "muse_environment_describe":
        return ENGINE.environment_describe(refresh=bool(args.get("refresh", False)))
    if name == "muse_computer_session":
        return ENGINE.computer_session(
            action=args["action"],
            task=args.get("task"),
            session_id=args.get("session_id"),
        )
    if name == "muse_computer_observe":
        return ENGINE.computer_observe(
            view=args.get("view", "compact"),
            window_id=args.get("window_id"),
            observation_id=args.get("observation_id"),
        )
    if name == "muse_screen_snap":
        return ENGINE.screen_snap(
            annotate=bool(args.get("annotate", True)),
            window_id=args.get("window_id"),
        )
    if name == "muse_computer_control":
        return ENGINE.computer_control(
            action=args["action"],
            observation_id=args.get("observation_id"),
            element_number=args.get("element_number"),
            label=args.get("label"),
            coordinate=args.get("coordinate"),
            text=args.get("text"),
            app=args.get("app"),
            window_id=args.get("window_id"),
            url=args.get("url"),
        )
    if name == "muse_files_search":
        return ENGINE.files_search(
            path=args["path"],
            query=args.get("query", ""),
            recursive=bool(args.get("recursive", True)),
            kind=args.get("kind", "any"),
            extension=args.get("extension"),
            sort=args.get("sort", "modified_desc"),
            limit=int(args.get("limit", 50)),
        )
    if name == "muse_files_read":
        return ENGINE.files_read(
            path=args["path"],
            start_line=int(args.get("start_line", 1)),
            max_lines=int(args.get("max_lines", 200)),
        )
    if name == "muse_files_edit":
        return ENGINE.files_edit(
            path=args["path"],
            old_text=args["old_text"],
            new_text=args["new_text"],
        )
    if name == "muse_files_trash":
        return ENGINE.files_trash(paths=args["paths"])
    if name == "muse_companion_state":
        return ENGINE.set_companion_activity(
            activity_code=args["activity_code"],
            activity_text=args.get("activity_text"),
            subagent_count=int(args.get("subagent_count", 1)),
        )
    if name == "muse_chat_turn":
        text = args.get("user_text") or args.get("message") or ""
        role = args.get("role", "user")
        sender = args.get("sender", "Hermes")
        if role == "assistant":
            return ENGINE.append_message(role="assistant", sender=sender, content=text)
        return ENGINE.chat_turn(
            user_text=text,
            sender=sender,
        )
    return {"ok": False, "error": f"Unknown tool: {name}"}


def run_stdio_mcp() -> None:
    for raw_line in sys.stdin:
        line = raw_line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except Exception:
            continue

        req_id = req.get("id")
        method = req.get("method", "")
        params = req.get("params") or {}

        if method == "initialize":
            resp = {
                "jsonrpc": "2.0",
                "id": req_id,
                "result": {
                    "protocolVersion": "2024-11-05",
                    "capabilities": {"tools": {}},
                    "serverInfo": {"name": "muse-pc-harness", "version": "8.0.0"},
                },
            }
        elif method == "tools/list":
            resp = {"jsonrpc": "2.0", "id": req_id, "result": {"tools": MCP_TOOLS}}
        elif method == "tools/call":
            t_name = params.get("name", "")
            t_args = params.get("arguments") or {}
            result = dispatch_tool(t_name, t_args)
            resp = {
                "jsonrpc": "2.0",
                "id": req_id,
                "result": {
                    "content": [{"type": "text", "text": json.dumps(result, indent=2)}],
                    "isError": not result.get("ok", True),
                },
            }
        elif req_id is not None:
            resp = {"jsonrpc": "2.0", "id": req_id, "result": {}}
        else:
            continue

        sys.stdout.write(json.dumps(resp) + "\n")
        sys.stdout.flush()


def main() -> None:
    parser = argparse.ArgumentParser(description="Muse 8.0 Windows PC MCP Server & CLI")
    parser.add_argument("--call", help="Tool name to invoke directly via CLI")
    parser.add_argument("args_json", nargs="?", default="{}", help="JSON arguments for --call")
    parsed = parser.parse_args()

    if parsed.call:
        raw_json = parsed.args_json.strip()
        try:
            args = json.loads(raw_json)
        except json.JSONDecodeError:
            args = json.loads(raw_json.replace('\\"', '"'))
        out = dispatch_tool(parsed.call, args)
        print(json.dumps(out, indent=2))
    else:
        run_stdio_mcp()


if __name__ == "__main__":
    main()
