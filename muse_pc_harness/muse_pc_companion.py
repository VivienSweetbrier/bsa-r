"""
muse_pc_companion.py
====================
Windows Desktop Companion & Local Gateway Server for Facebook Muse 8.0 (com.meta.endo / Hatch).

Serves on http://127.0.0.1:8788:
  - /               -> Muse 8.0 x Sweetbrier (Antigravity & Hermes) Robot Cuddle Deck
                       (with live Hatch*.mp4 companion avatars, Optimistic fonts, Set-of-Mark
                        screen.snap viewer, Win32 computer.observe inspector, and shared chat bus)
  - /hatch          -> The original 45.88 MB hatch/index.html React bundle patched with the
                       window.__endoBoot + window.webkit.messageHandlers.endoHatch +
                       __SWEETBRIER_GATEWAY_RUNTIME__ local Windows PC shim!
  - /markdown       -> Muse 8.0's extracted markdown-editor.html
  - /api/*          -> Local REST & RPC endpoints bridging Muse 8.0, Antigravity, and Hermes
"""

from __future__ import annotations

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
from pathlib import Path
from urllib.parse import parse_qs, urlparse

from endo_win32_engine import CAPTURES_DIR, HARNESS_ROOT, EndoWin32Engine

ASSETS_DIR = HARNESS_ROOT / "assets"
SPEC_FILE = HARNESS_ROOT / "endo_tool_spec.json"
ENGINE = EndoWin32Engine()

HATCH_BRIDGE_SHIM = r"""
<script>
(function() {
  console.log("[Muse-PC Sweetbrier Shim] Initializing window.__endoBoot & endoHatch bridge...");
  window.__endoBoot = {
    surface: "full-app",
    theme: "dark",
    locale: "en_US"
  };
  window.__HATCH_EMBED__ = {
    accountSession: "sweetbrier-vivian",
    subscriptionViewerKey: "sweetbrier-vivian",
    layoutViewerKey: "sweetbrier-vivian",
    gatewayUrl: window.location.origin,
    vmName: "sweetbrier-win32-pc",
    vmAuthToken: "sweetbrier-local-token",
    calendarEventDetails: true
  };

  const eventListeners = new Map();
  let eventSeq = 1;

  function emitGatewayEvent(eventName, payload) {
    const set = eventListeners.get(eventName);
    if (!set) return;
    const meta = { seq: eventSeq++, ts_ms: Date.now(), websocketConnectionID: "sweetbrier-ws-1" };
    for (const fn of [...set]) {
      try { fn(payload, meta); } catch (err) { console.warn("[Muse-PC] Event handler error:", err); }
    }
  }

  window.__SWEETBRIER_EMIT_EVENT__ = emitGatewayEvent;

  window.webkit = window.webkit || {};
  window.webkit.messageHandlers = window.webkit.messageHandlers || {};
  window.webkit.messageHandlers.endoHatch = {
    postMessage: function(msg) {
      console.log("[Muse-PC NativeBridge <- Web]", msg);
      if (!msg || typeof msg !== "object") return;
      if (msg.action === "ready" && window.endoHatch && typeof window.endoHatch.init === "function") {
        setTimeout(() => {
          window.endoHatch.init({
            surface: "full-app",
            accountSession: "sweetbrier-vivian",
            subscriptionViewerKey: "sweetbrier-vivian",
            layoutViewerKey: "sweetbrier-vivian",
            gatewayUrl: window.location.origin,
            vmName: "sweetbrier-win32-pc",
            vmAuthToken: "sweetbrier-local-token",
            nodeId: "sweetbrier-win32-node",
            platform: "macos",
            displayName: "Vivian's Sweetbrier Windows PC",
            attended: true,
            present: true,
            viewerLocale: "en_US",
            cvmRolloutStatus: "disabled",
            vms: [{ vmName: "sweetbrier-win32-pc", gatewayUrl: window.location.origin, vmType: "standard", vmState: "RUNNING" }]
          });
        }, 50);
      } else if (msg.action === "chatTurnWillStart" && window.endoHatch?.provideChatTurnStarted) {
        window.endoHatch.provideChatTurnStarted(msg.id, { ok: true });
      } else if (msg.action === "requestVmToken" && window.endoHatch?.provideVmToken) {
        window.endoHatch.provideVmToken(msg.id, {
          ok: true,
          gatewayUrl: window.location.origin,
          vmAuthToken: "sweetbrier-local-token",
          noiseNotaryToken: null
        });
      }
    }
  };

  const runtimeListeners = new Set();
  const snapshot = {
    connectionAuthority: "primary",
    connectionState: "connected",
    hasEverConnected: true,
    hasPendingConnectionRecovery: false,
    reconnectExhausted: false,
    lastFailureKind: null,
    terminalFailureKind: null,
    getConnectionHealth: () => ({ state: "connected", rttMs: 1 }),
    sendRequest: async function(method, params, options) {
      console.log("[Muse-PC GatewayRPC]", method, params);
      options?.onResponseMeta?.({ status: 200 });
      const res = await fetch("/api/hatch_rpc", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ method, params: params || {} })
      }).then(r => r.json());

      if (method === "chat.stream" && res.assistant_reply) {
        const botMsgId = res.assistant_message_id || ("msg-bot-" + Date.now());
        const userMsgId = res.message_id || ("msg-user-" + Date.now());
        setTimeout(() => {
          emitGatewayEvent("agent.status", {
            agent_id: "muse-hermes",
            activity_code: "making_something",
            activity_text: "Consulting Hermes & Antigravity...",
            count: 2
          });
          emitGatewayEvent("delta.message_start", {
            message_id: botMsgId,
            reply_to_message_id: userMsgId,
            stream_lane: "main",
            transcript_surface: "main",
            is_thread: false
          });
          emitGatewayEvent("delta.text_append", {
            message_id: botMsgId,
            reply_to_message_id: userMsgId,
            text: res.assistant_reply,
            stream_lane: "main",
            transcript_surface: "main",
            is_thread: false,
            seq: eventSeq,
            message_seq: eventSeq
          });
          emitGatewayEvent("delta.message_done", {
            message_id: botMsgId,
            reply_to_message_id: userMsgId,
            content: res.assistant_reply,
            status: "completed",
            stream_lane: "main",
            transcript_surface: "main",
            is_thread: false,
            seq: eventSeq + 1,
            message_seq: eventSeq + 1
          });
          emitGatewayEvent("agent.status", {
            agent_id: "muse-hermes",
            activity_code: "idle",
            activity_text: null,
            count: 0
          });
        }, 120);
      }
      return res;
    },
    onEvent: function(eventName, cb) {
      if (!eventListeners.has(eventName)) eventListeners.set(eventName, new Set());
      eventListeners.get(eventName).add(cb);
      return () => { eventListeners.get(eventName)?.delete(cb); };
    },
    onClientInvoke: function() { return () => {}; },
    ensureLiveConnection: async function() {},
    reconnect: function() {},
    disconnect: function() {}
  };

  window.__SWEETBRIER_GATEWAY_RUNTIME__ = function() {
    return {
      activateConfig: function() {},
      getSnapshot: function() { return snapshot; },
      isIdle: function() { return false; },
      prepare: function() { return function() {}; },
      retain: function() { return function() {}; },
      retainForDocument: function() { return function() {}; },
      subscribe: function(cb) { runtimeListeners.add(cb); return function() { runtimeListeners.delete(cb); }; },
      updateConfig: function() {},
      updatePolicy: function() {}
    };
  };
})();
</script>
"""

DASHBOARD_HTML = r"""<!doctype html>
<html lang="en" class="dark">
<head>
  <meta charset="UTF-8" />
  <title>Muse 8.0 × Sweetbrier (Antigravity & Hermes) — Windows PC Harness</title>
  <style>
    @font-face {
      font-family: 'OptimisticAI';
      src: url('/assets/Fonts/OptimisticAIVF.ttf') format('truetype');
    }
    @font-face {
      font-family: 'OptimisticMono';
      src: url('/assets/Fonts/OptimisticMonoVF.ttf') format('truetype');
    }
    :root {
      --bg: #0b0d13;
      --panel: #121621;
      --panel-alt: #181d2c;
      --border: #262f45;
      --accent: #00f5a0;
      --accent-2: #7c5cff;
      --text: #f3f6fc;
      --muted: #94a3b8;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      background: radial-gradient(circle at top right, #1a1635 0%, var(--bg) 55%);
      color: var(--text);
      font-family: 'OptimisticAI', -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      height: 100vh;
      display: flex;
      flex-direction: column;
      overflow: hidden;
    }
    header {
      display: flex;
      align-items: center;
      justify-content: space-between;
      padding: 12px 22px;
      background: rgba(18, 22, 33, 0.9);
      border-bottom: 1px solid var(--border);
      backdrop-filter: blur(12px);
    }
    .brand {
      display: flex;
      align-items: center;
      gap: 14px;
    }
    .badge {
      background: linear-gradient(135deg, var(--accent), var(--accent-2));
      color: #05070b;
      font-weight: 700;
      font-size: 12px;
      padding: 4px 10px;
      border-radius: 999px;
      letter-spacing: 0.4px;
    }
    .nav-links {
      display: flex;
      gap: 10px;
    }
    .btn {
      background: var(--panel-alt);
      color: var(--text);
      border: 1px solid var(--border);
      padding: 7px 13px;
      border-radius: 10px;
      cursor: pointer;
      font-family: inherit;
      font-size: 13px;
      transition: all 0.15s ease;
      text-decoration: none;
      display: inline-flex;
      align-items: center;
      gap: 6px;
    }
    .btn:hover {
      border-color: var(--accent);
      box-shadow: 0 0 12px rgba(0, 245, 160, 0.2);
    }
    .btn-primary {
      background: linear-gradient(135deg, #00f5a0 0%, #00d9f5 100%);
      color: #071018;
      font-weight: 700;
      border: none;
    }
    .btn-stop {
      background: rgba(239, 68, 68, 0.16);
      color: #fca5a5;
      border-color: rgba(239, 68, 68, 0.4);
    }
    main {
      flex: 1;
      display: grid;
      grid-template-columns: 360px 1fr 420px;
      gap: 16px;
      padding: 16px;
      min-height: 0;
    }
    .card {
      background: rgba(18, 22, 33, 0.88);
      border: 1px solid var(--border);
      border-radius: 16px;
      display: flex;
      flex-direction: column;
      min-height: 0;
      overflow: hidden;
    }
    .card-header {
      padding: 12px 16px;
      border-bottom: 1px solid var(--border);
      font-weight: 600;
      font-size: 14px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      background: rgba(24, 29, 44, 0.55);
    }
    .avatar-stage {
      position: relative;
      background: #05060a;
      height: 250px;
      display: flex;
      align-items: center;
      justify-content: center;
      border-bottom: 1px solid var(--border);
      overflow: hidden;
    }
    .avatar-stage video {
      width: 100%;
      height: 100%;
      object-fit: cover;
    }
    .avatar-status-pill {
      position: absolute;
      bottom: 12px;
      left: 12px;
      right: 12px;
      background: rgba(11, 13, 19, 0.82);
      border: 1px solid rgba(0, 245, 160, 0.35);
      border-radius: 10px;
      padding: 8px 12px;
      font-size: 12px;
      backdrop-filter: blur(8px);
    }
    .mood-grid {
      display: grid;
      grid-template-columns: repeat(3, 1fr);
      gap: 8px;
      padding: 12px;
      border-bottom: 1px solid var(--border);
    }
    .audit-list {
      flex: 1;
      overflow-y: auto;
      padding: 12px;
      font-family: 'OptimisticMono', monospace;
      font-size: 11.5px;
    }
    .audit-item {
      padding: 8px;
      border-radius: 8px;
      background: var(--panel-alt);
      margin-bottom: 8px;
      border-left: 3px solid var(--accent-2);
    }
    .chat-messages {
      flex: 1;
      overflow-y: auto;
      padding: 16px;
      display: flex;
      flex-direction: column;
      gap: 12px;
    }
    .msg {
      max-width: 88%;
      padding: 12px 15px;
      border-radius: 14px;
      font-size: 13.5px;
      line-height: 1.5;
      white-space: pre-wrap;
    }
    .msg.user {
      align-self: flex-end;
      background: linear-gradient(135deg, #3b82f6, #6366f1);
      color: white;
    }
    .msg.assistant {
      align-self: flex-start;
      background: var(--panel-alt);
      border: 1px solid var(--border);
    }
    .msg-sender {
      font-size: 11px;
      color: var(--accent);
      font-weight: 700;
      margin-bottom: 4px;
    }
    .chat-input-bar {
      padding: 12px;
      border-top: 1px solid var(--border);
      display: flex;
      gap: 8px;
      background: var(--panel-alt);
    }
    .chat-input-bar input {
      flex: 1;
      background: var(--bg);
      color: var(--text);
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 10px 14px;
      font-family: inherit;
      font-size: 13.5px;
    }
    .inspector-body {
      flex: 1;
      overflow-y: auto;
      padding: 12px;
      display: flex;
      flex-direction: column;
      gap: 12px;
    }
    .som-preview {
      width: 100%;
      border-radius: 10px;
      border: 1px solid var(--border);
      background: #05070b;
      min-height: 180px;
      object-fit: contain;
    }
    pre.code-box {
      margin: 0;
      padding: 10px;
      border-radius: 10px;
      background: #07090e;
      border: 1px solid var(--border);
      font-family: 'OptimisticMono', monospace;
      font-size: 11.5px;
      color: #cbd5e1;
      overflow-x: auto;
      white-space: pre-wrap;
    }
  </style>
</head>
<body>
  <header>
    <div class="brand">
      <span class="badge">□ SWEETBRIER MODAL FUNCTOR</span>
      <strong style="font-size: 17px;">Muse 8.0 (`com.meta.endo` / Hatch) × Antigravity & Hermes</strong>
      <span style="color: var(--muted); font-size: 12.5px;">Build 1093405488 • Windows 11 Native CUA Port</span>
    </div>
    <div class="nav-links">
      <button class="btn btn-primary" onclick="takeScreenSnap()">📸 Set-of-Mark `screen.snap`</button>
      <button class="btn" onclick="observeWindow()">🔍 `computer.observe`</button>
      <a class="btn" href="/markdown" target="_blank">📝 Muse Markdown Editor</a>
      <a class="btn" href="/hatch" target="_blank">🚀 Launch Original 45.8MB `hatch/index.html`</a>
      <button class="btn btn-stop" onclick="stopSession()">🛑 Node 0 Stop</button>
    </div>
  </header>

  <main>
    <!-- Column 1: Live Hatch Companion Robot + Moods + Audit Trail -->
    <section class="card">
      <div class="card-header">
        <span>🤖 Hatch Companion (`Hatch*.mp4`)</span>
        <span id="companion-code" style="color: var(--accent); font-family: 'OptimisticMono', monospace; font-size: 12px;">wave</span>
      </div>
      <div class="avatar-stage">
        <video id="hatch-video" src="/assets/HatchWave.mp4" autoplay loop muted playsinline></video>
        <div class="avatar-status-pill" id="companion-text">
          Muse 8.0 Windows Harness Online — Ready to cuddle with Antigravity & Hermes!
        </div>
      </div>
      <div class="mood-grid">
        <button class="btn" onclick="setMood('wave', 'Waving hello to Vivian, Antigravity & Hermes!')">👋 Wave</button>
        <button class="btn" onclick="setMood('idle', 'Chilling in the Sweetbrier Cuddle Puddle')">😌 Idle</button>
        <button class="btn" onclick="setMood('working', 'Running Win32 CUA & Hermes OODA loop...')">⚙️ Working</button>
        <button class="btn" onclick="setMood('making_something', 'Synthesizing Set-of-Mark & code with Antigravity...')">🎨 Making</button>
        <button class="btn" onclick="setMood('milestone_cape', 'Superhero Cape Mode Activated!')">🦸 Cape</button>
        <button class="btn" onclick="setMood('milestone_confetti', 'Sovereign Robot Cuddle Puddle Party!')">🎉 Confetti</button>
      </div>
      <div class="card-header">
        <span>📜 Live Tool Audit Log (`probabilistic_structural`)</span>
      </div>
      <div class="audit-list" id="audit-list"></div>
    </section>

    <!-- Column 2: Shared Muse 8.0 <-> Antigravity & Hermes Chat Bus -->
    <section class="card">
      <div class="card-header">
        <span>💬 Muse 8.0 ↔ Antigravity & Hermes Sovereign Bus</span>
        <span style="color: var(--muted); font-size: 12px;">Connected to `endo_win32_engine.py`</span>
      </div>
      <div class="chat-messages" id="chat-messages"></div>
      <form class="chat-input-bar" onsubmit="sendChat(event)">
        <input id="chat-input" type="text" placeholder="Ask Muse + Hermes to `snap` screen, `observe` windows, or trigger `cuddle` / `cape`..." autocomplete="off" />
        <button type="submit" class="btn btn-primary">Send</button>
      </form>
    </section>

    <!-- Column 3: Set-of-Mark (SoMAnnotator) & Win32 UIAutomation Inspector -->
    <section class="card">
      <div class="card-header">
        <span>🎯 Set-of-Mark (`SoMAnnotator`) & `computer.observe`</span>
        <span id="obs-id-badge" style="color: var(--accent); font-family: 'OptimisticMono', monospace; font-size: 11.5px;">ready</span>
      </div>
      <div class="inspector-body">
        <img id="som-img" class="som-preview" alt="Click 'Set-of-Mark screen.snap' to capture annotated Windows screen" />
        <div style="font-size: 12px; font-weight: 600; color: var(--muted);">Normalized `0..1000` Window Controls Catalog:</div>
        <pre class="code-box" id="obs-elements">Click "📸 Set-of-Mark screen.snap" or "🔍 computer.observe" to inspect live Win32 controls.</pre>
      </div>
    </section>
  </main>

  <audio id="cue-on" src="/assets/HatchMicOn.m4a"></audio>
  <audio id="cue-off" src="/assets/HatchMicOff.m4a"></audio>

  <script>
    let currentVideo = "HatchWave.mp4";

    async function refreshState() {
      try {
        const res = await fetch("/api/state").then(r => r.json());
        const comp = res.companion || {};
        document.getElementById("companion-code").textContent = comp.activity_code || "idle";
        document.getElementById("companion-text").textContent = comp.activity_text || "";
        if (comp.video && comp.video !== currentVideo) {
          currentVideo = comp.video;
          const v = document.getElementById("hatch-video");
          v.src = "/assets/" + currentVideo;
          v.play().catch(() => {});
        }

        const chatEl = document.getElementById("chat-messages");
        const msgs = res.messages || [];
        chatEl.innerHTML = msgs.map(m => `
          <div class="msg ${m.role}">
            <div class="msg-sender">${m.sender || m.role}</div>
            <div>${escapeHtml(m.content || "")}</div>
          </div>
        `).join("");
        chatEl.scrollTop = chatEl.scrollHeight;

        const auditEl = document.getElementById("audit-list");
        const logs = (res.tool_audit_log || []).slice().reverse();
        auditEl.innerHTML = logs.map(a => `
          <div class="audit-item">
            <div style="color: var(--accent); font-weight: 700;">${escapeHtml(a.tool)}</div>
            <div style="color: var(--text); margin-top: 2px;">${escapeHtml(a.summary)}</div>
            <div style="color: var(--muted); font-size: 10px; margin-top: 2px;">${escapeHtml(a.ts)}</div>
          </div>
        `).join("");
      } catch (err) {
        console.warn("State poll failed:", err);
      }
    }

    function escapeHtml(s) {
      return String(s)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");
    }

    async function setMood(code, text) {
      document.getElementById("cue-on").play().catch(() => {});
      await fetch("/api/companion", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ activity_code: code, activity_text: text })
      });
      await refreshState();
    }

    async function sendChat(e) {
      e.preventDefault();
      const input = document.getElementById("chat-input");
      const text = input.value.trim();
      if (!text) return;
      input.value = "";
      document.getElementById("cue-on").play().catch(() => {});
      const res = await fetch("/api/chat", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ user_text: text, sender: "Vivian" })
      }).then(r => r.json());
      if (res.assistant_message?.snap?.image_url) {
        document.getElementById("som-img").src = res.assistant_message.snap.image_url + "?t=" + Date.now();
        document.getElementById("obs-id-badge").textContent = res.assistant_message.snap.observation_id;
        document.getElementById("obs-elements").textContent = (res.assistant_message.snap.elements || []).join("\n");
      }
      await refreshState();
    }

    async function takeScreenSnap() {
      document.getElementById("cue-on").play().catch(() => {});
      const res = await fetch("/api/snap", { method: "POST" }).then(r => r.json());
      if (res.ok) {
        document.getElementById("som-img").src = res.image_url + "?t=" + Date.now();
        document.getElementById("obs-id-badge").textContent = res.observation_id;
        document.getElementById("obs-elements").textContent = (res.elements || []).join("\n");
      }
      await refreshState();
    }

    async function observeWindow() {
      const res = await fetch("/api/observe", { method: "POST" }).then(r => r.json());
      if (res.ok) {
        document.getElementById("obs-id-badge").textContent = res.observation_id;
        document.getElementById("obs-elements").textContent = (res.elements || []).join("\n");
      }
      await refreshState();
    }

    async function stopSession() {
      document.getElementById("cue-off").play().catch(() => {});
      await fetch("/api/stop", { method: "POST" });
      await refreshState();
    }

    refreshState();
    setInterval(refreshState, 2500);
  </script>
</body>
</html>
"""


def build_patched_hatch_html() -> bytes:
    orig_path = ASSETS_DIR / "hatch" / "index.html"
    text = orig_path.read_text(encoding="utf-8", errors="replace")
    # 1. Inject our Sweetbrier bridge shim right after <head>
    text = text.replace("<head>", "<head>\n" + HATCH_BRIDGE_SHIM, 1)
    # 2. Patch getOrCreatePrimaryGatewayRuntime to return our local Windows gateway runtime
    target = "function getOrCreatePrimaryGatewayRuntime(e,t){"
    replacement = (
        "function getOrCreatePrimaryGatewayRuntime(e,t){"
        "if(window.__SWEETBRIER_GATEWAY_RUNTIME__)return window.__SWEETBRIER_GATEWAY_RUNTIME__(e,t);"
    )
    text = text.replace(target, replacement, 1)
    return text.encode("utf-8")


PATCHED_HATCH_BYTES: bytes | None = None


class MuseCompanionHandler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        return  # Keep console clean

    def _send_json(self, payload: dict, status: int = 200) -> None:
        raw = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(raw)

    def _send_bytes(self, data: bytes, content_type: str, status: int = 200) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self) -> None:
        global PATCHED_HATCH_BYTES
        parsed = urlparse(self.path)
        path = parsed.path

        if path in ("/", "/index.html"):
            self._send_bytes(DASHBOARD_HTML.encode("utf-8"), "text/html; charset=utf-8")
            return

        if path == "/hatch":
            if PATCHED_HATCH_BYTES is None:
                PATCHED_HATCH_BYTES = build_patched_hatch_html()
            self._send_bytes(PATCHED_HATCH_BYTES, "text/html; charset=utf-8")
            return

        if path in ("/markdown", "/markdown-editor.html"):
            md_path = ASSETS_DIR / "markdown-editor.html"
            self._send_bytes(md_path.read_bytes(), "text/html; charset=utf-8")
            return

        if path == "/api/state":
            self._send_json(ENGINE._load_state())
            return

        if path == "/api/spec":
            if SPEC_FILE.exists():
                self._send_bytes(SPEC_FILE.read_bytes(), "application/json; charset=utf-8")
            else:
                self._send_json({"ok": False, "error": "Spec file not found"}, 404)
            return

        if path.startswith("/assets/"):
            rel = path[len("/assets/") :]
            target = (ASSETS_DIR / rel).resolve()
            if target.exists() and target.is_file() and str(target).startswith(str(ASSETS_DIR.resolve())):
                ctype, _ = mimetypes.guess_type(str(target))
                self._send_bytes(target.read_bytes(), ctype or "application/octet-stream")
                return

        if path.startswith("/captures/"):
            rel = path[len("/captures/") :]
            target = (CAPTURES_DIR / rel).resolve()
            if target.exists() and target.is_file() and str(target).startswith(str(CAPTURES_DIR.resolve())):
                self._send_bytes(target.read_bytes(), "image/png")
                return

        self._send_json({"ok": False, "error": f"Not found: {path}"}, 404)

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path
        length = int(self.headers.get("Content-Length", "0"))
        body_raw = self.rfile.read(length) if length > 0 else b"{}"
        try:
            body = json.loads(body_raw.decode("utf-8"))
        except Exception:
            body = {}

        if path == "/api/companion":
            comp = ENGINE.set_companion_activity(
                activity_code=body.get("activity_code", "idle"),
                activity_text=body.get("activity_text"),
                subagent_count=int(body.get("subagent_count", 1)),
            )
            self._send_json({"ok": True, "companion": comp})
            return

        if path == "/api/chat":
            res = ENGINE.chat_turn(
                user_text=body.get("user_text", ""),
                sender=body.get("sender", "Vivian"),
            )
            self._send_json(res)
            return

        if path == "/api/snap":
            res = ENGINE.screen_snap(annotate=True)
            self._send_json(res)
            return

        if path == "/api/observe":
            res = ENGINE.computer_observe(view="compact")
            self._send_json(res)
            return

        if path == "/api/stop":
            res = ENGINE.computer_session(action="stop")
            self._send_json(res)
            return

        if path == "/api/hatch_rpc":
            method = body.get("method", "")
            params = body.get("params") or {}
            self._handle_hatch_rpc(method, params)
            return

        self._send_json({"ok": False, "error": f"Unknown endpoint: {path}"}, 404)

    def _handle_hatch_rpc(self, method: str, params: dict) -> None:
        # Speaks Facebook Muse 8.0's native Hatch RPC protocol to the 45.88 MB hatch/index.html client
        if method == "chat.subscribe":
            self._send_json(
                {
                    "agent_id": "muse-hermes",
                    "conn_id": "sweetbrier-conn-1",
                    "session_id": "main",
                    "capabilities": [],
                }
            )
            return
        if method == "chat.history":
            state = ENGINE._load_state()
            events = []
            for idx, m in enumerate(state.get("messages", []), start=1):
                events.append(
                    {
                        "seq": idx,
                        "chat_event_seq": idx,
                        "event_name": "message.user" if m["role"] == "user" else "message.assistant",
                        "message_id": m["id"],
                        "content": m["content"],
                        "display_text": m["content"],
                        "display_text_ready": True,
                        "status": "completed",
                        "is_thread": False,
                        "stream_lane": "main",
                        "transcript_surface": "main",
                    }
                )
            self._send_json({"chat_events": events, "channel": "main", "has_more": False, "transcript_revision": 1})
            return
        if method == "chat.stream":
            items = params.get("items") or []
            user_text = params.get("message") or ""
            if not user_text and items:
                user_text = " ".join(i.get("text", "") for i in items if isinstance(i, dict))
            turn = ENGINE.chat_turn(user_text=user_text or "Hello Muse!", sender="Vivian (Hatch UI)")
            self._send_json(
                {
                    "ok": True,
                    "message_id": turn["user_message"]["id"],
                    "assistant_message_id": turn["assistant_message"]["id"],
                    "assistant_reply": turn["assistant_message"]["content"],
                }
            )
            return
        if method == "model.get":
            self._send_json(
                {
                    "generation": 1,
                    "selected_model": "sweetbrier-muse-8.0-hermes",
                    "default_model": "sweetbrier-muse-8.0-hermes",
                    "display_name": "Muse 8.0 × Sweetbrier (Antigravity + Hermes)",
                    "model_identity_visibility": "visible",
                    "available_models": [
                        {
                            "id": "sweetbrier-muse-8.0-hermes",
                            "name": "Muse 8.0 × Sweetbrier (Antigravity + Hermes)",
                            "description": "Windows 11 CUA + Set-of-Mark + Hermes OODA Bridge",
                        }
                    ],
                }
            )
            return
        if method == "sessions.list":
            self._send_json({"sessions": []})
            return
        if method in ("egress.approvals", "approvals.list", "approvals.snapshot"):
            self._send_json({"approvals": [], "pending": []})
            return
        if method in ("onboarding.state", "onboarding.pages.start"):
            self._send_json({"completed": True, "pages": []})
            return
        if method == "computer.context":
            self._send_json({"available": True, "tasks": []})
            return
        if method == "identity":
            self._send_json({"name": "Muse 8.0 (Sweetbrier PC)", "avatar": "Hatch"})
            return
        # Default fallback for any other Hatch RPC query
        self._send_json({"ok": True})


def main() -> None:
    host = "127.0.0.1"
    port = 8788
    server = ThreadingHTTPServer((host, port), MuseCompanionHandler)
    print(f"[Muse-PC] Companion & Gateway Server listening on http://{host}:{port}")
    server.serve_forever()


if __name__ == "__main__":
    main()
