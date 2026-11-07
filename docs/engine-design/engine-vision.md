# Bsar engine vision: a Godot for SNES, on MWL

*Draft for Christopher's red pen — Nov 4, 2026. Companion to `arena-design-note.md`.
Status: vision/architecture, not implementation. Flagship target: BRUTAL SOCK.*

## The one-sentence version

A game engine and editor for the SNES that is easy the way Godot is easy — scenes,
nodes, inspectors, one-click builds — built on Bsar's guarantees, and able to eat
the existing SMW hacking ecosystem's level format (MWL) with no architectural
ceiling on how many levels a game can contain.

## Why the Godot comparison is structural, not cosmetic

Godot won because of three decisions, and all three port:

1. **Everything is a scene; scenes compose into trees.** A level, an enemy, a HUD,
   a title screen — the same kind of object, nestable. Our version: everything is
   a *state machine*. Bsar already thinks in sum-typed machines with transitions
   that consume the old state, which is what a scene graph wants to be when it
   grows up. A node in the tree = a machine; the tree = their composition.
2. **The editor is the game's first scene.** Godot's editor runs in the engine.
   Our editor runs the ROM live (embedded emulator) so what you edit is what the
   hardware does — no export-and-pray.
3. **Scripting with a low floor.** Bsar is the scripting layer: Lua's shape, R's
   verbs, types underneath. A beginner writes behaviour in ten lines; the
   compiler still refuses to emit a flag clobber, an escaped pointer, or a DMA
   transfer outside VBlank. Ease at the surface, receipts at the bottom.

## The MWL pipeline

MWL is Lunar Magic's level format, and there is a generation of level design
sitting in it. The engine treats MWL as an *import* format, not a runtime format:

```
MWL file ──► importer ──► typed level IR ──► Bsar compiler ──► engine data
              (untrusted)    (checked)          (guarantees)
```

- The importer parses MWL completely defensively (it is an untrusted external
  format with decades of edge cases) and produces a **typed intermediate
  representation**: tile layers, sprite placements, exits, palettes as data the
  type system can see.
- Anything the IR cannot represent is reported at import time, in plain language,
  with the level and coordinates attached — never discovered at runtime.
- The runtime never parses MWL. It consumes engine data laid out for the
  hardware: arena-friendly, bank-disciplined, DMA-staged.

## Arbitrarily high level count

Vanilla SMW hard-codes a small level table; hacking tools inherited the shape of
that constraint for decades. The engine removes the ceiling by demoting "level"
from an architecture slot to a *data record*:

- Levels live in a **directory**: an append-only index of `{id, bank, offset,
  length, checksum}` entries, in expanded ROM space. Adding a level appends a
  directory entry and a data blob; nothing else in the ROM moves.
- Level IDs are plain numbers, not table positions, so the count is bounded by
  ROM size and the directory's address width, not by a fixed table: hundreds,
  thousands — the architecture does not care. (Honesty box: "arbitrary" means
  *no architectural cap*. The physical caps are ROM size and directory width,
  both chosen at project creation and both bigger than any sane game.)
- Because a level is data, the editor can also treat the directory as a library:
  levels sortable, taggable, reusable across projects — a level becomes an asset
  you can carry between games like a sprite sheet.
- Exits are references by level ID, checked by the compiler: a door to a level
  that does not exist is a *compile error*, listed with the source level and
  coordinates. (The SMW scene has shipped a thousand broken exits. This deletes
  that bug class socially, not just technically.)

## How the earlier bricks carry the engine

- **Flags as typed state** — sprite and player behaviour code can't silently
  corrupt each other through the processor status register.
- **Arenas** — frame arena for entities and particles, level arena for the
  current stage, persistent storage quarantined by the escape rule. The scene
  tree's lifetime and the memory geography are the same shape, which is why a
  node can own memory without owning a free() call.
- **Session-typed DMA** — the engine's renderer is a typed conversation with the
  PPU; user code requests uploads, the engine performs them inside the legal
  windows, and "wrote to VRAM during active display" is unrepresentable rather
  than a rite of passage.
- **Refinement types** — sprite counts, OAM budgets, tilemap dimensions:
  checked quantities, with errors phrased as the editor's plain-language
  diagnostics.

## The editor (the Godot half)

- Scene tree panel; level view importing/drawing in MWL terms so existing
  hackers feel at home on day one; entity inspector exposing the state machine
  (variants as states, transitions as arrows you can click).
- Live ROM preview; "why won't this compile" panel written like a helpful
  colleague, because our compiler errors carry reasons and provenance by design.
- One-click build to a flashable/emulatable ROM.
- BRUTAL SOCK is the dogfood: if the flagship can't be built in it, the engine
  isn't done.

## Open questions

1. **How much of Lunar Magic's surface do we mirror?** Familiarity is adoption;
   divergence is correctness. Current lean: mirror the level-editing gestures,
   diverge everywhere the old tool was shaped by the ROM's limits rather than
   by the designer's intent.
2. **ExGFX / custom graphics pipeline**: typed asset pipeline with palette and
   VRAM-budget checking at build time. Design note to follow.
3. **Music**: SPC700 audio is its own machine; by symmetry it wants the same
   treatment (typed driver interface, session-typed uploads). Park until the
   visual pipeline stands.
4. **Save/persistence format**: engine-level standard, checksummed, so every
   game built on the engine inherits sane saves.

## Second dogfood: the Seeds game (added Nov 4, his question)

The Seeds descent (Min & Cress, Pokemon-shaped, Digimon World 2's dungeon
bones) runs on this engine, and parts of it fit *better* than the platformer:

- **Maps are levels.** Towns, roads, and hell-floors are directory records with
  IDs; warps are exits, so the compile-time exit checker covers RPG warps —
  a warp to a missing map is a build error, not a soft-lock shipped to players.
- **The descent wants the arbitrary count.** Hell is arbitrarily big; a game
  about going down forever cannot be built on a fixed level table. The
  directory model is the first architecture where the fiction and the file
  format agree about infinity.
- **Battles are machines.** A doubles battle is a state machine; the room
  moves (Trick Room, Wonder Room, Magic Room and kin) are *variant operators*
  on the field state — exactly sum-type machinery. The battle system's weird
  verbs stop being special cases and become typed transitions.
- **Data tables are data.** Species, moves, stats: typed tables with
  refinement-checked ranges, imported and validated like levels, so a typo'd
  stat is a build error with coordinates.

## The slogan

Lunar Magic proved one person with the right tool can out-produce a studio.
The engine's bet: give that person a compiler that refuses their worst bugs,
a level format with no ceiling, and an editor that treats them like a game
designer instead of a ROM surgeon — and SNES dev stops being archaeology
and becomes a medium again.
