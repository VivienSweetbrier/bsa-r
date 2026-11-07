# Bsar build sheet — the queue, consolidated

*Assembled Nov 5, 2026, at Christopher's request, from the Nov 4 design session and
the Nov 5 Verse findings. All items are design-stage unless noted. Repo:
https://github.com/VivienSweetbrier/bsa-r*

## Already in the foundation

- **Flags as explicit threaded state.** Haskell algebraic differentiation constrains
  the implicit machines; the CPU flags — assembly's canonical hidden state machine —
  are a sum-typed value consumed by transitions, so flag clobbers are
  unrepresentable. (Done at design level; this is what the next four build on.)

## The four (in order)

1. **Region-typed arenas.** Design note written: `arena-design-note.md`.
   Bump allocation only, no individual frees; escape from a region is a type error;
   regions are machine states. SNES mapping: frame arena bulldozed at VBlank, room
   arena on exit, persistent data quarantined. Open questions on file: exhaustion
   bounds, DMA alignment proof, linear-register handshake, interrupt mini-arena.
2. **Session-typed DMA/VBlank protocol.** DMA transfers typed as sessions: a
   transfer is a protocol with a beginning (armed), a middle (bytes in flight,
   only inside VBlank), and an end (completed, state consumed) — so a transfer
   outside VBlank or a half-completed one is unrepresentable, the same way flag
   clobbers already are.
3. **Refinement types for lengths and wrap.** Lengths, bank crossings, and
   wraparound carried in the types: a buffer's type states its length bound and
   wrap behaviour; code that would overrun or wrap silently fails to typecheck.
4. **Coalgebraic equivalence for optimisation receipts.** Optimisations justified
   by coalgebraic (behavioural) equivalence: two machines that are observably the
   same may be swapped, and the swap carries a checkable equivalence witness — an
   optimisation receipt — rather than a shrug and a benchmark.

## North star

- **Engine vision.** Document written: `engine-vision.md`. A Godot-equivalent SNES
  engine: everything a state machine in a tree, editor runs the ROM live, MWL
  import-only into typed IR, append-only level directory {id, bank, offset, length,
  checksum} with no architectural level cap, doors to nonexistent levels are
  compile errors. BRUTAL SOCK is the dogfood; Seeds? is confirmed on-engine.

## The Verse additions (Nov 5 — source: Book of Verse, verselang.github.io)

Verse is Epic's language, designed by Simon Peyton Jones. Steal the semantics,
leave the runtime (Verse is garbage-collected and built for a persistent
metaverse of untrusted code; Bsar is arenas on 1990 hardware).

5. **Failure as control flow, with transactional rollback.** Verse expressions
   fail rather than throw; `<transacts>` functions execute speculatively and roll
   back every write if any guard fails. For Bsar: transitions that consume old
   state get transactional semantics — a transition posts whole or never
   occurred. Guard idiom worth copying: a bare assertion expression
   (`x <= limit`) that fails the whole computation if false — refusal-at-posting
   as syntax.
6. **Effect specifiers.** Every function declares what it may touch:
   `<computes>`, `<reads>`, `<writes>`, `<transacts>`, `<decides>`. For Bsar:
   effects declared per machine/verb, extending the flags work — declared state
   access instead of global fog, compiler-checked.
7. **"Just one language."** No preprocessor; the same constructs run at compile
   time and runtime. For Bsar the metacompiler: MWL-to-IR lowering, level
   directory checks, and door/exit validation performed as ordinary in-language
   compile-time evaluation rather than a separate macro layer.
