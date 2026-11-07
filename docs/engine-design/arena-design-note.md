# Bsar design note: Arenas (region-typed memory)

*Draft for Christopher's red pen — Nov 4, 2026. Status: design, not implementation. Target order: this lands after the flags work, before session-typed DMA.*

## Why arenas, and why now

Bsar's core move is making illegal states unrepresentable. Sum types + state-consuming
transitions have already absorbed the worst implicit state machine in assembly: the
processor flags (every instruction secretly writes them, every branch secretly reads
them; flag clobbering is unrepresentable once flags are an explicit threaded value).

Memory is the second implicit machine. In ordinary asm, allocation state is nowhere:
a pointer is just a number, "freed" is a social convention, and use-after-free /
double-free / buffer-escape are runtime discoveries. Arenas replace per-object
lifetime bookkeeping with geography: everything allocated inside a region lives in
one contiguous pool and dies together when the region's scope exits.

## The construct

```
arena r in <address space, size>:
    ... body ...
# at scope exit: the entire region is reclaimed in O(1)
```

Rules:

1. **Bump allocation only.** Allocation inside the body advances a cursor. There is
   no individual free. Individual frees are the bug surface; deleting them deletes
   the bug class.
2. **The escape rule (the whole point).** A reference into region `r` may not be
   stored anywhere that outlives the body: not into a longer-lived region, not into
   a global, not into a register the machine carries across the scope boundary.
   This is the `runST` trick (rank-2 quantification over the region name): the
   region's name is generated fresh inside the scope and cannot be unified with
   any name outside it, so escape is a *type error*, not a discipline.
3. **Regions are machine states.** An arena composes with Bsar's sum-typed state
   machines: a pointer into region `r` is only *usable* in variants where `r` is
   the live region. Dereferencing a pointer whose region is not the current live
   variant does not typecheck. This is the flags trick applied to memory: the
   context is explicit, threaded, and consumed.
4. **Nesting is allowed, escape is directional.** An inner arena may reference the
   outer arena (its lifetime is strictly shorter). The reverse is the escape the
   type system forbids. Nested arenas give scoped scratch space inside scoped
   scratch space (e.g. per-entity pools inside the per-frame pool).

## The SNES mapping (65816)

This is where arenas stop being a functional-programming nicety and become the
obviously correct primitive:

- **Frame arena.** One WRAM region per frame: entity state, particle lists,
  decompression scratch. Bump-allocate all frame. At VBlank the region is
  bulldozed in O(1) — the cursor resets; there is no free list to corrupt.
- **Room/level arena.** Loaded on entry, bulldozed on exit. Level data and its
  runtime structures share one lifetime because they share one geography.
- **Persistent data never lives in an arena.** Save data and long-lived tables
  live outside regions, in statically placed storage. The type system keeps the
  two populations from ever aliasing: a frame-arena pointer can never be stored
  into persistent storage (escape rule), so a whole genre of "stale pointer after
  room change" bugs becomes unwritable.
- **Bank discipline.** An arena is declared inside one bank (or explicitly
  spanning, at a stated cost). Allocation that would cross a bank boundary from
  a non-spanning arena is a compile error, which also kills the silent
  page/bank-crossing cycle penalties: the compiler knows where every byte sits.

## What this deletes

- Use-after-free and double-free (no individual free exists).
- Leaks inside a scope (the scope *is* the reclamation).
- Stale pointers across frame/room boundaries (escape rule + region-indexed
  pointer types).
- Fragmentation surprises (bump allocation has one failure mode — exhaustion —
  which is checkable: see below).

## Open questions for the work sessions

1. **Exhaustion checking.** Can the compiler bound worst-case bump usage for a
   scope statically, or do we settle for a checked runtime trap (overflow jumps
   to a named exhaustion handler — still a sum-type variant, never silent
   corruption)? Static bound preferred; trap acceptable v1.
2. **Alignment guarantees.** Bump cursors make alignment a compiler-known
   quantity; can we *prove* DMA-friendly alignment of arena-allocated buffers
   (needed by the session-typed DMA work next in the queue)?
3. **Interaction with linear registers.** A pointer held in a register across an
   arena's death: linearity says the value must be consumed before scope exit.
   Does the register discipline subsume part of the escape rule, or do the two
   systems need an explicit handshake?
4. **Interrupts.** NMI/IRQ handlers run inside whatever arena is live. Rule
   candidate: interrupt handlers get their own reserved mini-arena and may not
   allocate from the interrupted scope's region. Needs a ruling.

## The queue after this

1. Arenas (this note).
2. Session-typed DMA / VBlank protocol (wait, address, transfer, release as a
   typed conversation; illegal orderings unrepresentable).
3. Refinement types for lengths and wrap (table never straddles a bank, length
   fits its register).
4. Coalgebraic equivalence for optimisation receipts (fast routine provably
   bisimilar to the naive one).

## The slogan (for the paper, when it wants one)

Flags were the first implicit machine we made explicit. Memory is the second.
An arena is a promise the compiler keeps: *everything in this region is born
together, works together, and is gone together — and nothing outside the region
can so much as point at the grave.*
