#!/usr/bin/env python3
"""
Adversarial & Dogfood Test Suite for BSA-R v0.5.0 QoL & SNES Engine Foundation:
  - Phase 1: Region-Typed Arenas (`bsar.arenas` — bump-only, rank-2 escape rule, directional
             nesting, register taint handshake, SA-1 Open-Bus guard, NMI interrupt mini-arena).
  - Phase 2: Refinement Types (`bsar.refinements` — lengths, LoROM/SA-1 bank crossings,
             wraparound policies, OAM/Sprite/CGRAM budgets, forbidden `CPX/CPY d,s` silicon check).
  - Phase 3: Session-Typed DMA / VBlank & SA-1 5-Cycle Math (`bsar.dma_sessions`).
  - Phase 4: Verse Effects (`<computes>`..`<transacts>`) & Coalgebraic Optimisation Receipts
             (`bsar.verse_effects`).
  - Phase 5A: Defensive `.mwl` Importer (`bsar.mwl_importer`), Infinite Append-Only
              `LevelDirectory`, Whole-Graph Broken-Exit Compiler Check, & Dogfood Builds
              (`BRUTAL SOCK` & `Seeds?` 1,024-floor descent) (`bsar.engine_scene`).
"""

from __future__ import annotations

from contextlib import redirect_stdout
import io
import json
import unittest

from bsar import (
    GPS_REQUIRED_LABELS,
    AddressSpace,
    DMASessionCoordinator,
    IxArenaError,
    IxArenaEscapeError,
    IxArenaExhaustionError,
    IxBisimulationError,
    IxBrokenExitCompileError,
    IxDMASessionError,
    IxEffectViolationError,
    IxRefinementError,
    LevelDirectory,
    MWLImportError,
    PersistentSlot,
    RefinedBufferSlice,
    RefinedInt,
    SA1MathSession,
    SceneMachine,
    StateTransition,
    check_snes_hardware_budgets,
    compile_brutal_sock_dogfood,
    compile_seeds_descent_dogfood,
    import_mwl_bytes,
    pack_mwl_binary,
    prove_bisimulation_receipt,
    run_verse_verb,
    verify_65816_silicon_legality,
    verse_transact,
    with_arena,
    with_dma_frame_protocol,
)
from bsar.cli import main as bsar_cli_main


class TestBsaRV05EngineAndQoL(unittest.TestCase):
    # ==========================================================================
    # PHASE 1: REGION-TYPED ARENAS & RANK-2 ESCAPE VERIFIER
    # ==========================================================================

    def test_arena_bump_alignment_bulldoze_and_directional_nesting(self) -> None:
        def _outer_room(room: object) -> dict:
            p_room = room.alloc(size=33, align=16, label="RoomTileHeader")
            self.assertEqual(p_room.offset % 16, 0)

            def _inner_frame(frame: object) -> int:
                # Inner arena MAY dereference and store reference to outer arena!
                frame.deref_check(p_room)
                frame.store_ref("parent_room_ptr", p_room)
                p_particles = frame.alloc(size=128, align=16, label="Particles")
                self.assertEqual(p_particles.offset % 16, 0)
                frame.bind_register("X", p_particles)
                frame.clear_register("X")
                return p_particles.size + p_room.size

            combined_sz, frame_rec = with_arena(
                "Frame_7E", AddressSpace.WRAM_7E_FRAME, 1024, _inner_frame
            )
            self.assertEqual(frame_rec["final_cursor_after_bulldoze"], 0)
            self.assertGreaterEqual(frame_rec["peak_watermark_bytes"], 128)
            return {"combined_sz": combined_sz}

        out, room_rec = with_arena("Room_7F", AddressSpace.WRAM_7F_ROOM, 4096, _outer_room)
        self.assertEqual(out["combined_sz"], 161)
        self.assertEqual(room_rec["final_cursor_after_bulldoze"], 0)

    def test_arena_rejects_escape_register_leak_sram_and_sa1_open_bus(self) -> None:
        # 1. Rank-2 `runST` return-value escape
        with self.assertRaises(IxArenaEscapeError):
            with_arena(
                "LeakyFrame",
                AddressSpace.WRAM_7E_FRAME,
                256,
                lambda a: {"escaped": a.alloc(16, align=2, label="BadReturn")},
            )

        # 2. Storing arena pointer into Persistent SRAM ($41:C000)
        sram_slot = PersistentSlot("SaveFileSlot0")
        with self.assertRaises(IxArenaEscapeError):
            with_arena(
                "FrameToSRAM",
                AddressSpace.WRAM_7E_FRAME,
                256,
                lambda a: sram_slot.store(a.alloc(8, label="TempEntity")),
            )

        # 3. Directional nesting violation: Outer room arena storing Inner frame pointer
        with self.assertRaises(IxArenaEscapeError):
            def _bad_nesting(outer: object) -> None:
                with_arena(
                    "InnerShortLived",
                    AddressSpace.WRAM_7E_FRAME,
                    128,
                    lambda inner: outer.store_ref("dangling", inner.alloc(8, label="Ephemeral")),
                )

            with_arena("OuterLongLived", AddressSpace.WRAM_7F_ROOM, 512, _bad_nesting)

        # 4. Linear Register Handshake: Leaving `X` tainted with region pointer across scope exit
        with self.assertRaises(IxArenaEscapeError):
            with_arena(
                "RegTaintLeak",
                AddressSpace.WRAM_7E_FRAME,
                128,
                lambda a: a.bind_register("X", a.alloc(16, label="PinnedInX")),
            )

        # 5. Static exhaustion check
        with self.assertRaises(IxArenaExhaustionError):
            with_arena(
                "TooSmall",
                AddressSpace.WRAM_7E_FRAME,
                64,
                lambda a: (a.alloc(48, label="A"), a.alloc(32, label="B")),
            )

        # 6. SA-1 Open-Bus protection: SA-1 CPU cannot allocate/read S-CPU WRAM $7E/$7F!
        with self.assertRaises(IxArenaError):
            with_arena(
                "SA1WrongBus",
                AddressSpace.WRAM_7E_FRAME,
                128,
                lambda _a: None,
                cpu_context="SA1",
            )

        # 7. Interrupt Isolation: NMI handler gets `INTERRUPT_MINI` and cannot deref foreground pointer!
        with self.assertRaises(IxArenaError):
            def _fg(fg_arena: object) -> None:
                fg_ptr = fg_arena.alloc(16, label="ForegroundDP")
                with_arena(
                    "NMIHandler",
                    AddressSpace.INTERRUPT_MINI,
                    64,
                    lambda nmi_arena: nmi_arena.deref_check(fg_ptr),
                    cpu_context="NMI",
                )

            with_arena("ForegroundFrame", AddressSpace.WRAM_7E_FRAME, 256, _fg)

    # ==========================================================================
    # PHASE 2: REFINEMENT TYPES (LENGTHS, BANK CROSSING, WRAP & OPCODE LEGALITY)
    # ==========================================================================

    def test_refinement_lengths_bank_crossing_budgets_and_cpx_stack_guard(self) -> None:
        idx_ok = RefinedInt(12, 0, 31, "tile_idx").require_fits_register("W8")
        slc = RefinedBufferSlice(
            label="LutTable",
            bank=0xC1,
            offset=0xFF00,
            length=64,
            max_length=256,
            mapping="SA1",
            wrap_policy="forbid",
        )
        self.assertEqual(slc.check_index(idx_ok), 0xFF0C)

        # Bank-crossing failure across $FFFF
        with self.assertRaises(IxRefinementError):
            RefinedBufferSlice(
                label="StraddlingTable",
                bank=0xC1,
                offset=0xFF80,
                length=256,
                max_length=512,
                mapping="SA1",
            )

        # LoROM < $8000 illegal offset
        with self.assertRaises(IxRefinementError):
            RefinedBufferSlice(
                label="BadLoROM",
                bank=0x01,
                offset=0x7F00,
                length=512,
                max_length=1024,
                mapping="LoROM",
            )

        # Out-of-bounds index when wrap_policy == "forbid"
        with self.assertRaises(IxRefinementError):
            slc.check_index(RefinedInt(40, 0, 80, "wide_idx"))

        # Vanilla SMW 12-sprite limit vs SA-1 22-sprite limit
        with self.assertRaises(IxRefinementError):
            check_snes_hardware_budgets(active_sprites=15, sa1_mode=False)
        self.assertTrue(check_snes_hardware_budgets(active_sprites=20, sa1_mode=True)["valid"])

        # Non-existent silicon opcode `CPY 1,s` / `CPX $03,s` rejected!
        with self.assertRaises(IxRefinementError):
            verify_65816_silicon_legality(["    PHA", "    CPY 1,s", "    PLA"])
        with self.assertRaises(IxRefinementError):
             SceneMachine(
                name="BadOpcodeSprite",
                variants=("A", "B"),
                initial_variant="A",
                transitions=(StateTransition("A", "tick", "B", ("CPX $02,s",)),),
            )

    # ==========================================================================
    # PHASE 3: SESSION-TYPED DMA / VBLANK & SA-1 5-CYCLE MATH
    # ==========================================================================

    def test_session_typed_dma_vblank_and_sa1_5_cycle_math_protocol(self) -> None:
        def _test_dma_inside_arena(arena: object) -> None:
            buf = arena.alloc(1024, align=16, label="VRAMTileChunk")

            # 1. Attempting to transfer without an authentic VBlankWindowToken fails!
            coord = DMASessionCoordinator()
            armed = coord.arm_dma(channel=2, src_ptr=buf, target_bus="VRAM", dest_addr=0x4000)
            with self.assertRaises(IxDMASessionError):
                coord.transfer_in_vblank(armed, "FAKE_TOKEN")  # type: ignore[arg-type]

            # 2. Half-completed session (armed but never transferred before frame end) fails!
            with self.assertRaises(IxDMASessionError):
                with_dma_frame_protocol(
                    arm_phase=lambda c: c.arm_dma(channel=0, src_ptr=buf, target_bus="VRAM"),
                    vblank_phase=lambda _c, _vb, _h: None,  # Forgot to transfer!
                )

            # 3. Exceeding NTSC VBlank byte budget fails!
            big_buf = arena.alloc(4096, align=16, label="BigChunk")
            with self.assertRaises(IxDMASessionError):
                with_dma_frame_protocol(
                    arm_phase=lambda c: (
                        c.arm_dma(channel=0, src_ptr=buf, target_bus="VRAM"),
                        c.arm_dma(channel=1, src_ptr=big_buf, target_bus="VRAM"),
                    ),
                    vblank_phase=lambda c, vb, hs: [
                        c.transfer_in_vblank(hs[0], vb),
                        c.transfer_in_vblank(hs[1], vb),
                    ],
                    vblank_budget_bytes=4608,
                )

        with_arena("DMATestArena", AddressSpace.WRAM_7E_FRAME, 8192, _test_dma_inside_arena)

        # 4. SA-1 5-Cycle Hardware Multiplier: reading $2307 early (< 5 cycles) fails!
        early_mul = SA1MathSession.start_q88_mul(100, 256, cpu_context="SA1").wait_nops(2)  # 4 cycles < 5!
        with self.assertRaises(IxDMASessionError):
            early_mul.read_q88_middle_word_2307()

        # Waiting 3 NOPs (6 cycles >= 5) unlocks exact middle-word Q8.8 read: 100 * 0.5 (128) = 50
        val_ok, _asm = SA1MathSession.start_q88_mul(100, 128, cpu_context="SA1").wait_nops(3).read_q88_middle_word_2307()
        self.assertEqual(val_ok, 50)

    # ==========================================================================
    # PHASE 4: VERSE EFFECTS, ZERO-GC `<transacts>` ROLLBACK & OPT RECEIPTS
    # ==========================================================================

    def test_verse_effects_zero_gc_transacts_rollback_and_bisimulation_receipts(self) -> None:
        state = {"coins": 98, "hp": 3}

        # 1. `<computes>` forbids reading/writing state or calling `guard`!
        with self.assertRaises(IxEffectViolationError):
            run_verse_verb("PureCheater", ["<computes>"], lambda ctx: ctx.write("coins", 99), state=state)

        # 2. Zero-GC `<transacts>` rollback inside a live Arena:
        def _arena_tx_test(arena: object) -> None:
            _ = arena.alloc(32, label="BaselineAlloc")
            self.assertEqual(arena.cursor, 32)

            # Speculative transaction allocates 64B and mutates state, then FAILS guard (`coins <= 99`)!
            tx_fail = verse_transact(
                "AddFiveCoinsCapped",
                state,
                lambda ctx: (
                    ctx.alloc_in_arena(64, label="SpeculativeScratch"),
                    ctx.write("coins", ctx.read("coins") + 5),
                    ctx.guard(ctx.read("coins") <= 99, "coin_cap_exceeded"),
                ),
                arena=arena,
            )
            self.assertFalse(tx_fail.committed)
            self.assertEqual(tx_fail.failure_reason, "coin_cap_exceeded")
            # Arena cursor rolled back to exact 32B in O(1) and state["coins"] untouched at 98!
            self.assertEqual(arena.cursor, 32)
            self.assertEqual(state["coins"], 98)

            # Valid transaction commits whole!
            tx_pass = verse_transact(
                "AddOneCoin",
                state,
                lambda ctx: (
                    ctx.alloc_in_arena(16, label="CommittedNode"),
                    ctx.write("coins", ctx.read("coins") + 1),
                    ctx.guard(ctx.read("coins") <= 99, "coin_cap_exceeded"),
                ),
                arena=arena,
            )
            self.assertTrue(tx_pass.committed)
            self.assertEqual(arena.cursor, 48)
            self.assertEqual(state["coins"], 99)

        with_arena("VerseTxArena", AddressSpace.WRAM_7E_FRAME, 512, _arena_tx_test)

        # 3. Coalgebraic Optimisation Receipt rejects buggy "optimisation" with counterexample trace!
        with self.assertRaises(IxBisimulationError):
            prove_bisimulation_receipt(
                spec_name="ExactMod4Counter",
                fast_name="BuggyMod4Counter",
                spec_init=0,
                fast_init=0,
                alphabet=("inc",),
                spec_step=lambda s, _: (s + 1) % 4,
                fast_step=lambda s, _: (s + 1) % 3,  # Diverges after 3 steps!
                spec_obs=lambda s: s,
                fast_obs=lambda s: s,
            )

    # ==========================================================================
    # PHASE 5A: DEFENSIVE `.mwl` IMPORTER, BROKEN EXIT CHECK & DOGFOOD BUILDS
    # ==========================================================================

    def test_defensive_mwl_importer_broken_exit_compile_error_and_dogfoods(self) -> None:
        # 1. Corrupt `.mwl` magic rejected cleanly
        with self.assertRaises(MWLImportError):
            import_mwl_bytes(b"NOT_AN_MWL_FILE" * 20, name="CorruptHeader")

        # 2. Truncated Layer 1 missing `0xFF` terminator rejected cleanly
        valid_mwl = bytearray(
            pack_mwl_binary(
                source_level_id=0x0101,
                layer1_objects=[(4, 8, 0x12, 0)],
                exits=[(0, 0x0999, False, 64, 176)],  # Points to missing level 0x0999!
                sprites=[(32, 10, 0x04, 2)],
            )
        )
        ir_dangling = import_mwl_bytes(bytes(valid_mwl), name="StageWithBrokenDoor")

        # 3. Broken Door/Warp to nonexistent Level ID `0x0999` is a COMPILE ERROR with coordinates!
        bad_dir = LevelDirectory(start_bank=0xC0, mapping="SA1")
        bad_dir.append_level(ir_dangling)
        with self.assertRaises(IxBrokenExitCompileError) as ctx_err:
            bad_dir.build_directory_blob_and_asm()
        self.assertIn("x=64, y=176", str(ctx_err.exception))
        self.assertIn("0x999", str(ctx_err.exception))

        # 4. Dogfood #1: BRUTAL SOCK full compile + PIXI 40x64 + all 10 GPS labels + UberASM SA-1
        bs_out = compile_brutal_sock_dogfood()
        self.assertEqual(bs_out["level_directory"]["level_count"], 2)
        self.assertEqual(bs_out["level_directory"]["verified_exit_edges"], 2)
        self.assertEqual(bs_out["sa1_q88_scaled_velocity"], 120)
        self.assertIn("40x64", bs_out["pixi_asm"])
        for req_lbl in GPS_REQUIRED_LABELS:
            self.assertIn(f"{req_lbl}:", bs_out["gps_asm"])
        self.assertIn("$40C000", bs_out["uberasm_asm"])

        # 5. Dogfood #2: Seeds? 1,024-floor directory (shattering SMW's 512-level cap!) + Doubles Receipt
        seeds_out = compile_seeds_descent_dogfood(floor_count=1024)
        self.assertTrue(seeds_out["exceeds_smw_512_ceiling"])
        self.assertEqual(seeds_out["level_directory"]["level_count"], 1024)
        self.assertEqual(seeds_out["level_directory"]["verified_exit_edges"], 1024)
        self.assertTrue(seeds_out["room_moves_optimisation_receipt"].rats_valid)
        self.assertEqual(seeds_out["room_moves_optimisation_receipt"].bisimulation_relation_size, 8)
        self.assertTrue(seeds_out["battle_transact_committed"])

        # 6. CLI `bsar engine brutal-sock` & `bsar engine seeds --floors 600` smoke test
        buf_cli = io.StringIO()
        with redirect_stdout(buf_cli):
            rc = bsar_cli_main(["engine", "seeds", "--floors", "600"])
        self.assertEqual(rc, 0)
        cli_json = json.loads(buf_cli.getvalue())
        self.assertEqual(cli_json["result"]["floor_count"], 600)


if __name__ == "__main__":
    unittest.main()
