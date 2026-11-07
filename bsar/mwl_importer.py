#!/usr/bin/env python3
"""
DEFENSIVE LUNAR MAGIC `.mwl` BINARY IMPORTER -> `TypedLevelIR` (`bsar.mwl_importer`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Dependencies: 0 (Python >= 3.10 Standard Library Only)

Implements the MWL pipeline of `engine-vision.md` + "Just One Language" (`build-sheet.md` #7):
  `MWL file (untrusted) ──► Defensive Importer ──► TypedLevelIR (checked) ──► Bsar Engine Data`

Binary Format Handled (Lunar Magic v3.xx `.mwl` specification):
  - `0x00..0x3F` (64B Header):
      * `0x00..0x01`: ASCII `"LM"` magic
      * `0x02..0x03`: `uint16_le` version (e.g. `0x0363` for v3.63)
      * `0x04..0x07`: `uint32_le` offset to Data Pointer List (`>= 0x40`)
      * `0x08..0x0B`: `uint32_le` byte size of Data Pointer List (`>= 64`, 8 pointers * 8B)
      * `0x0C..0x0F`: `uint32_le` export flags
      * `0x10..0x3F`: 48B ASCII signature/comment block
  - `0x40..0x7F` (8 x 8-byte `(offset_u32_le, length_u32_le)` Data Pointer List):
      `[0]` Level Info, `[1]` Layer 1 Objects & Exits (`0xFF`-terminated), `[2]` Layer 2,
      `[3]` Sprites (`0xFF`-terminated 3-byte records), `[4]` Palette (BGR555),
      `[5]` Secondary Entrances, `[6]` ExAnimation, `[7]` ExGFX & Bypass.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import struct
import zlib
from typing import Any, Dict, List, Optional, Sequence, Tuple

from .refinements import IxRefinementError, RefinedInt, check_snes_hardware_budgets

MWL_MAGIC = b"LM"
MWL_HEADER_SIZE = 0x40
MWL_POINTER_COUNT = 8
MWL_POINTER_TABLE_BYTES = MWL_POINTER_COUNT * 8

SECTION_NAMES: Tuple[str, ...] = (
    "LevelInfo",
    "Layer1",
    "Layer2",
    "Sprites",
    "Palette",
    "SecondaryEntrances",
    "ExAnimation",
    "ExGFX",
)


class MWLImportError(ValueError):
    """
    Plain-English compile/import-time diagnostic carrying level ID, section name,
    and `(x, y)` coordinates so malformed `.mwl` data is NEVER discovered at runtime!
    """


@dataclass(frozen=True)
class TileObjectIR:
    layer: int
    x: int
    y: int
    object_id: int
    settings_byte: int


@dataclass(frozen=True)
class SpritePlacementIR:
    index: int
    x: int
    y: int
    sprite_id: int
    extra_bits: int


@dataclass(frozen=True)
class ScreenExitIR:
    """
    Typed Door / Pipe / Warp Exit Reference:
    Checked at compile time against the whole-project `LevelDirectory` so broken exits
    are unshippable compile errors!
    """

    screen_number: int
    dest_level_id: int
    is_secondary: bool
    source_x: int
    source_y: int


@dataclass(frozen=True)
class TypedLevelIR:
    """
    Checked, immutable Intermediate Representation produced from an `.mwl` import
    or constructed directly in Bsar ("Just One Language").
    """

    level_id: int
    name: str
    lm_version: int
    layer1_objects: Tuple[TileObjectIR, ...]
    layer2_objects: Tuple[TileObjectIR, ...]
    sprites: Tuple[SpritePlacementIR, ...]
    exits: Tuple[ScreenExitIR, ...]
    palette_bgr555: bytes
    exgfx_slots: Tuple[int, ...] = (0x0080, 0x0081, 0x0082, 0x0083)
    sa1_mode: bool = True

    def serialize_engine_blob(self) -> bytes:
        """
        Pack `TypedLevelIR` into a clean, runtime-ready binary engine record
        (arena-friendly, 2-byte aligned, zero runtime `.mwl` parsing!).
        """
        parts: List[bytes] = [
            b"BSLV",
            struct.pack(
                "<IHHHH",
                self.level_id,
                len(self.layer1_objects),
                len(self.sprites),
                len(self.exits),
                len(self.palette_bgr555),
            ),
        ]
        for obj in self.layer1_objects:
            parts.append(
                struct.pack("<BBHB", obj.x & 0xFF, obj.y & 0xFF, obj.object_id & 0xFFFF, obj.settings_byte & 0xFF)
            )
        for sp in self.sprites:
            parts.append(
                struct.pack("<HHBB", sp.x & 0xFFFF, sp.y & 0xFFFF, sp.sprite_id & 0xFF, sp.extra_bits & 0xFF)
            )
        for ex in self.exits:
            parts.append(
                struct.pack(
                    "<BIHH",
                    (ex.screen_number & 0x7F) | (0x80 if ex.is_secondary else 0x00),
                    ex.dest_level_id & 0xFFFFFFFF,
                    ex.source_x & 0xFFFF,
                    ex.source_y & 0xFFFF,
                )
            )
        parts.append(self.palette_bgr555)
        raw = b"".join(parts)
        if len(raw) % 2 == 1:
            raw += b"\x00"  # Guarantee 2-byte DMA word alignment!
        return raw

    @property
    def crc16(self) -> int:
        return zlib.crc32(self.serialize_engine_blob()) & 0xFFFF


def pack_mwl_binary(
    *,
    source_level_id: int = 0x0105,
    layer1_objects: Sequence[Tuple[int, int, int, int]] = (),
    exits: Sequence[Tuple[int, int, bool, int, int]] = (),
    sprites: Sequence[Tuple[int, int, int, int]] = (),
    palette_bgr555: bytes = b"\x00\x00" * 256,
    exgfx_files: Sequence[int] = (0x0080, 0x0081, 0x0082, 0x0083),
    lm_version: int = 0x0363,
) -> bytes:
    """
    Construct a spec-compliant Lunar Magic `.mwl` binary buffer for round-trip
    import testing and headless level generation:
      - `layer1_objects`: `(x, y, obj_id, settings)`
      - `exits`: `(screen_num, dest_level_id, is_secondary, src_x, src_y)`
      - `sprites`: `(x, y, sprite_id, extra_bits)`
    """
    # Section 0: LevelInfo (8 bytes: uint32 source_level_id + reserved)
    sec_info = struct.pack("<II", source_level_id, 0)

    # Section 1: Layer 1 (5-byte header + 4-byte object records + `0xFE` exit tag records + `0xFF` end)
    l1_buf = bytearray(b"\x00\x00\x00\x00\x00")
    for x, y, oid, settings in layer1_objects:
        # Tag 0x01 = standard object record: [0x01, x, y, oid, settings]
        l1_buf.extend(bytes([0x01, x & 0xFF, y & 0xFF, oid & 0xFF, settings & 0xFF]))
    for scr, dest_id, is_sec, sx, sy in exits:
        # Tag 0xFE = extended exit descriptor: [0xFE, scr | (0x80 if sec), dest_u32_le, sx_u16_le, sy_u16_le]
        flag_scr = (scr & 0x1F) | (0x80 if is_sec else 0x00)
        l1_buf.extend(struct.pack("<BBIHH", 0xFE, flag_scr, dest_id, sx, sy))
    l1_buf.append(0xFF)

    # Section 2: Layer 2 (minimal valid `0xFF`-terminated stream)
    sec_l2 = b"\x00\x00\x00\x00\x00\xff"

    # Section 3: Sprites (1-byte sprite header + 3-byte SMW sprite records + `0xFF` end)
    sp_buf = bytearray(b"\x00")
    for x, y, sp_id, extra in sprites:
        # Encode authentic SMW 3-byte sprite format:
        # Byte 0: YYYYEEsy  (Y bits 0..3 in upper nibble, extra bits 2..3 in bits 2..3, screen_y bit4 in bit 0)
        # Byte 1: XXXXSSSS  (X bits 0..3 in upper nibble, screen number X>>4 in lower nibble)
        # Byte 2: NNNNNNNN  (8-bit sprite number)
        if not (0 <= x <= 511 and 0 <= y <= 31):
            raise ValueError(f"SMW sprite coordinates out of 3-byte range: x={x}, y={y}")
        b0 = ((y & 0x0F) << 4) | ((extra & 0x03) << 2) | ((y >> 4) & 0x01)
        b1 = ((x & 0x0F) << 4) | ((x >> 4) & 0x0F)
        b2 = sp_id & 0xFF
        sp_buf.extend(bytes([b0, b1, b2]))
    sp_buf.append(0xFF)

    # Section 4: Palette (512B BGR555)
    sec_pal = bytes(palette_bgr555)

    # Sections 5, 6, 7: SecondaryEntrances, ExAnimation, ExGFX
    sec_ent = b""
    sec_exanim = b""
    sec_exgfx = struct.pack(f"<{len(exgfx_files)}H", *exgfx_files)

    sections = [sec_info, bytes(l1_buf), sec_l2, bytes(sp_buf), sec_pal, sec_ent, sec_exanim, sec_exgfx]

    ptr_table = bytearray()
    cur_offset = MWL_HEADER_SIZE + MWL_POINTER_TABLE_BYTES
    for sec in sections:
        ptr_table.extend(struct.pack("<II", cur_offset, len(sec)))
        cur_offset += len(sec)

    comment = b"|Lunar Magic 3.63| |Bsar Defensive MWL Fixture|".ljust(48, b" ")[:48]
    header = (
        MWL_MAGIC
        + struct.pack("<HIII", lm_version, MWL_HEADER_SIZE, MWL_POINTER_TABLE_BYTES, 0)
        + comment
    )
    assert len(header) == MWL_HEADER_SIZE
    assert len(ptr_table) == MWL_POINTER_TABLE_BYTES
    return header + bytes(ptr_table) + b"".join(sections)


def import_mwl_bytes(
    raw: bytes,
    *,
    override_level_id: Optional[int] = None,
    name: str = "ImportedMWLLevel",
    sa1_mode: bool = True,
) -> TypedLevelIR:
    """
    Defensively parse an untrusted Lunar Magic `.mwl` byte buffer into `TypedLevelIR`.
    Reports any header corruption, out-of-bounds pointer, missing `0xFF` terminator,
    palette odd-byte corruption, or sprite/OAM budget overflow with exact provenance!
    """
    if len(raw) < MWL_HEADER_SIZE + MWL_POINTER_TABLE_BYTES:
        raise MWLImportError(
            f"MWL Import Failed (`{name}`): File is only {len(raw)} bytes "
            f"(minimum valid `.mwl` header + pointer table is {MWL_HEADER_SIZE + MWL_POINTER_TABLE_BYTES} bytes)!"
        )
    if raw[:2] != MWL_MAGIC:
        raise MWLImportError(
            f"MWL Import Failed (`{name}`): Missing `'LM'` magic header at offset 0x00 (got {raw[:4]!r})!"
        )

    lm_ver, ptr_offset, ptr_bytes, _flags = struct.unpack("<HIII", raw[2:16])
    if ptr_bytes < MWL_POINTER_TABLE_BYTES or ptr_offset + ptr_bytes > len(raw):
        raise MWLImportError(
            f"MWL Import Failed (`{name}`): Corrupted Data Pointer List bounds "
            f"(offset=0x{ptr_offset:X}, size={ptr_bytes}B, file_size={len(raw)}B)!"
        )

    slices: Dict[str, bytes] = {}
    for idx, sec_name in enumerate(SECTION_NAMES):
        entry_off = ptr_offset + idx * 8
        sec_off, sec_len = struct.unpack("<II", raw[entry_off : entry_off + 8])
        if sec_off + sec_len > len(raw):
            raise MWLImportError(
                f"MWL Import Failed (`{name}`, section `{sec_name}`): Pointer slice "
                f"[0x{sec_off:X}..0x{sec_off + sec_len:X}] overruns file end ({len(raw)}B)!"
            )
        slices[sec_name] = raw[sec_off : sec_off + sec_len]

    # 0. Level Info
    info_b = slices["LevelInfo"]
    if len(info_b) >= 4:
        parsed_lvl_id = struct.unpack("<I", info_b[:4])[0]
    else:
        parsed_lvl_id = 0
    level_id = override_level_id if override_level_id is not None else parsed_lvl_id

    # 1. Layer 1 stream (requires 5B header + 0xFF terminator)
    l1_b = slices["Layer1"]
    if len(l1_b) < 6 or l1_b[-1] != 0xFF:
        raise MWLImportError(
            f"MWL Import Failed (Level 0x{level_id:X} `{name}`, section `Layer1`): "
            f"Layer 1 data stream is missing its `0xFF` end-of-level terminator (or < 6 bytes)!"
        )

    l1_objs: List[TileObjectIR] = []
    exits: List[ScreenExitIR] = []
    pos = 5
    end_pos = len(l1_b) - 1
    while pos < end_pos:
        tag = l1_b[pos]
        if tag == 0xFF:
            break
        if tag == 0x01:
            if pos + 5 > end_pos:
                raise MWLImportError(
                    f"MWL Import Failed (Level 0x{level_id:X} `{name}`, `Layer1` offset 0x{pos:X}): "
                    f"Truncated 5-byte tile object record!"
                )
            _, ox, oy, oid, oset = l1_b[pos : pos + 5]
            l1_objs.append(TileObjectIR(layer=1, x=ox, y=oy, object_id=oid, settings_byte=oset))
            pos += 5
        elif tag == 0xFE:
            if pos + 10 > end_pos:
                raise MWLImportError(
                    f"MWL Import Failed (Level 0x{level_id:X} `{name}`, `Layer1` offset 0x{pos:X}): "
                    f"Truncated 10-byte screen exit record!"
                )
            _, flag_scr, dest_id, sx, sy = struct.unpack("<BBIHH", l1_b[pos : pos + 10])
            exits.append(
                ScreenExitIR(
                    screen_number=flag_scr & 0x1F,
                    dest_level_id=dest_id,
                    is_secondary=bool(flag_scr & 0x80),
                    source_x=sx,
                    source_y=sy,
                )
            )
            pos += 10
        else:
            # Standard 3-byte SMW Layer 1 object fallback `[b0, b1, b2]`
            if pos + 3 > end_pos:
                raise MWLImportError(
                    f"MWL Import Failed (Level 0x{level_id:X} `{name}`, `Layer1` offset 0x{pos:X}): "
                    f"Truncated 3-byte SMW Layer 1 object!"
                )
            b0, b1, b2 = l1_b[pos : pos + 3]
            oy = b0 & 0x1F
            ox = b1 & 0x1F
            l1_objs.append(TileObjectIR(layer=1, x=ox, y=oy, object_id=b2, settings_byte=(b0 >> 5)))
            pos += 3

    # 3. Sprite stream (1-byte header + N * 3-byte sprites + 0xFF terminator)
    sp_b = slices["Sprites"]
    if len(sp_b) < 2 or sp_b[-1] != 0xFF:
        raise MWLImportError(
            f"MWL Import Failed (Level 0x{level_id:X} `{name}`, section `Sprites`): "
            f"Sprite stream is missing its `0xFF` terminator!"
        )
    sp_payload = sp_b[1:-1]
    if len(sp_payload) % 3 != 0:
        raise MWLImportError(
            f"MWL Import Failed (Level 0x{level_id:X} `{name}`, section `Sprites`): "
            f"Sprite payload byte length ({len(sp_payload)}B) is not a multiple of 3 bytes!"
        )
    sprites: List[SpritePlacementIR] = []
    for s_idx in range(0, len(sp_payload), 3):
        b0, b1, b2 = sp_payload[s_idx : s_idx + 3]
        sy = ((b0 >> 4) & 0x0F) | ((b0 & 0x01) << 4)
        sx = ((b1 >> 4) & 0x0F) | ((b1 & 0x0F) << 4)
        extra = (b0 >> 2) & 0x03
        sprites.append(
            SpritePlacementIR(
                index=s_idx // 3,
                x=sx,
                y=sy,
                sprite_id=b2,
                extra_bits=extra,
            )
        )

    # 4. Palette validation (BGR555 2-byte color words, max 256 colors = 512B)
    pal_b = slices["Palette"]
    if len(pal_b) % 2 != 0:
        raise MWLImportError(
            f"MWL Import Failed (Level 0x{level_id:X} `{name}`, section `Palette`): "
            f"Palette byte length ({len(pal_b)}B) is odd (BGR555 colors require 2 bytes per color)!"
        )

    try:
        check_snes_hardware_budgets(
            oam_tiles=min(128, len(sprites) * 4),
            active_sprites=len(sprites),
            cgram_colors=len(pal_b) // 2,
            sa1_mode=sa1_mode,
            provenance=f"Level 0x{level_id:X} (`{name}`)",
        )
    except IxRefinementError as ref_err:
        raise MWLImportError(str(ref_err)) from ref_err

    # 7. ExGFX slots
    ex_b = slices["ExGFX"]
    exgfx: Tuple[int, ...] = (0x0080, 0x0081, 0x0082, 0x0083)
    if len(ex_b) >= 8 and len(ex_b) % 2 == 0:
        exgfx = struct.unpack(f"<{len(ex_b) // 2}H", ex_b)

    return TypedLevelIR(
        level_id=RefinedInt(level_id, 0, 0xFFFFFFFF, "level_id").value,
        name=name,
        lm_version=lm_ver,
        layer1_objects=tuple(l1_objs),
        layer2_objects=(),
        sprites=tuple(sprites),
        exits=tuple(exits),
        palette_bgr555=pal_b,
        exgfx_slots=exgfx,
        sa1_mode=sa1_mode,
    )


def import_mwl_file(
    path: str | Path,
    *,
    override_level_id: Optional[int] = None,
    sa1_mode: bool = True,
) -> TypedLevelIR:
    p = Path(path)
    return import_mwl_bytes(
        p.read_bytes(),
        override_level_id=override_level_id,
        name=p.stem,
        sa1_mode=sa1_mode,
    )
