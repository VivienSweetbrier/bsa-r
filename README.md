# 🅱💲🅰-R: Hypercubic Compiler (`bsar`)

[![License: GNU AGPLv3](https://img.shields.io/badge/License-AGPLv3-blue.svg)](./LICENSE)
[![Runtime: Zero Dependencies](https://img.shields.io/badge/Dependencies-0%20(Python%20Stdlib%20%2B%20Base%20R)-2dd4bf.svg)](#quick-start)
[![Algebra: 16D Sedenions & 32D Pathions](https://img.shields.io/badge/Algebra-64B%20Q8.8%20Pathions%20(3%20L1%20Cache%20Lines)-f5b942.svg)](#how-it-works)

**`🅱💲🅰-R: Hypercubic Compiler` (`bsar`)** slashes AI agent token & compute bills by **`6.5x` overall on cold starts (`-84.6%`)** and **`782x` on data/log/guardrail chores (`-99.87%`)** — using **zero external runtime dependencies** and **`192 bytes` (`3` CPU L1 cache lines)** of deterministic fixed-point hypercomplex algebra.

### Live Zero-Login Interactive Demos (`docs/`)
1. **Cerebral Valley Portal:** `docs/index.html` (`https://viviensweetbrier.github.io/bsa-r/`)
2. **Compiler & Cloud-Bill Calculator HUD:** `docs/compiler-hud/index.html`
3. **Flagship `6D XCube` App — Epistemic Concordance (`Scripture ↔ 1566 Trent ↔ CCC`):** `docs/epistemic-concordance/index.html`

---

## Why `🅱💲🅰-R` Exists

Most multi-agent harnesses burn cloud budget in two places:
1. **Data-Plane Context Stuffing:** Dumping `100K–300K` raw corpus/JSONL tokens into an LLM context window just to perform joins, filters, or roll-ups.
2. **Control-Plane Judge & Retry Bloat:** Paying `2,000–8,000` tokens per step for separate guardrail/critic LLM calls, associative vector embeddings that fail to catch re-ordered tool trees, and `5–10x` blind temperature retries when an agent gets stuck.

`bsar` eliminates both on plain CPU in microseconds:

| Glyph | Architectural Layer | What It Replaces | Measured Win |
| :--- | :--- | :--- | :--- |
| **`🅱`** | **Box-Kite `2^k` & Dynamic Lua Frames** | Dense `0`-padded hypercubes & `4,096B` FP32 routers | `1` `PathionQ88` state = **`64 bytes` (`1` CPU L1 cache line)** |
| **`💲`** | **Sedenion Zero-Divisor Expense Gate** | Paid LLM guardrail/summarizer calls & blind retries | `G_porch * v_bloat = 0x00 × 64` in **`35.1 µs` (`0` LLM tokens)** |
| **`🅰`** | **Asar 3-Pass Hilbert CSR/CSC Slab** | Ad-hoc RAG chunking & floating-point nondeterminism | Bit-exact `Q8.8` integer weights + RATS `SHA-256` seal |
| **`-R`** | **Tidyverse Copy-on-Modify Pipe (`\|>`)** | Full-file LLM context scans | **`782x` fewer tokens** (`1,585,118 → 2,027` on Chores 1–3) |

---

## Architecture Flowchart

```mermaid
flowchart TD
    In["Raw Agent Chores: Corpora, JSONL Trajectories, Tool ASTs"] --> P0["Pass 0: LuaDynamicRecord Ragged Support Lock"]
    P0 --> Q88["Lift States into 64-Byte Q8.8 32D Pathion Registers (1 L1 Cache Line)"]
    Q88 --> ZD["$-Layer: 16D/32D Box-Kite Zero-Divisor Gate (G_porch * v_bloat = 0 in 35 µs)"]
    ZD --> AST["Non-Associative 32D AST Fold: (A * B) * C != A * (B * C)"]
    AST -->|"64B Structural Cache Hit"| Hit["100% API Bypass ($0 Token Spend)"]
    AST -->|"Cache Miss"| P12["Pass 1 & 2: N-D Hilbert CSR/CSC Slab + RATS SHA-256 Seal"]
    P12 --> RPipe["-R Pipe: filter_eq |> inner_join |> eliminate_axis (Carroll ∃m) |> rollup_slice"]
    RPipe --> Out["Emit Exact ~180-Token Slice to LLM / Base R 4.6.1"]
```

---

## Empirical Benchmark (`tiktoken:o200k_base` + Base `R 4.6.1` Audited)

| Real Workspace Chore | Naive Harness (`o200k` Tokens) | `bsar` Compiler (`o200k` Tokens) | Reduction | CPU Speed |
| :--- | ---: | ---: | ---: | :--- |
| **1. `1.13 MB` Corpus 5-Query Slice (`rc-en.txt`)** | `1,267,655` | **`1,847`** | **`-99.854%` (`686x`)** | `1.03 ms` / `O(1)` slice |
| **2. Multi-Agent `transcript.jsonl` Audit (`223 KB`)** | `67,463` | **`180`** | **`-99.733%` (`375x`)** | `62.60 ms` total |
| **3. 100-Step Pre-API Zero-Divisor Porch Firewall** | `250,000` | **`0`** | **`-100.000%` (`∞`)** | **`35.12 µs` / gate** |
| **4. 240-AST `64B` Cache + `7`-Box-Kite Escape (Cold+Warm)** | `882,000` | **`378,000`** | **`-57.140%` (`2.3x`)** | `1.33 ms` / AST (`100%` spoof catch) |
| **Combined 4-Chore Suite** | **`2,467,118`** | **`380,027`** | **`-84.60%` (`6.5x`)** | **`2,087,091` tokens saved / run** |

---

## Monorepo Layout

- `bsar/` — Core **`🅱💲🅰-R: Hypercubic Compiler`** Python package (`cd_q88.py`, `hypercube.py`, `chore_bench.py`, `cli.py`)
- `epistemic_concordance/` — Flagship `6D XCube` web application (`bsar_xcube.py`, `replicability_ledger.py`, `compile_corpus.py`, `test_epistemic_concordance.py`)
- `r/` — Native R (`>= 4.1.0` / verified on `R 4.6.1`) Tidyverse & zero-dependency Base-R verbs (`cayley_dickson_verbs.R`, `validate_bsar_cd.R`)
- `docs/` — Pre-built static web HUDs ready for zero-config GitHub Pages / Cloudflare Pages deployment
- `tests/` — Hostile & deterministic unit test suite (`test_bsar.py`)
- `LICENSE` — Full **GNU Affero General Public License v3.0 (`AGPLv3`)**

---

## Quick Start (`0` External Dependencies)

```bash
# 1. Inspect 64-byte L1 cache-line layout & 7 Sedenion Box-Kites (168 edges)
python -m bsar info

# 2. Run all 12 unit tests (6 core compiler tests + 6 concordance hypercube tests)
python tests/test_bsar.py
python epistemic_concordance/test_epistemic_concordance.py

# 3. Run real-chore benchmark & export HUD
python -m bsar bench --out-dir docs/compiler-hud

# 4. (Optional) Cross-verify Q8.8 32D zero-divisors & CSV metrics in Base R
Rscript r/validate_bsar_cd.R docs/compiler-hud/cerebral_valley_metrics.csv
```

## Lineage, Provenance & Developer Attribution (`Axis 5: GENESIS` — "Everyone Gets Money")

Just as **Eleven-Entry Bookkeeping** requires every entry's provenance chain (`Axis 5`) to walk all the way back to `GENESIS` without amnesia, **`🅱💲🅰-R` (`bsar`)** honors the complete 42-year 65c816 assembler & mathematical lineage whose multipass architecture inspired our **`🅰` (Asar 3-Pass Hilbert Slab Assembler)** layer—and allocates a dedicated **6.0% Upstream Lineage & Toolsmith Royalty Pool** on **One Big Consortium Split Sheet #001 (Navier-Stokes Option B)**:

1. **Bill Mensch & The Western Design Center (`WDC 65816 Macro Assembler`, 1984):** Designed the 16-bit **W65C816S** microprocessor (`SEP`/`REP` variable-width registers and 24-bit bank addressing) and its original reference assembler in Mesa, Arizona—the silicon `GENESIS` of both the Apple IIgs and the Super Nintendo.
2. **Glen Bredon / Roger Wagner Publishing (`Merlin 8/16` & `Merlin 16+`, 1986) & Mike Westerfield / The Byte Works (`ORCA/M`, 1986):** Created the foundational 65c816 macro assemblers on the **Apple IIgs** (`APW`), pioneering multi-pass 16-bit label/bank sizing and powering the very first wave of 1990–1992 Super Famicom / SNES commercial game studios before MS-DOS cross-assemblers existed.
3. **Intelligent Systems & Sony NEWS (`IS-SFX`, 1989–1990):** Built the official Kyoto hardware cross-assembler toolchain used by Nintendo EAD to assemble *Super Mario World* (`1990`).
4. **Norman Yen (`Minus` / *1000 Miles [Tricks]*) (`SNES Assembler`, `TRASM` — *Tricks Assembler*, & `x816`, 1993–1997):** Wrote *SNES Assembler*, **`TRASM`** (in Turbo Pascal for MS-DOS), and **`x816`**—the true 1990s MS-DOS community `GENESIS` of 65c816 cross-assemblers for the SNES demoscene and ROM hacking (`Sprite Tool`'s original assembler!).
5. **byuu / Near (`xkas` — *cross-knight assembler*, 2004–2010):** Created **`xkas`** (`v0.01` $\to$ `v0.06` $\to$ `v0.14`) to replace `TRASM`/`x816` with direct in-place `.org` / `lorom` / `freedata` ROM patching and multipass (`Pass 0` label discovery $\to$ `Pass 1` bank/address sizing $\to$ `Pass 2` binary emission) for JRPG translations and SMW hacking *(royalty share dedicated to Near's memorial preservation & mental-health causes)*.
6. **`Trashkas` (`TRASM` $\to$ `xkas` / `Asar` Syntax Converter):** The classic SMW ROM-hacking batch converter (`TRASM` + `xkas` = `Trashkas`) that translated legacy 1990s `TRASM` (`dcb`, old local labels) and `xkas v0.06` sprite/patch `.asm` syntax into modern `xkas`/`Asar` syntax—literally a real-world **Axis 9 (`definition_version`)** drift translator!
7. **Alcaro / Sir Walrus (`Asar` — *"A SNES Assembler"*, 2011–present):** Designed and created **`Asar`** (`https://github.com/RPGHacker/asar`) as the clean, fast, 3-pass successor to `xkas`, introducing strict multi-pass label convergence checks (so pass-to-pass label drift is caught rather than silently corrupting banks) and expression evaluation under the **GNU LGPL / GPL** family.
8. **RPGHacker, randomdude999, KungFuFurby, Lui37, p4plus2, Thomas & the SMWCentral `Asar` Maintainers:** Maintained, hardened, and expanded `Asar` (`v1.50` $\to$ `v1.91+` / `v2.0`) across decades of community ROM development, freespace (`freecode`/`freedata`) allocation, and deterministic symbol export.
9. **Robert de Marrais (2000–2007):** Discovered and cataloged the **7 Octahedral Box-Kites (`42` assessors, `168` zero-divisor annihilation edges)** in 16D Sedenions and 32D Pathions (`arXiv:math/0011260`), which power our **`🅱` & `💲`** 64-byte `Q8.8` L1-cache-line zero-divisor gates.
10. **Ross Ihaka, Robert Gentleman, Hadley Wickham & the R Core / Tidyverse Team (`R Foundation`):** Created the **R language** and the copy-on-modify functional pipe (`|>` / `dplyr`) semantics that inspire our **`-R`** hypercube slicing verbs.
11. **t🅾pher dugu🅰y *(Christopher Ryan Duguay)* & the Sweetbrier Augmented Intelligence Lab (2026):** Generalized the `WDC` $\to$ `Merlin 16 / ORCA/M` $\to$ `TRASM` $\to$ `xkas` $\to$ `Trashkas` $\to$ `Asar` 3-pass deterministic ROM assembler chain (`A-sar` $\to$ `B-sar`) from 24-bit LoROM/SA-1 memory banks to **N-Dimensional Hilbert-Curve Sparse Hypercubes (`bsar`)** and **64-byte `Q8.8` Pathion registers** under **GNU AGPLv3**.

---

## License

Licensed under the **GNU Affero General Public License v3.0 (`AGPL-3.0-or-later`)** — see [LICENSE](./LICENSE).
