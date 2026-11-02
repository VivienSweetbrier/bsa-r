---
title: 'BSA-R: A Deterministic Three-Pass Hilbert Sparse Hypercube Compiler and Fixed-Point Cayley-Dickson Zero-Divisor Runtime for Python and R'
tags:
  - Python
  - R
  - sparse tensors
  - Hilbert curve
  - Cayley-Dickson algebras
  - formal verification
  - reproducible research
authors:
  - name: Christopher "Topher" Duguay
    orcid: 0009-0006-8693-6839
    affiliation: 1
affiliations:
  - name: University of Manitoba, Winnipeg, MB, Canada
    index: 1
date: 2 November 2026
bibliography: paper.bib
---

## Summary

`BSA-R` (distributed as the Python package `bsar` with companion native `R` routines under the GNU Affero General Public License v3.0) is a zero-dependency sparse hypercube compiler and fixed-point hypercomplex runtime for Python (`>= 3.10`) and Base `R` (`>= 4.1.0`, verified on `R 4.6.1`) [@ihaka1996r]. The software addresses data-intensive scientific auditing, formal proof certificate generation, and large language model (LLM) context reduction by uniting three deterministic mechanisms on standard CPUs: (1) a three-pass multipass slab compiler (`BsaRHypercubeCompiler`) that maps ragged multi-axis records onto $N$-dimensional Hilbert space-filling curves [@hilbert1891curve] with compressed sparse row and column (`CSR/CSC`) inverted indices and `SHA-256` pass-convergence attestation; (2) a `64-byte` signed `Q8.8` fixed-point `16D` Sedenion and `32D` Pathion Cayley-Dickson algebraic kernel (`PathionQ88` and `cd_q88_mult`) occupying a single CPU L1 cache line alongside a `128-byte` bit-packed sign lookup table; and (3) copy-on-modify relational pipe verbs (`RPipe` and native `R` `|>` pipelines) [@wickham2019tidyverse] for bit-exact, cross-language analytical slicing.

## Statement of Need

Researchers constructing reproducible multi-axis concordances, computer-assisted mathematical proofs, and multi-agent data pipelines routinely encounter three structural bottlenecks. First, materializing dense $D$-dimensional contingency or tensor grids incurs $O(N^D)$ memory allocation even when empirical support (`nnz`) occupies an infinitesimal fraction of the ambient Cartesian space. Second, parallel and cross-language reductions in IEEE-754 floating-point arithmetic suffer from rounding non-associativity [@goldberg1991float], preventing bit-identical aggregation digests across heterogeneous hardware architectures and scripting runtimes. Third, contemporary LLM harnesses frequently serialize hundreds of thousands of raw corpus or telemetry tokens into paid API context windows merely to perform deterministic joins, roll-ups, or policy admission checks, while relying on commutative vector embeddings that cannot distinguish non-associative re-bracketings of tool execution trees.

Mature sparse linear and tensor algebra ecosystems already serve high-performance numerical simulation well. The Tensor Algebra Compiler (`TACO`) [@kjolstad2017taco] generates optimized C++ kernels for general sparse tensor contractions, while `scipy.sparse` [@virtanen2020scipy] in Python and the `Matrix` package [@bates2000matrix] in Base `R` provide battle-tested compiled routines centered primarily on two-dimensional sparse matrix factorizations and iterative solvers. However, workflows focused on auditable certificate generation, cross-runtime provenance ledgers, and lightweight pre-API agent filtering have lacked a zero-dependency standard-library engine that combines arbitrary-rank named sparse hypercubes ($O(\text{nnz})$ storage), bit-identical fixed-point roll-ups shared across Python and `R`, and algebraic zero-divisor admission gates without requiring external C, C++, or Fortran build toolchains. `BSA-R` (`bsar`) is designed specifically to fill this systems niche.

## Architecture and Key Capabilities

`BSA-R` comprises three interoperable layers implemented solely against the Python standard library (`bsar/hypercube.py`, `bsar/cd_q88.py`) and zero-dependency Base `R` (`r/cayley_dickson_verbs.R`):

1. **Three-Pass `Asar`-Inspired Hypercubic Compiler (`BsaRHypercubeCompiler`):** Adapting the multipass symbol-convergence discipline of classic 16-bit microprocessor macro assemblers from linear memory banks to sparse $N$-dimensional slabs, compilation proceeds in three deterministic passes:
   - *Pass 0 (Dynamic Support Discovery):* Ingests ragged associative frames (`LuaDynamicRecord`) with arbitrary attribute fan-out, expands optional interval assertions (`spread_interval`), constructs canonically sorted axis ordinal vocabularies in $O(\text{nnz})$ memory, and computes `64-byte` `PathionQ88` abstract syntax tree (AST) signatures over each record.
   - *Pass 1 ($N$-D Hilbert `CSR/CSC` Layout):* Folds $N$-dimensional integer coordinate tuples onto one-dimensional locality keys via pairwise Hilbert curve composition (`hilbert_nd_to_d`) [@hilbert1891curve], sorting active cells to preserve multi-axis spatial locality while building $O(1)$ per-axis inverted `CSR/CSC` index tables (`axis_index`).
   - *Pass 2 (Zero-Drift `SHA-256` Lock):* Verifies strict pass-to-pass cardinality convergence (`pass_drift == 0`), quantizes continuous weights into signed 16-bit `Q8.8` fixed-point integers (`1.0 == 256` on `[-32768, 32767]`), and seals the serialized `bsar.hypercube.v1` artifact with a canonical `SHA-256` digest (`rats_sha256`).

2. **Fixed-Point `16D` Sedenion and `32D` Pathion Runtime (`bsar.cd_q88`):** Each `PathionQ88` state packs 32 signed 16-bit `Q8.8` lanes into exactly `64 bytes` (one standard CPU L1 cache line). Basis multiplication $e_i e_j = s(i, j)\, e_{i \oplus j}$ is driven by `S32BitPackedLUT`, a `128-byte` (`1,024-bit`, two L1 cache lines) bit-packed Cayley-Dickson sign table shared conceptually with Base `R`'s `cd_sign_matrix` and `cd_q88_mult`. Sign-symmetric fixed-point shift rounding preserves exact zero (`0 == 0`) and eliminates floating-point drift across x86-64, ARM64, Python, and `R`. Because real Cayley-Dickson algebras of dimension $2^k \ge 16$ contain nontrivial zero divisors [@moreno1998], `BSA-R` constructs and verifies the complete `16D` Sedenion zero-divisor topology cataloged by de Marrais: `7` octahedral Box-Kites partitioning `42` primitive assessors and `168` directed annihilation edges (`enumerate_sedenion_box_kites` and `cd_boxkite_table`) [@demarrais2000]. Mapping rejected or policy-violating subspaces onto paired Box-Kite blades annihilates inadmissible states to exact binary zero across all `64 bytes` in microseconds without floating-point threshold tuning. Simultaneously, non-associative multiplication ($(a b) c \neq a (b c)$) allows `fold_ast_q88` to distinguish re-ordered or re-parenthesized execution trees that collide under associative or commutative hashing.

3. **Copy-on-Modify Relational Pipe Verbs (`RPipe` and Base `R`):** Compiled hypercube slabs expose immutable, Tidyverse-inspired pipe verbs [@wickham2019tidyverse] in both Python and `R 4.6.1`, including $O(1)$ indexed slice filtering (`filter_eq`), predicate filtering (`filter`), dictionary joins (`inner_join`), column derivation (`mutate`), Carrollian four-valued (`0`, `1`, `?`, `*`) existential middle-term projection (`eliminate_axis`) with full witness retention, anti-echo `Q8.8` cluster aggregation (`rollup_slice`), and compact table emission (`to_compact_prompt_table`).

## Empirical Validation and Research Applications

`BSA-R` includes an automated benchmark and verification suite (`python -m bsar bench` and `Rscript r/validate_bsar_cd.R`) alongside two domain research deployments:

- **Multi-Agent Token and Latency Reduction:** Audited with the `o200k_base` tokenizer across a four-task workload—(1) five-query cross-referencing over a `1.13 MB` historical text (`1,267,655` reduced to `1,847` tokens at `1.03 ms` per `O(1)` indexed slice), (2) multi-agent `JSONL` trajectory telemetry aggregation (`67,463` to `180` tokens), (3) a 100-step pre-API `Q8.8` Box-Kite zero-divisor admission gate (`250,000` to `0` tokens at `35.12 us` per gate within a `192-byte` combined state-and-table footprint, a `64x` parameter footprint reduction relative to a `4,096-byte` dense `FP32` `32x32` router), and (4) 240-tree non-associative AST memoization (`882,000` to `378,000` tokens with `100%` structural regrouping detection versus `0%` for commutative bag-of-vectors baselines)—`BSA-R` achieves an **`84.60%` overall token reduction** (`2,467,118` to `380,027` tokens) and a **`782x` data-plane reduction** (`1,585,118` to `2,027` tokens across Tasks 1–3), cross-checked for exact `Q8.8` zero-divisor and metric agreement in Base `R 4.6.1`.
- **Supercritical 3D Navier–Stokes Interval and `Lean 4` Verification:** In computer-assisted supercritical 3D Navier–Stokes interval auditing paired with constructive `Lean 4.35.0` formal proofs [@duguay2026zenodo; @moura2021lean4], three-pass `BSA-R` sparse hypercube compilation compresses candidate wavenumber triad interactions by **`99.99967%`**, isolating **`82` active triads out of `25,200,451` candidates** under deterministic `SHA-256` certificate locks.
- **`6D XCube` Historical-Textual Concordance:** The bundled `epistemic_concordance` module compiles byte-pinned slices of the 1566 *Roman Catechism*, public-domain biblical witnesses, conciliar citations, and modern paragraph indices into a static `6D XCube` concordance supporting reversible four-valued epistemic roll-ups in browser and command-line environments.

## Acknowledgements

The three-pass symbol-convergence architecture of `BSA-R` (`bsar`) draws direct inspiration from the 1984–2026 `W65C816S` microprocessor and multipass macro-assembler lineage: Bill Mensch and The Western Design Center (`WDC` `W65C816S`), Glen Bredon (`Merlin 16`), Mike Westerfield (`ORCA/M`), Norman Yen (`TRASM` and `x816`), Near (`xkas`), and Alcaro together with the `SMWCentral` maintainers (`Asar`). The author also gratefully acknowledges Robert de Marrais for uncovering the octahedral Box-Kite zero-divisor geometry of higher Cayley-Dickson algebras, and the R Core Team alongside the Tidyverse contributors for pioneering the functional copy-on-modify pipe semantics reflected in `BSA-R`.
