# `bsar` Algebraic, Group-Ring & Coalgebraic Research Workbench (`v0.4.0`)

`BSA-R` (`bsar`) is a **zero-dependency** (`Python >= 3.10` standard library + Base `R >= 4.1.0`, plus zero-Mathlib constructive `Lean 4.35.0` and optional `pip install bsar[verify]` `Z3`/`SymPy` provers) toolkit uniting:
1. **Fast `64-byte` L1-Cache-Line `Q8.8` Cayley–Dickson Hardware Sieving** (`bsar.cd_q88`, `13.98 µs` per 32D product on commodity CPUs),
2. **Exact Arbitrary-Precision `ℤ / ℚ / 𝔽ₚ` Algebraic Verification & `OutwardInterval` Enclosures** (`bsar.math_algebras`, `bsar.group_rings`, & `bsar.round4_bridge`, eliminating fixed-point underflow and IEEE-754 rounding false positives),
3. **Navier–Stokes Round-4 Shell Dispersion (`Θ`) & `𝕋³` Bloch–Floquet Group-Ring Certifiers** (`bsar.round4_bridge` + `lean/CayleyDicksonBimodalRound4.lean`), and
4. **Haskell-Inspired Applicative `MooreFold` Stream Fusion & Coalgebraic Implicit State-Machine Discovery (`S / ~`)** (`bsar.fp_coalgebra` + `r/cayley_dickson_math.R`) alongside **3-Pass Hilbert Sparse Hypercubes** (`bsar.hypercube`).

> **Design Philosophy:** Known results from the literature (Moreno, de Marrais, Wilmot, Reggiani, Koebisu, Guterman & Zhilina, Promislow, Gardam, Ivanov) are included strictly as **regression calibration checks** (`python -m bsar math calibrate`) so collaborators can trust the exact arithmetic before probing **open questions** (higher $64\text{D}/128\text{D}$ zero-divisor strata, mixed split signatures, relation-graph invariants, loop identities, and `char 0` vs `char p` group-ring obstructions).

---

## 1. Zero-Install Quick Start (CLI & R)

```bash
# Run the full exact calibration suite (Python >= 3.10, zero pip dependencies)
python -m bsar math calibrate

# Compute exact rational/integer right-annihilator basis ker(L_x) in 32D Pathions or 64D Chingons
python -m bsar math annihilator --level 5 --coords "1:1,18:1"
python -m bsar math annihilator --level 6 --coords "1:1,34:1"

# Compile 3-pass Hilbert sparse relation-graph hypercubes (standard vs. split signatures)
python -m bsar math relations --level 4 --gamma "-1,-1,-1,-1"
python -m bsar math relations --level 4 --gamma "-1,-1,-1,1"

# Probe nonassociative identities across R, C, H, O, S_16, P_32 (or modulo p)
python -m bsar math identities --max-level 5
python -m bsar math identities --identity left_moufang --level 4 --mod 5

# Audit support-product multiplicities (Unique Product / parity fibers) in torsion-free P
python -m bsar math groupring --words "a,abb,aB,Ba,ABB,BA,AB,BB,bb,A,bAb,bab,ab,bA"

# Run Round-4 bimodal dispersion Theta, OutwardInterval Stiefel V_2(R^7), T^3 Bloch-Floquet & Z3/SymPy proofs
python -m bsar math round4 --angle 0.73

# Extract implicit minimal deterministic state machines via coalgebraic bisimulation (with Mermaid export)
python -m bsar math fsm --mermaid

# Verify constructive Lean 4.35.0 proofs (Zero Classical.choice, Zero Mathlib)
lean lean/CayleyDicksonBimodalRound4.lean
```

---

## 2. Programmable Python API for Custom Conjectures

### A. Arbitrary $2^n$-ions & Split Signatures $\gamma \in \{-1, +1\}^n$
Construct any Cayley–Dickson algebra $\mathbb{A}_n(\gamma)$ up to $256\text{D}$ ($n = 8$) over exact $\mathbb{Z}$, $\mathbb{Q}$ (`fractions.Fraction`), or $\mathbb{F}_p$ (`modulus=p`):

```python
from bsar import CayleyDicksonAlgebra, exact_annihilator_profile, bareiss_det_int

# 64D Chingons (level=6) or split 32D Pathions with custom doubling signature
alg32_split = CayleyDicksonAlgebra(level=5, gamma=(-1, -1, -1, +1, -1))
x = alg32_split.elem({1: 1, 10: -2, 18: 1, 27: 2})

# Exact integer left-multiplication matrix L_x, Bareiss determinant, & rational ker(L_x) basis
Lx = alg32_split.left_mult_matrix(x)
det_val = bareiss_det_int(Lx)
ker = exact_annihilator_profile(x, side="right")
print("det(L_x) =", det_val, "| dim ker(L_x) =", ker["nullity"])
```

### B. Zero-Divisor Manifolds ($V_2(\mathbb{R}^7)$, $G_2$ Pairs, & Higher $2^n$ Strata)
Generate dense, zero-error rational points on the normalized sedenion zero-divisor Stiefel manifold $V_2(\mathbb{Q}^7) \subset V_2(\mathbb{R}^7) \cong G_2 / SU(3)$ via exact rational Householder reflections, or audit quartic left-multiplication determinant factorizations:

```python
from bsar import (
    CayleyDicksonAlgebra,
    koebisu_sedenion_det_factorization,
    moreno_pathion_kernel_spectrum_probe,
    sample_reggiani_stiefel_v2_q7,
)

# Dense 7-lane rational orthonormal frames lifted to primitive integer zero divisors
frames = sample_reggiani_stiefel_v2_q7()

# Inspect the 4 non-negative Stiefel sum-of-squares obstructions on any sedenion in Z^16
s16 = CayleyDicksonAlgebra(level=4)
audit = koebisu_sedenion_det_factorization(s16.elem([1, 2, -1, 0, 1, 0, -2, 1, -1, 1, 0, 2, -1, 1, 0, -1]))

# Full {0, 4, 8, 12} annihilator spectrum in 32D Pathions
spectrum = moreno_pathion_kernel_spectrum_probe()
```

### C. Sparse Relation-Graph Hypercubes (`|>`)
Compile multi-relation graphs (`zero_divisor`, `commutativity`, `mutual_alternativity`, plus doubly-alternative vertex tags) into a 3-pass `BsaRHypercubeCompiler` slab for $O(1)$ indexed slicing:

```python
from bsar import BsaRHypercubeCompiler, compile_guterman_zhilina_relation_hypercube

rep = compile_guterman_zhilina_relation_hypercube(level=4, gamma=(-1, -1, -1, +1))
pipe = BsaRHypercubeCompiler.pipe(rep["slab"])

# O(1) CSR/CSC slice on a specific relation & connected component
zd_c01 = pipe.filter_eq(relation="zero_divisor", component="C01").rows
```

### D. Custom Nonassociative Polynomial ASTs & Catalan Bracketings
Screen custom nonassociative identities using the two-stage `64B Q8.8` L1 sieve $\to$ Exact $\mathbb{Z}/\mathbb{F}_p$ counterexample certifier (so fixed-point underflow can never fake an identity):

```python
from bsar import catalan_bracketings, probe_nonassociative_identity

# Probe a custom AST: e.g. Mal'cev / Jordan / Bol-type expression
# Operators: "+", "-", "*", "conj", "comm", "assoc"
custom_ast = ("-", ("*", "x", ("*", "y", ("*", "x", "z"))), ("*", ("*", "x", ("*", "y", "x")), "z"))
res = probe_nonassociative_identity(custom_ast, variables=("x", "y", "z"), level=4)

# Generate all C_4 = 14 parenthesizations of 5 variables
trees_5 = catalan_bracketings(("x1", "x2", "x3", "x4", "x5"))
```

### E. Torsion-Free Group Rings (`char 0` vs `char p`) & Twisted Group Algebras
Plug in any finitely generated group multiplication/normal-form function (or use the built-in exact Bieberbach screw-motion normal form for the Hantzsche–Wendt / Promislow group $P$, or the Albuquerque–Majid twisted group-ring presentation $R^\sigma[(\mathbb{Z}_2)^n] \cong \mathbb{A}_n(\gamma)$):

```python
from bsar import (
    GroupRingSpec,
    compile_support_product_hypercube,
    construct_gardam_f2_unit_and_char0_lift,
    make_promislow_group_ring,
    promislow_word_ball,
    solve_support_zero_divisor_kernel,
)

# 1. Inspect F_2[P] unit cancellation vs exact Z[P] (char 0) even-parity residual
unit_xray = construct_gardam_f2_unit_and_char0_lift()

# 2. Test candidate zero-divisor annihilators across Q[G] (char 0) vs F_p[G] (char p)
spec = make_promislow_group_ring()
ball = list(promislow_word_ball(radius=2).keys())
alpha = spec.elem({ball[0]: 1, ball[1]: -1, ball[2]: 1, ball[3]: -1})
kernel_cmp = solve_support_zero_divisor_kernel(alpha, candidate_right_support=ball, primes=(2, 3, 5, 7))

# 3. Plug in ANY custom torsion-free group (e.g. discrete Heisenberg group H_3(Z))
heisenberg = GroupRingSpec(
    name="Z[Heisenberg_H3]",
    identity=(0, 0, 0),
    mul_fn=lambda u, v: (u[0] + v[0], u[1] + v[1], u[2] + v[2] + u[0] * v[1]),
)
```

### F. Round-4 Shell Dispersion (`Θ`), `OutwardInterval` Stiefel Frames, & `𝕋³` Bloch–Floquet Certifiers
Bridge Round 4's Shifted-Laplacian Spectral-Variance Depletion (`M_0 P - D^2 = e_1 e_2(m_2 - m_1)^2`) directly into zero-divisor geometry and unbounded-support `char 0` group-ring certification:

```python
from bsar import (
    CayleyDicksonAlgebra,
    PROMISLOW_14_NON_UP_WORDS,
    cayley_dickson_shell_dispersion,
    certify_continuous_stiefel_rotation_interval,
    make_promislow_group_ring,
    parse_promislow_word,
    promislow_bloch_floquet_t3_audit,
)

# 1. Single-pass MooreFold shell dispersion: zero divisors force maximal bimodal dispersion Theta == 1
s16 = CayleyDicksonAlgebra(level=4)
disp = cayley_dickson_shell_dispersion(s16.elem({1: 1, 10: 1})).extract()

# 2. Rigorous IEEE-754 outward-rounded interval enclosure on continuous Stiefel V_2(R^7) rotations
iv_cert = certify_continuous_stiefel_rotation_interval(angle_rad=0.73)

# 3. Faithful 4x4 Laurent matrix symbol M_alpha(X,Y,Z) on T^3: nonzero Bareiss det at (2,3,5) certifies
#    alpha * beta != 0 across ALL nonzero beta in C[P] of arbitrary UNBOUNDED finite support!
spec = make_promislow_group_ring()
alpha_14 = spec.elem({parse_promislow_word(w): 1 for w in PROMISLOW_14_NON_UP_WORDS})
bf_cert = promislow_bloch_floquet_t3_audit(alpha_14).extract()
```

### G. Haskell-Inspired Functional Primitives & Coalgebraic Implicit State-Machine Discovery (`S / ~`)
Compose verified computations via `ModalBox` (`Functor`, `Applicative` Axiom K `<*>`, `Comonad`), single-pass `MooreFold` stream fusion, deforested `hylo` (`cata . ana`) recursion schemes, static `AlgebraicPipeline` rewrites, and automatic coalgebraic bisimulation (`discover_minimal_fsm`):

```python
from bsar import (
    AlgebraicPipeline,
    FilterStage,
    MutateStage,
    NonlinearShellFluxStage,
    discover_minimal_fsm,
    extract_promislow_v4_orientation_fsm,
    extract_sedenion_boxkite_mode_fsm,
)

# 1. Extract implicit minimal quotient state machines S / ~ from any transition coalgebra!
#    Round 0 sees 3 trace values {-2, 0, +2}, and Round 2 automatically splits `a` vs `b` into 4 V_4 states:
fsm_v4 = extract_promislow_v4_orientation_fsm()
print(fsm_v4.to_mermaid())

fsm_7modes = extract_sedenion_boxkite_mode_fsm()  # 42 assessors -> 7 Wilmot Box-Kite modes

# 2. Static AlgebraicPipeline equational fusion + Round-4 Theorem J1 Theta==0 short-circuiting
pipe = (
    AlgebraicPipeline()
    .then(FilterStage("pos", lambda r: r["x"] > 0))
    .then(FilterStage("even", lambda r: r["x"] % 2 == 0))
    .then(MutateStage("sq", {"x2": lambda r: r["x"] ** 2}))
    .then(NonlinearShellFluxStage("flux", known_dispersion_theta=0.0))
    .optimize()
)
```

---

## 3. Native Base `R` Companion (`r/cayley_dickson_math.R`)

```r
source("r/cayley_dickson_math.R")

# Arbitrary split/standard sign matrix, L_x nullity, & relation-graph data.frame for |>
S16_split <- cd_sign_matrix_gamma(4L, c(-1L, -1L, -1L, 1L))
edges_df  <- cd_relation_edges_df(4L, c(-1L, -1L, -1L, 1L))
subset(edges_df, relation == "zero_divisor") |> head(10)

# Single-pass functional Reduce Moore fold for Round-4 shell dispersion Theta & coalgebraic FSMs
zd <- numeric(16); zd[2] <- 1; zd[11] <- 1
cd_shell_dispersion(zd)$z2_bimodal$theta_dispersion  # == 1
```
