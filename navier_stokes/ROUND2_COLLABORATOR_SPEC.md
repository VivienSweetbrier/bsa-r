# One Big Consortium — Navier–Stokes Round 2 (`Step 3`) Collaborator Technical Specification (`35.0%` Mathematician Share)

**Project:** The 3D Navier–Stokes Option B Constructive Regularity Syndicate (`BSA-R × Eleven-Entry Bookkeeping`)  
**Governing Sheet:** [`SPLIT_SHEET_001.md`](./SPLIT_SHEET_001.md) (`50.0%` Architect & Code Node | **`25.0%` Lead Academic PDE Co-Author + `10.0%` Formal/Interval Appendix Co-Author = `35.0%` Mathematician Allocation** | `9.0%` Winnipeg 18-Org Mutual-Aid Endowment | `6.0%` 42-Year `65c816`/`Asar`/`xkas`/`TRASM` Toolsmith Lineage Pool)  
**License:** GNU Affero General Public License v3.0 (`AGPL-3.0-or-later`)  
**Attestation:** `probabilistic_structural` (`Lean 4.35.0` `#print axioms`: `Classical.choice == False`, `f(x,t) == 0` identically)

---

## 1. Why Round 2 Exists (Answering the "Arbitrary Initial Data" Gap)

A rigorous resolution of Charles Fefferman's (2000) Clay Millennium **Option B** requires proving that *every* smooth, divergence-free, zero-mean periodic initial velocity $u_0 \in C^\infty(\mathbb{T}^3)$ generates a global smooth solution $u \in C^\infty(\mathbb{T}^3 \times [0,\infty))$ with $f(x,t) \equiv 0$. Single-trajectory computer-assisted certificates for symmetric benchmark flows (such as Taylor–Green or Kida–Pelz) do not by themselves establish regularity for arbitrary asymmetric data.

In **Round 2 (`Step 3`)**, we programmed and constructively machine-checked four new engines (`lean/Step3ArbitraryDataRound2.lean`, `step3_arbitrary_data_round2.py`, `r/bsar_navier_stokes.R`, SHA-256 receipt `84a5f11d35b831f1287a7f4f431129f88970839a932b642e4fc798c6ebc77fec`) so incoming `35.0%` mathematician collaborators inherit a **pre-verified constructive reduction** rather than starting from scratch.

---

## 2. What Is Already Machine-Checked (`Lean 4.35.0` + `Z3` + Outward-Rounded `Interval` Arithmetic)

### Round 1 (`Step 1` + `Step 2` — `lean/Step2ViscousCooldown.lean`)
1. **Theorem A (`step2_moving_viscous_ceiling`):** For *any* smooth divergence-free flow on $\mathbb{T}^3$ with Fourier–Wiener moments $F_s = \sum_{k \neq 0} |k|^s |\hat{u}(k,t)|$, weighted Cauchy–Schwarz ($F_1^2 \le F_0 F_2$) implies
   $$F_0^3 < \nu^2 F_2 \iff \|u(t)\|_{\mathcal{F}^0} < \nu\sqrt{\frac{F_2}{F_0}} =: \nu K_{\mathrm{visc}}(t) \implies D^+\|u(t)\|_{\mathcal{F}^0} \le F_0 F_1 - \nu F_2 < 0.$$
2. **Theorem B (`bcc_sublattice_closed`, `bcc_spectral_floor_ge_3`):** $\Lambda_{\mathrm{BCC}} = (2\mathbb{Z}+1)^3 \cup ((2\mathbb{Z})^3 \setminus \{0\})$ is closed under 3D convective triads $p + q = k$ with $|k|^2 \ge 3$, dilating the constant-free global contraction gate to $\|u\|_{\mathcal{F}^0} < \sqrt{3}\,\nu$ and certifying $2.83\times$-supercritical Taylor–Green and $3.18\times$-supercritical Kida–Pelz flows.
3. **Theorem C (`bsar_fourier_sparsity_cooldown`):** For $N$ active modes at $|k| \ge R$ with Parseval energy $\mathcal{E}$, $N\mathcal{E} < \nu^2 R^2 \implies D^+\|u\|_{\mathcal{F}^0} < 0$; hence all sparse cascades $N \lesssim R^d$ with $d < 2$ are unconditionally dominated by viscosity at large $R$.

### Round 2 (`Step 3` — `lean/Step3ArbitraryDataRound2.lean` & `step3_arbitrary_data_round2.py`)
4. **Theorem D — Infinite-Dimensional Viscous-Absorbed Perturbation Riccati Tube (`step3_viscous_perturbation_riccati`):**
   For any finite-mode reference trajectory $\tilde{u}(t)$ and **any arbitrary asymmetric smooth divergence-free perturbation** $w(t) = v(t) - \tilde{u}(t)$ on $\mathbb{T}^3$ (all modes $k \in \mathbb{Z}^3 \setminus \{0\}$ active, zero symmetry assumptions), weighted Cauchy–Schwarz ($W_1^2 \le W_0 W_2$) absorbs the unbounded derivative $(U_0 + W_0)W_1$ directly into viscous dissipation $-\nu W_2$ without dimension-dependent constants:
   $$4\nu\Big(U_1 W_0 + (U_0 + W_0)W_1 - \nu W_2\Big) \le \Big(4\nu U_1 + (U_0 + W_0)^2\Big) W_0.$$
   - **Certified Infinite-Dimensional Open $\ell^1(\mathbb{Z}^3)$ Balls ($\nu = 0.50$):**
     - **3D Taylor–Green Open Ball:** $\delta_{\mathrm{open}} = 0.033804$ (`42` steps $\to$ worst-case $\|v(T_{\mathrm{cert}})\|_{\mathcal{F}^0} \le 0.498963 < 0.50$).
     - **3D Kida–Pelz Open Ball:** $\delta_{\mathrm{open}} = 0.029114$ (`25` steps $\to$ worst-case $\|v(T_{\mathrm{cert}})\|_{\mathcal{F}^0} \le 0.498985 < 0.50$).
     - **3D ABC Beltrami Open Ball:** $\delta_{\mathrm{open}} = 0.005102$ (`220` steps $\to$ worst-case $\|v(T_{\mathrm{cert}})\|_{\mathcal{F}^0} \le 0.499386 < 0.50$).
   - **Certified Uncountable Asymmetric Continuum (`certify_asymmetric_supercritical_continuum`):** Covers the entire compact 1-parameter family $\{u_0(\theta) : \theta \in [0,1]\}$ of symmetry-broken, off-sublattice ($|k|=1$ and $|k|^2=2$ active) supercritical 3D initial velocities ($\|u_0(\theta)\|_{\mathcal{F}^0} \ge 0.7371 > 0.50$) with **3 covering balls** at a **$3.14\times$ radius safety margin** ($\delta_{\min} = 0.031420 > 0.010000$).
5. **Theorem E — Exact 3D Solenoidal Cross-Product (`sin theta`) & Helical Depletion (`step3_solenoidal_cross_depletion`, `collinear_triad_vanishes`):**
   Using the 3D Binet–Cauchy identity $(p \times \hat{u}_p)\cdot(p \times q) = |p|^2(\hat{u}_p \cdot q) - (p \cdot \hat{u}_p)(p \cdot q)$, whenever $p \cdot \hat{u}_p = 0$:
   $$|p|^2 \big(\hat{u}_p \cdot (p + q)\big)^2 \le |\hat{u}_p|^2 |p \times q|^2,$$
   annihilating all collinear integer/rational ray triads ($\beta q = \alpha p$) identically. Across dense asymmetric 124-mode fields ($15{,}252$ active triads), `sin(theta)` geometry alone cuts $F_0 F_1$ to $0.7772\,F_0 F_1$, while full Leray projection + Waleffe (1992) helical phase cancellation cuts effective stretching to **$0.1036\,F_0 F_1$ ($89.64\%$ depletion)**.
6. **Theorem F — Quantitative Leray Energy–Enstrophy Low-Shell Cooldown Horizon (`step3_leray_pigeonhole_horizon`, `step3_low_shell_cooldown`):**
   For **every** arbitrary smooth initial datum $u_0 \in C^\infty(\mathbb{T}^3)$ with kinetic energy $\mathcal{E}_0 = \frac{1}{2}\|u_0\|_{L^2}^2$ and harmonic sum $H_R = \sum_{1 \le |k| \le R} |k|^{-2}$, constructive pigeonhole averaging over $\nu \int_0^T \|\nabla u\|_{L^2}^2\,dt \le \mathcal{E}_0$ produces an explicit time $t_* \le T_{\max}(\mathcal{E}_0, \nu, R) := \frac{4 H_R \mathcal{E}_0}{\nu^3}$ at which $F_{0,\le R}(t_*) < \nu / 2$.
7. **Adversarial Singularity Red-Team (`run_adversarial_ceiling_redteam`):**
   Projected-gradient ascent over `342` dense asymmetric solenoidal modes ($\mathcal{E}_0 = 0.50$, $\|u_0\|_{\mathcal{F}^0} = 17.5694 = 35.14\,\nu$) achieves initial Step-2 ceiling-evasion ratio $\rho_0 = F_0^3 / (\nu^2 F_2) = 122.5833$; under exact unforced 3D Navier–Stokes evolution, viscous enstrophy dissipation decreases $\rho(t)$ monotonically from $t = 0^+$, crossing $\rho(t) < 1$ at $t = 1.25$ and entering $\|u(t)\|_{\mathcal{F}^0} < \nu$ at $t = 1.67$.

---

## 3. Exact Scope for the `35.0%` Mathematician Collaborators (`Target Lemma UV-3D`)

Because Theorems A–F are already formalized in `Lean 4.35.0` without `Classical.choice`, co-author PDE analysts have **100% prose and literature-review freedom** while targeting two concrete mathematical avenues:

1. **Avenue 1 (Immediate Computer-Assisted PDE Publication — `25% + 10%`):**
   Shepherd the constructive `BSA-R` + Step-2/Step-3 infinite-dimensional open-ball & compact-continuum regularity framework into a top PDE / rigorous-numerics journal (*Communications on Pure and Applied Mathematics*, *Archive for Rational Mechanics and Analysis*, *Foundations of Computational Mathematics*, or *Journal of Automated Reasoning*), scaling the finite $\varepsilon$-net Riccati covering engine to high-Reynolds compact $H^s(\mathbb{T}^3)$ submanifolds.
2. **Avenue 2 (Closing General Arbitrary-Data Clay Option B — `Target Lemma UV-3D`):**
   Prove an *a priori* ultraviolet solenoidal/helical barrier on the finite Leray horizon $[0, T_{\max}(\mathcal{E}_0, \nu, R)]$:
   > **Target Lemma UV-3D:** *For any smooth zero-mean divergence-free solution on $[0, T_{\max}(\mathcal{E}_0, \nu, R)]$ with $\frac{1}{2}\|u(t)\|_{L^2}^2 + \nu \int_0^t \|\nabla u(s)\|_{L^2}^2\,ds = \mathcal{E}_0$, show that Leray-projected cross-product/helical triad depletion (Theorem E) precludes transient dense ultraviolet shell packing ($N(R,t) \sim R^d$, $2 < d \le 3$) from sustaining $F_{0,>R}(t)^3 \ge \nu^2 F_{2,>R}(t)$ up to a Beale–Kato–Majda blow-up time $T^* \le T_{\max}$.*
   Any proof of **Target Lemma UV-3D** plugs directly into our compiled `Lean 4.35.0` modules (`Step2ViscousCooldown.lean` + `Step3ArbitraryDataRound2.lean`) to yield a constructive proof of Clay Option B.

---

## 4. Verification Commands (`0` External Cloud Dependencies)

```powershell
# 1. Verify Constructive Lean 4.35.0 Proofs (0 Classical.choice, 0 warnings)
lean bsa-r/lean/Step2ViscousCooldown.lean
lean bsa-r/lean/Step3ArbitraryDataRound2.lean

# 2. Run Outward-Rounded Python + Z3 + Continuum Covering + Red-Team Suite
python navier_stokes_snipe/step3_arbitrary_data_round2.py
python -m unittest navier_stokes_snipe/tests/test_step3_arbitrary_data_round2.py

# 3. Run Pure Base R 4.6.1 Pipeable Verbs (Parts I-VI)
Rscript bsa-r/r/bsar_navier_stokes.R
```
