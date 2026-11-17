# SCOPE: an orthogonality-based SU(2) strong-coupling expansion in u = w³ (2026-11-16, base a301993d)

**Label: scope only. No Lean. Not chart closure.** The reach numbers are arithmetic on stated activity/entropy assumptions, not theorems.

## 0. Why (from the STOP note a301993d)
- The existing seed chain bounds each face's excited part f_w − 1 by a sup-norm `Interval` cap δ = `heatRemainderBound` = 128w³
  (`Continuum/QuaternionHaarCharacterInterval.lean:78–88`), and sums over all face subsets.
- Even with ideal sup-norm caps (δ = 4w³) that architecture tops out at w ≈ 0.10.
- An orthogonality expansion uses the fact that the Haar integral of a product of characters vanishes unless every link is "paired".
  Then only face sets whose every link is covered at least twice (closed surfaces) survive, and each surviving face costs its character
  coefficient rather than a sup-norm cap.

## 1. The expansion
- Per face p (repo normalisation): f_w(U_p) = Σ_{n≥0} coeffW w n · χ_n(U_p), with coeffW w n = (n+1)·w^{n(n+2)} (`BondMovingStep.lean:259`).
  So f_w = 1 + Σ_{n≥1} d_n u_n χ_n, with d_n = n+1 and u_n = w^{n(n+2)}; u_1 = w³ (Casimir c(½) = 3). The repo identity is `faceHeat_eq_one_add`
  (used at `BF4ExactSlabSmallNomeHaarComparison.lean:65`).
- Expand ∏_p f_w(U_p) = Σ over labelled face sets (S, n: S → ℕ≥1) of ∏_{p∈S} d_{n_p} u_{n_p} χ_{n_p}(U_p). Integrate the links with Haar measure.
  - **Orthogonality:** if some link ℓ lies in exactly one face of S (and in no probe), then ∫ dU_ℓ χ_n(U_ℓ A) = 0 for n ≥ 1, so the term vanishes.
  - Surviving S are therefore "closed" relative to the probes: every link of S is shared by ≥ 2 faces of S ∪ probes.
  - Consequences: |S| ≥ 6 for a vacuum polymer (elementary cube), and a set connecting two probes at time separation t has size ≳ t, with the tube bound ≳ 4t still to be proved.
- **Activity.** A surviving term is bounded by ∏_{p∈S} d_{n_p} u_{n_p} times |∫ ∏χ|. The integral is a product of SU(2) recoupling factors, each ≤ 1.
  I take the conservative per-face activity z(w) = Σ_{n≥1} coeffW w n · c_n, where c_n ≥ |χ_n| contributions after integration.
  The safe bound with c_n = 1 per paired link gives z ≈ 2w³ (the repo's exact cube value below is consistent with that).
  Using sharper d^{χ(S)} gains, as in literature strong-coupling series, is *not assumed*.
- **Polymer gas plus KP.** Polymers are connected closed labelled face sets. Z/Z₀ = Σ over compatible families, and the KP criterion controls log Z and truncated correlations.

## 2. Repo pieces it would reuse (file:line)
- Character data and Haar facts:
  - `characterPolynomial` (`BF4GeometricSpinNetworkMehler.lean:409`);
  - `coeffW` (`BondMovingStep.lean:259`);
  - bare Haar centring of the fundamental face `plaquette_mean_zero` (`BF4ExactSlabFixedSpatialPlaquetteHaar.lean:54`), the n = 1 orthogonality instance;
  - the exact closed-surface rung `cubeBoxHaarCharacterSector_exact` (`Z4UnitCubeHaarSectorBridge.lean:348`): cube-sector Haar weight = (coeffW coupling 2)⁶ at every box size.
    Its docstring says this works because "a link meets either zero or exactly two cube faces … character orthogonality evaluates both to one". This is the template for O1/O2 below.
  - `vacuumBoxHaarCharacterSector_eq_one` (:400).
- Character caps:
  - `character_squareBound` (`QuaternionHaarPolynomialSquareBound.lean:201`);
  - the sharp SOS square bound `character_square_haar_le` (`SU2CharacterHaarBound.lean:221`), giving H(χ_s²) ≤ (s+1)² for a single link. Its docstring marks the plaquette case **OPEN** (radius multiplicativity).
- Haar functional and certificates: `quaternionHaar`, `Certificate`, `Interval` (`QuaternionHaarPolynomialInterval.lean:30`), plus the face-product certificates (`BF4ExactSlabSmallNomeHaarComparison.lean:52–80`).
- Entropy:
  - the descent-coded count 96 (`connecting_weight_tail`, `BF4ExactSlabDescentDistanceDecay.lean:49`; `BF4ExactSlabDescentCoreCount`) for connecting anchor sets;
  - `size_sum_bound` / `tailBudget` (`FiniteSizeGeometricSum.lean:60,113`).
  - **Caveat:** the 96 count is proved for the connecting-core family of the current chain. Whether it bounds closed labelled polymers is unchecked. That is a milestone item.
- Wiring targets: `connectedNumerator_distance_bound` (`BF4ExactSlabDescentDistanceDecay.lean:145`), `finite_covariance_distance_bound` (`BF4ExactSlabDescentSelectedCovariance.lean:65`),
  `WilsonVacuumSqContraction` (`BF4WilsonAllNomeExprMixRateContraction.lean:61`).

## 3. Predicted reach (arithmetic; assumptions explicit)
- Per-face activity: z = 2w³ (n = 1 dominates; the n ≥ 2 terms are O(w⁸)). Entropy per face κ. To keep the existing fixed time rate 1/4, require κ·z ≤ 1/4, the same convention as `comparisonCoreRate = 1/384` with κ = 96.
  - **κ = 96:** 2w³ ≤ 1/384 ⇒ w³ ≤ 1/768 ⇒ **w ≤ 0.1092 ≈ 1/9.16**. That falls short of 1/8, where κz = 96·2/512 = 0.375 > 1/4.
  - **w = 1/8 with a w-dependent rate:** κz = 0.375 < 1. KP/geometric convergence holds with per-face rate 0.375 (and KP needs some margin e^{a}). So **1/8 is predicted reachable** if the rate is allowed to be 3/8 instead of 1/4, or if κ ≤ 64 is proved for closed polymers (64·2/512 = 1/4).
  - **w = 0.35 (start of step 2):** z = 0.0858, so κz = 8.2 with κ = 96. Needs κ ≤ 2.9 for rate 1/4, or κ < 11.7 just to converge.
  - **w = 0.56:** z = 0.351, so κ < 2.85 just to converge.
  - Any plaquette-animal growth constant in d = 4 is far above 3. Heuristic: there are ≥ 20 edge-adjacent faces per face. **UNVERIFIED as a theorem; not proved here.**
- **Verdict on reach:** an orthogonality expansion plausibly reaches **w = 1/8** (u = 1/512). It **cannot reach step 2 (0.35 → 0.56)** with any lattice-animal entropy. Step 2 would need resummation or RG on top (Balaban-type), or computer-assisted finite-volume input. This matches the task2o observation that m(0.56) ≈ −4 ln u holds only *numerically* there.
- Mass gain, expected and unproved: a connecting surface between times 0 and t has area ≥ 4t (a tube) rather than ≥ t, so the decay exponent improves by about 4×.

## 4. SU(2)-specific vs U(1)-valid
- Character orthogonality, the polymer gas and KP are **group-agnostic**. The same expansion works for U(1) Villain/HK with characters e^{inθ} and activity z_U(1) = 2w (n = ±1).
- The **only** SU(2)-specific input at equal nome is the Casimir-3 exponent: z_SU(2) = 2w³ vs z_U(1) = 2w.
  - At w = 1/8: z_U(1) = 1/4, so κz = 24 ≫ 1 with κ = 96. The same constants do **not** cover U(1) at 1/8.
  - The U(1) regime for rate 1/4 is w ≤ 1/768.
- U(1) at w = 1/8 is itself confined (numerics README; numerical). So reaching 1/8 is **not non-abelian evidence**: it only says SU(2) at nome 1/8 is deep in strong coupling in its own variable u = w³.
- At w = 0.56 U(1) is past its ≈ 0.463 transition (task2o). The expansion cannot reach 0.56 for either group, consistent with the analysis above.

## 5. Literature basis
- **Kotecký–Preiss-type criterion, verified from fetched text:** D. Ueltschi, "Cluster expansions & correlation functions", arXiv:math-ph/0304003v3 (Moscow Math. J. 4 (2004) 511–522), https://arxiv.org/abs/math-ph/0304003, §2, Theorem 1 ("Cluster expansion").
  - Quote: "Assume that |1 + ζ(A, A′)| ⩽ 1 for all A, A′ ∈ A, and that there exists a nonnegative function a on A such that for all A ∈ A, ∫ d|µ|(A′) |ζ(A, A′)| e^{a(A′)} ⩽ a(A), (3) and ∫ d|µ|(A) e^{a(A)} < ∞."
    The conclusion is the absolutely convergent cluster expansion of log Z, with bound (4). The paper calls (3) an extension of "the neat Kotecký-Preiss criterion".
  - The original Kotecký–Preiss CMP 103 (1986) was **not fetched**.
- **Osterwalder–Seiler 1978**, Ann. Phys. 110, 440–471: abstract only (OpenAIRE), as quoted in PROOF-STRATEGY §1.1. Strong-coupling infinite-volume limit plus the confinement bound. Radius **UNVERIFIED**.
- **Drouffe–Zuber**, strong-coupling / mean-field review (Phys. Rep., 1983): **not fetched; UNVERIFIED**. No statements are quoted.
- **Münster** (strong-coupling expansions for vortex free energy / string tension, early 1980s): **not fetched; UNVERIFIED**.
- **Shen–Zhu–Zhu** arXiv:2204.12737 (fetched earlier, PROOF-STRATEGY §1.3): a different method (Bakry–Émery). It covers β_W < 1/12 for SU(2), i.e. w_char ≈ 0.275 on the character map. That is a comparator, not a basis.

## 6. Module plan (estimates)
| id | module (new files) | content | est. lines |
|---|---|---|---|
| O1 | `SU2LinkOrthogonalityVanishing` | **first milestone:** bare quaternion Haar of a product of face characters vanishes if some link occurs in exactly one nontrivial face (and no probe). Generalises `plaquette_mean_zero` and the cube-incidence argument | 150–250 |
| O2 | `ClosedFaceSetSupport` | surviving labelled sets are closed (link multiplicity ≥ 2); vacuum polymers have size ≥ 6; connecting sets have size ≥ time gap (then ≥ 4·gap) | 250–350 |
| O3 | `ClosedPolymerActivity` | |∫∏ coeffW χ| ≤ ∏ z on surviving sets, via existing `SquareBound`/`Interval` caps per face, used only on surviving sets | 250–400 |
| O4 | `ClosedPolymerEntropy` | count of connected closed labelled sets containing a face ≤ C·κⁿ: reuse or re-prove the descent-96 count for this family; try κ ≤ 64 | 200–400 |
| O5 | `OrthogonalityConnectedNumerator` | the connected numerator over closed polymers, parallel to `BF4ExactSlabHeterogeneousConnectedExpansion` / `…DistanceDecay` | 400–600 |
| O6 | `OrthogonalityUniformRate` | `WilsonVacuumSqContraction` at a fixed rate on all widths at w = 1/8, as a new wrapper (no edits) | 250–350 |
Total ≈ 1500–2350 lines, in several ≤ 400-line commits.
- **First Lean milestone (O1):** "if a link ℓ belongs to exactly one face of the labelled set and to no probe, the bare Haar integral of the character product is ≈ 0."
  This is purely algebraic in the quaternion Haar carrier and is the gate for everything else.
  Go/no-go for O1: whether the existing `quaternionHaar` block-factorisation lemmas used by `Z4UnitCubeHaarSectorBridge` let one integrate a single link out of a product without unfolding the whole box.

## 7. Risks
- O4 (entropy for closed polymers) may not inherit the 96 count. If κ > 128 at rate 1/4, or κ > 256 at w = 1/8 for mere convergence, then 1/8 is not reached.
- O3 depends on recoupling factors being ≤ 1 under the repo's Haar normalisation. Only the cube instance is verified (`Z4UnitCubeHaarSectorBridge.lean:348`).
- Step 2 is out of reach by this method alone (§3).
