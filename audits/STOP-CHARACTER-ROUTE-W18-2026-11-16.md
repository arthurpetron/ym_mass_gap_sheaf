# STOP REPORT: character-route milestone (sharpen SCGuards to w = 1/8), 2026-11-16 (base fe78bb43)

**Outcome: stopped before writing Lean. Both stop conditions of the brief apply.**
(a) Removing the 16ⁿ loss needs the strong-coupling cluster chain re-proved for an abstract remainder cap. That is a re-proof far past the
~900-line budget, not a local lemma.
(b) Even with *ideal* constants, **w = 1/8 is structurally unreachable** by this sup-norm Interval architecture. Reaching it needs a new mathematical input:
an expansion that uses Haar orthogonality rather than sup-norm caps.
No new Lean files were written. Box MemAvailable was 17.5–18.0 % of 16002 MB the whole time, below the 25 % floor, so no Lean run was possible anyway.
Not chart closure. No numerics are used as proof.

## 1. How the guards enter the existing chain (read from source)
- `SCGuards w` (`RG/StrongCouplingNomeThreshold.lean:53`) is `heatRatio w ≤ 1/2 ∧ ∃ hd : heatRemainderBound w < 1, entropyRate 625 (adjustedCoreRate w hd) < 1`.
  It is consumed by `uniformRate_of_guards` (:68) via `allNome_strongCoupling_vacuumSq_all_widths`
  (`Continuum/BF4WilsonAllNomeStrongCouplingUniformRate.lean`, threaded through `originalWindowScalar_connected_sc_bound` :228 … `sc_oneStep_norm_gap`).
- **The δ = 128w³ cap.** `heatTermBound w n = coeffW w n · 2·16ⁿ` and `heatRemainderBound = heatTermBound w 1 · 2 = 128w³`
  (`Continuum/QuaternionHaarCharacterInterval.lean:78–88`). The 16ⁿ comes from `characterBound` (`QuaternionHaarPolynomialSquareBound.lean:196`),
  the recurrence b(n+2) = 8b(n+1)+2b(n) on SOS square caps. b(1) = 4 is already sharp for χ₁ = 2a (|χ₁| ≤ 2), but `Interval.ofSquare` turns a square cap c into an interval cap c+1 (`QuaternionHaarPolynomialInterval.lean`, `ofSquare`).
  - This δ is **hard-wired by definition** into the whole chain:
    - `faceRemainderInterval … (heatRemainderBound w)` (`BF4ExactSlabSmallNomeHaarComparison.lean:52`);
    - `inverseFaceFloor w hd = (1−heatRemainderBound w)⁻¹`, `probePrefactor = inverseFaceFloor^(12·links)`, `adjustedCoreRate = pairedHeatRate w · inverseFaceFloor⁴⁸` (`BF4ExactSlabCollarAdjustedRate.lean:41–48`);
    - the heterogeneous comparison / resummation / distance-decay files.
  - 305 files (58,254 lines) mention `heatRemainderBound`. The chain-critical subset alone is several thousand lines.
  - A sharper cap therefore cannot be "plugged in". It needs a parallel copy of the chain generalised to an abstract cap δ with an `Interval` certificate. **Over budget → stop (a).**
  - Hiding it as a hypothesis ("the chain holds with δ′") would be exactly the disguised assumption the brief forbids.
- **The 625 factor is not a real entropy.** `oldGuard_coreRate_le` (`BF4ExactSlabDescentDistanceDecay.lean:77`) uses it only to derive `adjustedCoreRate ≤ 1/384`
  (`comparisonCoreRate` :70). The actual count is the descent-coded **96** (`connecting_weight_tail` :49), and `timeRate = 1/4 = 96·(1/384)` (`comparison_entropy` :72).
  - So the 625 guard can honestly be weakened to `384·adjustedCoreRate ≤ 1` without new math. Replacing 96 itself would need new lattice-animal combinatorics.
  - Wiring the weakened guard needs: a new oldGuard-style theorem (via the public `connectedNumerator_distance_bound` :145 plus a rate-monotonicity lemma for `tailBudget`, because `connected_of_weight_bound` :110 is private);
    a copy of `finite_covariance_distance_bound` (`BF4ExactSlabDescentSelectedCovariance.lean:65`); and copies of `BF4WilsonAllNomeStrongCouplingUniformRate.lean:204–444`
    with the new hypothesis. Estimate ≈ 350–400 lines. **Not built** (see §3).

## 2. Reach of each sharpening (box python; bisection on the exact guard; δ = K·w³, A(δ) = (2δ+δ²)(1−δ)^(−48))

| guard on A(δ) | max δ | w at K = 128 (current cap) | w at K = 4 (ideal: sup of f_w−1 is ≈ Σ(n+1)²w^{n(n+2)} ≈ 4w³) |
|---|---|---|---|
| 625·A < 1 (current) | 7.71e-4 | **0.01819 = 1/55.0** (matches `inv55` :141) | 0.0578 = 1/17.3 |
| 384·A ≤ 1 (honest weakening, §1) | 1.23e-3 | **0.02124 ≈ 1/47.1** (1/48 passes: 384·A = 0.940; 1/47 fails: 1.005) | 0.0674 = 1/14.8 |
| 96·A < 1 (bare count; needs a w-dependent time rate) | 4.24e-3 | 0.0321 = 1/31.1 | 0.1020 = 1/9.8 |

- **At w = 1/8 with the ideal cap δ = 4w³ = 0.0078: 96·A = 2.19 > 1.** Under any Interval (sup-norm) cap, δ ≥ sup|f_w − 1| ≥ 4w³ (attained at U = 1).
  So even perfect Haar constants together with the bare 96 count miss w = 1/8 by about 2.2×. This is stop (b).
  Reaching 1/8 needs either a sharper animal count (≲ 44) *together with* removing the (1−δ)^(−48) collar loss, or an expansion whose activity is the Haar-integrated character u = w³ times dimension factors.
  The latter is the actual SU(2) strong-coupling expansion, using orthogonality ∫χ_n = 0, not the sup-norm |χ_n| ≤ n+1. **Both are new mathematical inputs, not proof repair.**
- **Largest w actually reached by new constants: none built.** The proven reach is unchanged at w ≤ 1/55 (`scGuards_of_le_inv55` :156).
  The cheapest honest increment (§1, 384 guard, no new math) would reach w = 1/48, which is about 15 % higher in w.

## 3. Why the 1/48 increment was not built this round
- It is about 350–400 lines of mostly duplicated chain for a 1/55 → 1/48 gain. It does not touch the 16ⁿ loss and cannot approach 1/8.
- The RAM floor blocked all Lean runs throughout (17.5 %, 18.0 % at checks; Numerics' own queues are paused for the same reason).
- Writing it unchecked was judged lower value than reporting the structural stop. It is available on request as a separate, clearly scoped build.

## 4. U(1) check (required)
- **What is SU(2)-specific:** only the Casimir-3 exponent at equal nome. `coeffW w n = (n+1)w^{n(n+2)}`, so the first excited term is 2w³ (u = w³, c(½) = 3).
  The U(1) Villain/HK analogue has first term ∝ w¹ (u = w). Everything else (Interval caps, the 96 count, the collar exponent 48) is group-agnostic.
- **The same constants applied to U(1) at w = 0.56:** δ_U(1) = K·w = 128·0.56 ≈ 72 (or ≈ 2.2 even at the ideal K = 4). Both are > 1, so `heatRemainderBound < 1` already fails.
  More generally the guards confine the method to u ≲ 1e-5 (u = (1/47)³), i.e. w_U(1) ≲ 1e-5, which is far below the U(1) transition w_c ≈ 0.463 (task2o, numerical).
  U(1) at w = 0.56 sits past that transition (Coulomb phase; task2o measured photon collapse, `results/task2o_partial.md` table A).
- **Consequence:** in its proven regime the method is abelian-valid (as the existing docstrings at `StrongCouplingNomeThreshold.lean:4–8` already say), so it is not non-abelian evidence.
  It would become SU(2)-discriminating only if it reached u = w³ ≳ (0.463)³ ≈ 0.1. That needs the orthogonality-based expansion of §2.

## 5. Recommendation
1. Do not pursue constant-sharpening inside the current architecture for step 2: its ceiling (ideal constants) is w ≈ 0.10.
2. If wanted: the 384-guard increment to w = 1/48 (≈ 400 lines, needs RAM ≥ 25 %).
3. The real milestone is a new, Haar-orthogonality-based polymer bound for SU(2) in u = w³. That is new mathematics; scope it separately before any Lean.

Caveats: the line and file counts are rg/wc measurements; the chain-subset size is an estimate. The reach table is from exact guard formulas evaluated in floating point, not Lean.
Not chart closure. No push.
