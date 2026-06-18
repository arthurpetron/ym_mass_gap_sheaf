# Scale-invariance research synthesis & plan of action (2026-06-18)

Five parallel deep-research strands tying the scale-invariance literature to actionable
Lean steps for the open continuum (`a→0`) problem and the use of fiducial constants.
The crux quantity is the physical gap `Δ = lim_{a→0} m_lat(a)/a` — an `f(x)/x` limit.

## Cross-strand consensus

1. **The interface SHAPE is already correct** (strands: regular-variation, scaling-function).
   `RegScalingLimitModulus` encodes homogeneity degree exactly 1 in the spacing
   (`physGap·a ≃ latMargin`) + finite-positive coefficient + convergence modulus.
   *Index exactly 1 ⇔ finite positive physical gap* (faster ⇒ gap→0; slower ⇒ gap→∞).
   Do NOT add a separate exponent field — degree-1 is best kept definitional.
2. **The `f(x)/x` / fold machinery already exists**: `completeLimit`,
   `isPositive_completeLimit`, `ofQ'_le_completeLimit`, `completeLimit_le_ofQ'`.
   The scale-extraction fold (`extractGap := completeLimit physGapSeq`) is essentially free
   because `physGap`+`physBound` are already a modulus-Cauchy datum.
3. **`physGapMin > 0` is correctly the single open frontier** (all strands) — the
   dimensional-transmutation content (gap survives `a→0` in physical units), uninhabited
   for 4D YM.
4. **Do NOT port the non-constructive theory**: Karamata UCT / Representation theorems
   (Baire–Steinhaus), Lang's PDE normal form, Dubrulle–Graner's functional-equation
   classification. Use the Bishop differential-quotient + explicit modulus + `completeLimit`,
   which already realize the constructive content. Modulus-as-data is load-bearing
   (Specker / Lubarsky) — validates `RegularCReal`.

## The decisive new finding (discrete scale invariance strand): KEEP THE BAND

- DSI (Sornette, Phys. Rep. 297 (1998)) permits log-periodic corrections
  `f(x)=x^ρ P(log x/log λ)` with complex exponents; then `f(x)/x` has `liminf < limsup`
  (a genuine band), and only the log/Cesàro average converges. The band is *provably real*
  in lattice-self-similar spectral problems (Strichartz, Proc. AMS 140 (2012);
  Lapidus–Pomerance lattice case).
- BUT ordinary 4D Yang–Mills has a UV *fixed point* (continuous scale invariance), not a
  limit cycle, so the expected approach is smooth, monotone, `O(a²·[log]^Γ̂)` — NO
  oscillation (Husung–Marquard–Sommer EPJC 80 (2020); Athenodorou–Teper glueball ratios,
  smooth even polynomial in a, no log-periodic term reported). So the band is expected to
  be *degenerate* (min=max) — but proving degeneracy is exactly the open uniqueness
  question (Balaban UV stability gives only a subsequence, uniqueness open).
- **Therefore:** target the two-sided BAND as primary (strictly weaker, robust, matches
  what compactness actually delivers, and `physGapMin>0` is all Clay needs). Band-collapse
  to a single limit is an OPTIONAL downstream lemma gated on a monotonicity side-condition
  (BGT Monotone Density Theorem 1.7.2). This refines the scale-extraction strand's
  "unique limit" into "unique *under monotonicity*."
- **Log-variable modulus:** work in `t_j = j·log λ` (geometric spacing `a_j=λ^{−j}` ⇒
  uniform Nat-steps), the home turf of `crealOfGeoIncrement`. Band edges = `completeLimit`
  of the running-min and running-max of `physGap`; optional Cesàro average = band mean.
  Three honest scalars `physGapMin ≤ physGapAvg ≤ physGapMax`.

## Nondimensionalization (dimensional-transmutation strand)

- Physical content is a pure number: `Δ = c·Λ`; cleanest dimensionless invariant is
  `Δ/√σ̂` (Buckingham-Π: {Δ,√σ̂}, 1 mass dimension ⇒ 1 invariant). SU(N) values numerical
  only; continuum open. Cross-check: `m(0++)/√σ` = SU(2) 3.781 > SU(3) 3.405 > SU(∞) 3.072
  — consistent with our R1 worst-case-is-SU(2) reduction.
- Carry the gap MULTIPLICATIVELY as a ratio (no division operator): `gapRatio·m_0 ≃ Δ`
  with `m_0=√σ̂` (already in `SqrtBridge`), positivity from `IsPositive Δ`/`IsPositive m_0`.
- Restate the open obligation dimensionlessly (`physGapRatio j · √σ̂_j ≃ physGap j`, open =
  positive limit of the ratio) ⇒ removes `999/1000`, `1/2` from theorem STATEMENTS.
- Quarantine fiducials: `unitScale` (σ̂, sqrtL = cancelling mass-unit choice) vs
  `gapFloorWitness` (sep, mFiducial = numeric claims). Formal precedent: ATOMSLab
  `LeanDimensionalAnalysis`, Botta–Jansson constructive Π-direction.

## PLAN OF ACTION (prioritized, sequenced)

Phase A — faithfulness/cleanup (low risk, high value, do first):
  A1. Make `physGap` a genuine `Q'`-quotient `latMargin j / spacing j` (rational division
      of positives; reuse `Sqrt.lean` reciprocal) so `physGap_spacing` becomes a THEOREM,
      not assumed data. Add the `divLimit` convenience lemma (5-line corollary of
      `isPositive_completeLimit` + `completeLimit_le_ofQ'`).
  A2. Nondimensionalize: add `gapRatio·m_0 ≃ Δ` (`Δ/√σ̂`) and the dimensionless
      `physGapRatio`; restate the open obligation as "positive limit of the ratio."
      Quarantine the four fiducials into `unitScale` vs `gapFloorWitness`.

Phase B — band-correct the interface (structural):
  B1. Reshape `RegScalingLimitModulus` to the two-sided BAND in the log-variable:
      running-min / running-max `completeLimit`s with geometric (`2^{−j}`) moduli;
      `physGapMin ≤ physGapAvg ≤ physGapMax`; `physGapMin>0` the single open content
      (stated dimensionlessly). Keep degree-1 homogeneity definitional.
  B2. `extractGap` scale-extraction fold (free) + `extractGap_band` (min/max edges).

Phase C — uniqueness/collapse (optional, honest):
  C1. `extractGap_unique_of_monotone`: band collapses to a single limit GIVEN a
      monotonicity side-condition (BGT Monotone Density). The RG-invariant uniqueness,
      gated — not asserted unconditionally.

Phase D — proof-of-concept (after A–C, against the corrected band interface):
  D1. φ⁴ d=2,3: instantiate the convergence-modulus machinery where the spacing-uniform
      modulus genuinely exists (Bauerschmidt–Dagallier). Validates the architecture;
      does NOT exercise YM gap-generation (φ⁴ mass is a tunable bare input). Label as such.

Do NOT: assert a single limit as primary; add an exponent field; port UCT/Lang-PDE/
Dubrulle-classification; let `999/1000`/`1/2` appear in theorem conclusions.

Sources (refereed unless flagged): Sornette Phys.Rep.297(1998); Bingham–Goldie–Teugels
*Regular Variation* (CUP 1987); Strichartz Proc.AMS 140(2012); Lapidus–Pomerance
Proc.LMS 66(1993); Husung–Marquard–Sommer EPJC 80(2020), PLB 829(2022); Athenodorou–Teper
JHEP 11(2020)/12(2021); Coleman–Weinberg PRD 7(1973); Gross–Wilczek & Politzer PRL 30(1973);
Shen–Zhu–Zhu CMP (arXiv:2204.12737); Lang Automatica 140(2022); Dubrulle–Graner JPhysII
6(1996); Yi–Huang–Simon–Doyle PNAS 2000; Buckingham Phys.Rev.4(1914); Balaban CMP 109(1987);
Leonel–Oliveira arXiv:2602.17839 (preprint); ATOMSLab arXiv:2509.13142; Botta–Jansson
arXiv:2308.09481.
</content>
