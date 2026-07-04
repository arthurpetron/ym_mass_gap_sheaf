# Core-B Decision Memo: the p≥2 discrete SU(2) fusion local-CLT saddle estimate

Date: 2026-07-03
Status: OPEN research. This memo records the sharpest current state of Core B, not a closure. The Clay Yang–Mills mass gap remains open.

## 0. What Core B is

The single named-open residual is the **p≥2 discrete SU(2) fusion local-CLT saddle estimate**. For the
vacuum-normalized p-fold fusion kernel `K_{w,p}(s)` (Lean: `FusionKernelStatement.fusionEig s = bmc(s)/((s+1)·bmc(0))`),
the claim is the saddle log form

```
log K_{w,p}(s) = -A_p(w)·C2(s) + R_p(s,w),   |R_p(s,w)| ≤ eta_p(w)·C2(s)^2
```

with saddle moduli `A_p(w)`, `eta_p(w)` as DATA. The same wall re-appears on the Tier-0 (tilted-variance)
side as `LineSumLogConcaveCR` / `MeanExpConvex`, which `MeanExpConvexProgress` reduced through the Casimir
moment identity (`casimir_secondDiff_eq_two`: Δ²C4 = 2) to the tight second-difference bound
`XMeanSecondDiffLeOne` (`d2x = ⟨x⟩_s + ⟨x⟩_{s+2} − 2⟨x⟩_{s+1} ≤ 1`), and further to the two halves
`MeanShiftHalf` + `MeanShiftComplementHalf`. Both faces are the same saddle/tilted-variance physics.

Three tranches were produced in parallel: a numerical pilot, a prose chapter, and a Lean reduction. This
memo synthesizes them and issues the mechanize / iterate-prose / route-change decision.

## 1. What the pilot measured

Source: `computations/core_b_pilot.py`, `tests/test_core_b_pilot.py` (16 tests, green ~2s),
`visualizations/pilot/core_b/core-b-pilot.json` + 5 SVGs.

**Grid.** w ∈ {1/2, 2/3, 7/9, 11/12, 95/96}, p ∈ {1, 2, 3, 4, 8, 16, 27, 64}. `A_p`, `eta_p` extracted by
`A_p = argmin_A sup_{1≤s} |L(s)+A·C2(s)|/C2(s)^2`; `eta_p` = that min.

**Result — the estimate side is load-bearing and passes with wide margin.**
- Saddle remainder `eta_p(w)` is under the **1/12 = 0.0833** budget in EVERY cell. Worst case
  `eta = 0.00246` at (w=1/2, p=2); minimum budget margin **34×**; `eta_fail_boundary = []` (none).
- Structure is monotone on the bulk: worst = smallest w and p=2; `eta` decays fast in p and in w
  (e.g. at w=2/3, p=2: 2.9e-4; at w=11/12, p=2: 3.6e-7).
- The p=1 anchor is exact: `eta ≈ 0` (≤1e-36), matching `saddleLocalCLT_p1`.

**Result — the LITERAL Lean field is FALSE for p≥2 (the sharp diagnostic).**
- `SaddleLocalCLT.bulkShiftBound` as literally stated — `max_s (fusionEig s − eigA w s) ≤ 1/12` with the
  bare p=1 rate `eigA = w^{c4·s}` — EXCEEDS 1/12 for **every** p≥2 at **every** w. `literal_fail_boundary`
  = all 35 non-anchor cells. Magnitude: 0.11–0.24 at p=2, rising to 0.85–0.91 at p=64. Exactly 0 at p=1.
- **The fix is pinpointed:** re-base the reference rate from the bare `w^{c4·s}` to `w_eff = exp(−A_p)`.
  Re-based shift `max_s |fusionEig s − w_eff^{c4·s}|` returns under 1/12 in every cell (max ≈ 0.012).

**Tier-0 mirror validated (exact `Fraction` arithmetic).**
- Casimir identity exact: Δ²C4 = 2 for all sampled s (`casimir_second_diff_two = true`).
- Tight face holds with margin: `max_s d2x = 0.620 < 1` (≈38% headroom under the `XMeanSecondDiffLeOne` floor).
- Two-halves split carries positive slack in the sampled window (half slack up to 0.50, complement slack up
  to 0.539) — corroborating but NOT proving `MeanShiftHalf`/`ComplementHalf` (the metric reports max slack,
  not the tightest cell; the robust, proof-relevant face is `d2x ≤ 1`).
- Mean-of-product identity `pfmom_split` reproduced to machine precision: rel-err 1.9e-17.

**Honest caveats the pilot itself measured (Rule 5 respected — no analytic estimate proved):**
1. The literal `bulkShiftBound` (bare `eigA = w^{c4·s}`) is unsatisfiable for p≥2 and MUST be re-based to `w_eff`.
2. `eta` monotonicity holds only on the bulk window w ≤ 11/12; a ~1e-6 anomaly appears at w=95/96 (deep
   near-boundary corner), so monotonicity claims are bulk-window only.

## 2. What the prose established vs. gap-flagged

Source: `formal/core-b-local-clt.tex` (not compiled — No-build per instructions; no tests this tranche).

**Established / reconciled with the six Lean modules:**
- Corrected the §4 remark from the **circular** `d2A ≤ 1−2dB` split (and its refuted `d2A ≤ 0` claim) to the
  **genuine non-circular** two-halves decoupling `d2x = (d2x − dB) + dB` with `dB ≤ 1/2` (`MeanShiftHalf`)
  and `d2x − dB ≤ 1/2` (`MeanShiftComplementHalf`), wired through `meanExpConvex_of_halves`.
- Added the complement half to the constants table; fixed a module misattribution (`coeffW_rect` lives in
  `FusionCoreStepRoundE`, not `RoundI`). All ~30 modref citations spot-checked against Lean definition sites.
- Documents the unification: `d2x ≤ 1` ⟹ mean-exp convexity is proved.

**Gap-flagged (five GAP remarks + OPEN/DATA table flags):** the p≥2 saddle estimate remains open in all three
equivalent guises — the saddle remainder `|R_p| ≤ eta_p·C2^2` / shift ≤ 1/12 (`SaddleLogForm`, p≥2); the
tight tilted-variance bound `d2x ≤ 1` (`XMeanSecondDiffLeOne`); the two universal-sign halves; plus the
general-p PF2 log-concavity + `AutoconvDefectReserve` aggregate cancellation on the box side.

## 3. What the Lean reduction proved (did fusion unify onto Tier-0?)

Source: `lean/YMGap/Continuum/FusionSaddleReduction.lean` (`lake build` green; `#print axioms` = [propext, Quot.sound]).

**Verdict on the postulate route: FALSE — no instantiation collapse.** The honest artifact shipped instead is a
sharp, axiom-clean **RELOCATION at p=2**, which DOES unify the fusion face onto the Tier-0 Casimir/d2x residual:
- `bulkShiftBound_p2_of_tier0` reduces the p=2 fusion saddle residual `SaddleLocalCLT.bulkShiftBound` to
  Tier-0 `XMeanSecondDiffLeOne` PLUS two new named-open bridges.
- `gap_reduction_p2_of_tier0` carries it into the δ-loop capstone `GapReductionConclusion`.
- `fusionEig_p2_le_of_bridge` is the one genuinely PROVED bridge (transports an additive-coordinate upper
  bound onto the fusion eigenvalue via `divPos_le_of_le_mul`).

**Two new named-open (uninhabited) bridge residuals:**
1. `FusionAdditiveBridge N w` — the sharp CG↔additive coordinate identity
   `bondMovedCoeff N w 2 s ≃ acN w (s+1) s` (object gap: `fusionInd`-truncated `fusionPow` vs plain `acN`).
2. `CurvatureToShift N w` — curvature ⟹ additive pointwise first-order shift, consuming `XMeanSecondDiffLeOne`
   (differential-order gap: discrete vacuum-anchored double-summation).

**Scope limit (honest):** this reduction is **p=2 ONLY** — the additive `mu_eq` has no p-body analogue, so
general p≥2 is untouched. YMGap.lean / YMGapGuard.lean untouched; no frontier type inhabited.

## 4. THE DECISION

**Decision: ITERATE PROSE → then MECHANIZE the p=2 face. Do NOT change route.**

Rationale. The three tranches agree on a coherent picture: (a) the estimate side is real and satisfiable with
30×+ margin and monotone bulk structure — the physics is not in doubt; (b) the literal Lean field was mis-stated
and the pilot pinpointed the exact fix (`w_eff = exp(−A_p)` re-basing); (c) the Lean tranche already unified the
fusion face onto Tier-0 curvature at p=2, factored through exactly two precisely-named bridges plus the one
Tier-0 core. This is the right shape to push — not a route change. A route change is unjustified because no
tranche found the current route unsatisfiable; on the contrary, every diagnostic is GO on the estimate side.

**The single named residual Core B now rests on:** the tight Tier-0 second-difference bound
`XMeanSecondDiffLeOne` (`d2x ≤ 1`), equivalently `MeanShiftHalf` + `MeanShiftComplementHalf`. At p=2 the fusion
saddle face is now provably downstream of this plus the two structural bridges `FusionAdditiveBridge` and
`CurvatureToShift`. All three faces saturate the SAME even-s / w→0 corner (worst cell w=1/2, p=2).

**Two prose corrections are load-bearing before mechanization** (hence prose-first):
1. Re-state `SaddleLocalCLT.bulkShiftBound` against `w_eff = exp(−A_p)`, NOT the bare `w^{c4·s}` — the literal
   field is unsatisfiable for p≥2 (35/35 cells fail) and must not be carried into any Lean obligation as stated.
2. Restrict `eta`-monotonicity statements to the bulk window w ≤ 11/12 (95/96 anomaly).

**Recommended next concrete step (single, de-risked):** prove `FusionAdditiveBridge N w` for p=2 — the
CG-fusion = additive-conv-modulo-truncation coordinate identity `bondMovedCoeff N w 2 s ≃ acN w (s+1) s`. It is
a finite algebraic/combinatorial object identity (no analysis), the pilot already mirrors both sides
(`bondMovedCoeff` and `acN`) and can serve as an exact-arithmetic oracle to pin the truncation bookkeeping, and
discharging it collapses the p=2 fusion residual onto `CurvatureToShift` + the single Tier-0 core `d2x ≤ 1`. The
irreducible open core after that remains the general p≥2 discrete SU(2) fusion local-CLT (either face).
