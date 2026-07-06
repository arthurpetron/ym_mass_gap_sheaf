/-
Track A / R2 — Round K of the fusion box log-concavity node: the CROSS-STRAND
LOCALISATION of the central-autoconvolution reserve.  Two new symbolic all-`s` atoms
that pin *exactly where* the reserve wall lives — the diagonal / single-strand content
holds with a proved margin to spare, so the SOLE open content is the cross-strand
aggregation — together with a CONSOLIDATED restatement of the exact
`FusionConvLogConcaveCore` and the complete downstream chain to the excited-suppression
(`S1Dominance`) datum.

# Why this module exists (read first — load-bearing honesty)

Rounds A–J reduced the box log-concavity core `SelfFusionLogConcave.FusionConvLogConcaveCore`
to a SINGLE quantitative local-CLT residual, reachable by two equivalent routes:

  * Track B (box / Cauchy–Binet): `FusionConvLogConcaveCore` ⟸ `UniformBoxLogConcave`
    ⟸ `UniformBoxQuadCertificate` ⟸ `QuadGershgorinClosure` (RoundA/B/C).
  * Track A (line-sum / autoconvolution): `S1Dominance` ⟸ `StrandReduction`
    ⟸ `CentralAutoconvReserve` ⟸ `AutoconvBumpBounds` ⟸ `AutoconvReserveResidual`
    (RoundD–J), the last being the central-autoconvolution log-concavity MARGIN
    `(1 + 31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.

Round J proved the DIAGONAL factor-`(3/4)` minor reserve and MACHINE-REFUTED the naive
symmetrised off-diagonal summand route (`symMinor_can_be_negative`).  So the wall is
genuinely the CROSS-STRAND aggregate cancellation, not a bookkeeping gap.

Round K localises this precisely.  The reserve constant is `256/225 = 1 + 31/225`.  Applied
to a SINGLE strand (or the diagonal `p = q` block of the autoconvolution defect), the
super-log-concavity atom `coeffW_superLogConcave` (`c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`, RoundC)
gives the reserve with a UNIFORM factor of room, because

    (256/225) · (1/4)  =  64/225  <  1.

So the diagonal / single-strand half of the reserve is TRUE with a `225/64 ≈ 3.5×` margin,
for every mode, symbolically on `w ≤ 1/2`.  The genuine open content — as Round J's
refutation already isolates — is exactly the CROSS-strand (`p ≠ q`) aggregation, where the
symmetrised minor is indefinite and needs the heat-kernel local-CLT cancellation.  These
atoms make the "where is the wall" verdict quantitative and machine-checked.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `coeffW_strandReserve` — the SINGLE-STRAND reserve: for `0 ≤ w ≤ 1/2` and every `s`,
        (1 + 31/225) · (c_s · c_{s+2})  ≤  c_{s+1} · c_{s+1}.
    The exact reserve constant `256/225`, discharged on one strand with margin (`64/225 ≤ 1`).
  * `fusionMeasure_superLogConcave` — the TWO-BODY (p = 2 fusion measure) magnitude reserve:
        (c_a·c_{a+2})·(c_b·c_{b+2})  ≤  (1/16) · ((c_{a+1}·c_{a+1})·(c_{b+1}·c_{b+1})).
    A factor-`1/16` strengthening of `R1LocalCLT.fusionMeasure_logConcave` (which has the
    plain factor `1`), on the strong-coupling window.  This is the magnitude reserve of the
    two-body fusion channel that builds `boxSum`.
  * `fusionConvLogConcaveCore_of_uniform` — CONSOLIDATION: a single `UniformBoxLogConcave w`
    witness (the sharp Track-B residual) inhabits `FusionConvLogConcaveCore N w` for EVERY
    `N` (re-export of `coreOfUniform`), and `s1Dominance_all_of_uniform` completes the chain
    to the excited-suppression datum `S1Dominance N w 2` for every `N` (with the per-`N`
    edge input).  The exact statement + the complete chain-to-defect in one auditable place.

# HONEST verdict and scope

Round K does NOT close the residual.  It proves the diagonal / single-strand half of the
reserve holds with a uniform margin, quantifying Round J's refutation into a precise "the
open content is the cross-strand aggregation" statement, and adds the two-body magnitude
reserve of the fusion channel.  The SOLE remaining open content is the cross-strand
aggregate cancellation — `AutoconvReserveResidual` / `LagCorrTP2` / `QuadGershgorinClosure`,
the heat-kernel `(r,d)` local-CLT — NOT a finite rational inequality, and NOT the (repeatedly
machine-refuted) generic "convolution preserves log-concavity".  This is a structural
sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap, and
it inhabits NO Clay-frontier bundle.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW_superLogConcave` / `mul_swap4` lemmas,
positive-factor monotonicity, and `decide` only on closed concrete-rational constants.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundJ

namespace YMGap.Continuum.FusionCoreStepRoundK

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC

/-- The exact reserve constant `256/225 = 1 + 31/225` (Round I's two-leg square
`(16/15)²`). -/
abbrev reserveC : Q' := 1 + Q'.mkPos 31 225 (by decide)

/-! ## 1. The single-strand reserve — the diagonal half holds with margin -/

/-- **`coeffW_strandReserve` — the single-strand reserve (all `s`, symbolic `w ≤ 1/2`).**

    (1 + 31/225) · (c_s · c_{s+2})  ≤  c_{s+1} · c_{s+1}.

This is `AutoconvReserveResidual`'s constant applied to a SINGLE strand.  It holds with a
uniform factor of room: `coeffW_superLogConcave` gives `c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`, and
`(256/225)·(1/4) = 64/225 ≤ 1`.  So the diagonal / single-strand half of the reserve is
`≈ 3.5×` inside the bound at every mode — the wall is NOT here.  The genuine open content is
the CROSS-strand (`p ≠ q`) aggregation (Round J's `symMinor_can_be_negative`). -/
theorem coeffW_strandReserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    reserveC * (coeffW w s * coeffW w (s + 2))
      ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  -- super-log-concavity: `c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`
  have h : coeffW w s * coeffW w (s + 2)
      ≤ quarter * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    coeffW_superLogConcave hw0 hw12 s
  have hsqnn : (0 : Q') ≤ coeffW w (s + 1) * coeffW w (s + 1) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (s + 1)) (coeffW_nonneg hw0 (s + 1))
  -- scale by `reserveC ≥ 0`
  have h1 : reserveC * (coeffW w s * coeffW w (s + 2))
      ≤ reserveC * (quarter * (coeffW w (s + 1) * coeffW w (s + 1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h (by decide)
  -- `reserveC · (quarter · Y) ≃ (reserveC · quarter) · Y`
  have e : (reserveC * (quarter * (coeffW w (s + 1) * coeffW w (s + 1)))).eqv
      ((reserveC * quarter) * (coeffW w (s + 1) * coeffW w (s + 1))) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv reserveC quarter _)
  -- `(reserveC · quarter) · Y ≤ 1 · Y ≤ Y`  since `reserveC · quarter = 64/225 ≤ 1`
  have h2 : (reserveC * quarter) * (coeffW w (s + 1) * coeffW w (s + 1))
      ≤ (1 : Q') * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : reserveC * quarter ≤ (1 : Q')) hsqnn
  refine Q'.le_trans' _ _ _ h1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
  exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 2. The two-body (p = 2 fusion measure) magnitude reserve -/

/-- The strong-coupling two-body reserve constant `1/16 = (1/4)²`. -/
abbrev sixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- **`fusionMeasure_superLogConcave` — the two-body magnitude reserve (all `a,b`, `w ≤ 1/2`).**

    (c_a·c_{a+2})·(c_b·c_{b+2})  ≤  (1/16) · ((c_{a+1}·c_{a+1})·(c_{b+1}·c_{b+1})).

This is the factor-`1/16` strong-coupling strengthening of
`R1LocalCLT.fusionMeasure_logConcave` (plain factor `1`): the two-body fusion channel that
builds `boxSum` carries a uniform `(1/4)²` magnitude reserve.  Proof: multiply two copies of
the RoundC atom `coeffW_superLogConcave` (nonneg factors) and combine `(1/4)·(1/4) = 1/16`
via the four-factor regroup `mul_swap4`. -/
theorem fusionMeasure_superLogConcave {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (a b : Nat) :
    (coeffW w a * coeffW w (a + 2)) * (coeffW w b * coeffW w (b + 2))
      ≤ sixteenth
          * ((coeffW w (a + 1) * coeffW w (a + 1))
             * (coeffW w (b + 1) * coeffW w (b + 1))) := by
  have hA : coeffW w a * coeffW w (a + 2)
      ≤ quarter * (coeffW w (a + 1) * coeffW w (a + 1)) :=
    coeffW_superLogConcave hw0 hw12 a
  have hB : coeffW w b * coeffW w (b + 2)
      ≤ quarter * (coeffW w (b + 1) * coeffW w (b + 1)) :=
    coeffW_superLogConcave hw0 hw12 b
  have hLBnn : (0 : Q') ≤ coeffW w b * coeffW w (b + 2) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 b) (coeffW_nonneg hw0 (b + 2))
  have hQAnn : (0 : Q') ≤ quarter * (coeffW w (a + 1) * coeffW w (a + 1)) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (a + 1)) (coeffW_nonneg hw0 (a + 1)))
  -- `LA·LB ≤ (¼A')·LB ≤ (¼A')·(¼B')`
  have step1 : (coeffW w a * coeffW w (a + 2)) * (coeffW w b * coeffW w (b + 2))
      ≤ (quarter * (coeffW w (a + 1) * coeffW w (a + 1))) * (coeffW w b * coeffW w (b + 2)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hA hLBnn
  have step2 : (quarter * (coeffW w (a + 1) * coeffW w (a + 1))) * (coeffW w b * coeffW w (b + 2))
      ≤ (quarter * (coeffW w (a + 1) * coeffW w (a + 1)))
          * (quarter * (coeffW w (b + 1) * coeffW w (b + 1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hB hQAnn
  -- `(¼A')·(¼B') ≃ (¼·¼)·(A'·B') ≃ (1/16)·(A'·B')`
  have eswap : ((quarter * (coeffW w (a + 1) * coeffW w (a + 1)))
        * (quarter * (coeffW w (b + 1) * coeffW w (b + 1)))).eqv
      ((quarter * quarter)
        * ((coeffW w (a + 1) * coeffW w (a + 1)) * (coeffW w (b + 1) * coeffW w (b + 1)))) :=
    mul_swap4 quarter (coeffW w (a + 1) * coeffW w (a + 1)) quarter
      (coeffW w (b + 1) * coeffW w (b + 1))
  have econst : ((quarter * quarter)
        * ((coeffW w (a + 1) * coeffW w (a + 1)) * (coeffW w (b + 1) * coeffW w (b + 1)))).eqv
      (sixteenth
        * ((coeffW w (a + 1) * coeffW w (a + 1)) * (coeffW w (b + 1) * coeffW w (b + 1)))) :=
    Q'.mul_eqv_congr_right (quarter * quarter) sixteenth _ (by decide)
  refine Q'.le_trans' _ _ _ step1 ?_
  refine Q'.le_trans' _ _ _ step2 ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eswap) (Q'.le_of_eqv econst)

/-! ## 3. Consolidation — the exact core statement and the complete chain to the defect -/

/-- **`fusionConvLogConcaveCore_of_uniform` — the sharp Track-B residual drives the whole
`N`-tower of the box log-concavity core.**  A single `UniformBoxLogConcave w` witness (the
direct box log-concavity for ALL `N`, the corrected uniform residual of RoundA) inhabits
`SelfFusionLogConcave.FusionConvLogConcaveCore N w` for EVERY `N`.  Re-export of
`FusionCoreStepRoundA.coreOfUniform`, surfaced here as the one-line consolidation of the
exact box-core statement against its single residual. -/
def fusionConvLogConcaveCore_of_uniform {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (u : UniformBoxLogConcave w) (N : Nat) :
    FusionConvLogConcaveCore N w hw0 hw1 :=
  coreOfUniform hw0 hw1 u N

/-- **`s1Dominance_all_of_uniform` — the complete chain to the excited-suppression datum.**
The single Track-B residual `UniformBoxLogConcave w` (plus the elementary per-`N`
first-excited edge `bmc 2 ≤ bmc 1`) drives `S1Dominance N w 2` — the `s = 1`-dominance /
excited-mode-suppression datum, i.e. the defect bound the bond-moving control consumes — for
EVERY `N`.  Re-export of `FusionCoreStepRoundA.s1DominanceOfUniform`, exhibiting that the
downstream chain `core ⟹ log-concavity ⟹ peak ⟹ s = 1-dominance` is COMPLETE: the ONLY open
content is the residual `u`. -/
def s1Dominance_all_of_uniform {w : Q'} (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (u : UniformBoxLogConcave w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfUniform hw hw1 u N hedge

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `coeffW_strandReserve` — the single-strand reserve `(1+31/225)·c_s·c_{s+2} ≤ c_{s+1}²`,
    all `s`, symbolic `w ≤ 1/2`, with the margin `(256/225)·(1/4) = 64/225 ≤ 1`.  The
    diagonal / single-strand half of `AutoconvReserveResidual` — proved, with room to spare.
  * `fusionMeasure_superLogConcave` — the two-body factor-`1/16` magnitude reserve of the
    p = 2 fusion channel (strong-coupling strengthening of `R1LocalCLT.fusionMeasure_logConcave`).
  * `fusionConvLogConcaveCore_of_uniform`, `s1Dominance_all_of_uniform` — the consolidated
    exact box-core statement + the complete downstream chain to `S1Dominance N w 2` (every
    `N`), driven by the single residual `UniformBoxLogConcave w`.

NAMED OPEN (carried, NOT inhabited here):
  * The CROSS-strand aggregation of the reserve — `AutoconvReserveResidual` (Track A) /
    `QuadGershgorinClosure` (Track B) / `LagCorrTP2` — where the symmetrised off-diagonal
    minor is indefinite (`FusionCoreStepRoundJ.symMinor_can_be_negative`).  This is the
    heat-kernel `(r,d)` Gaussian-theta local-CLT, NOT a finite rational inequality, and NOT
    the machine-refuted generic "convolution preserves log-concavity".

HONEST VERDICT.  Round K localises the reserve wall: the diagonal / single-strand half holds
with a uniform `≈ 3.5×` margin (proved, all `s`), and the two-body fusion channel carries a
`1/16` magnitude reserve.  So the SOLE open content is the cross-strand aggregate
cancellation.  The downstream chain (core ⟹ log-concavity ⟹ peak ⟹ `s = 1`-dominance) is
COMPLETE and re-exported.  This is a structural sharpening of one box-level log-concavity
sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundK

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundK.coeffW_strandReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundK.fusionMeasure_superLogConcave
#print axioms YMGap.Continuum.FusionCoreStepRoundK.fusionConvLogConcaveCore_of_uniform
#print axioms YMGap.Continuum.FusionCoreStepRoundK.s1Dominance_all_of_uniform
