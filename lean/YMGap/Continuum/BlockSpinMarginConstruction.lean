/-
# Constructing the REAL block-spin eigenvalue margin — dissolving the free-field
# vacuity of `SingleStepDefectReduction.SingleStepDefectBound.trueMargin`, and the
# machine-refutation of the naive identification.

## The obligation this module attacks

`SingleStepDefectReduction.SingleStepDefectBound` carries the physical margin as a
**FREE** field `trueMargin : Nat → Q'`, and its sole open field

    singleStep : ∀ k, (1 − afDefectSeq afr k) · trueMargin k ≤ trueMargin (k+1)

is therefore VACUOUSLY fakeable by `trueMargin := afDefectSeq`-derived data.  Routes
H/I PROVED the analytic side (the renormalized defect `δ_ren ≤ 6(1−w)²` uniformly; the
multiplicity-blind fusion defect `= 0`).  The remaining content is the physical
IDENTIFICATION: is there a CONCRETE (non-free) `trueMargin` that is the genuine 4D
block-spin margin AND satisfies `singleStep`?

## What this module does — CONSTRUCT the concrete margin, then test it adversarially

1. **`eigMarginSeq afr k := 1 − w_k³`** — the CONCRETE (non-free) multiplicity-blind
   *eigenvalue* margin `1 − eigA(w_k, 1)` (`GapIsEigenvalue` VERDICT A: the physical
   gap edge is the transfer EIGENVALUE `eigA w 1 = w^{C₄(1)} = w³`, not the amplitude
   `coeffW`).  `w_k = afr.w (afCutoff afr + k)` is the AF-flowed coupling (Route F:
   the real `reconTransfer_located_gap.sep` IS the character eigenvalue, so `1 − w_k³`
   is the real fixed-spacing eigenvalue margin at RG scale `k`).  This is a genuine
   `Nat → Q'`, NOT a free field.

2. **`eigMargin_degradation_eq_shift`** — the EXACT additive degradation identity
   `eigMarginSeq k − eigMarginSeq (k+1) ≃ eigShiftSeq k = w_{k+1}³ − w_k³`, the
   multiplicity-blind coupling-flow EIGENVALUE SHIFT (Route I's `bulk_shift`).  Proved
   as a `Q'` identity for EVERY AF rate.

3. **THE CRUX — `eigMargin_fails_singleStep` (machine-refutation).**  The constructed
   eigenvalue margin does **NOT** satisfy the MULTIPLICATIVE `singleStep`.  At the
   genuine canonical AF-trajectory pair `w₁₀ = 10/11`, `w₁₁ = 11/12` (the canonical
   `afRateModulus_canonical.w`, `1 − wₖ = 1/(k+1)`), with the REAL model defect
   `δ = bondMovingDeltaRen 1 1 (10/11)` (= `afDefectSeq` at that coupling):

       (1 − δ)·(1 − w₁₀³)  =  419377/1771561  ≈ 0.23673
                > 1 − w₁₁³  =  397/1728        ≈ 0.22975 ,

   so `(1 − δ)·trueMargin_k ≤ trueMargin_{k+1}` is **FALSE** — proved by `decide`
   (zero axioms).  Hence the eigenvalue-margin construction canNOT inhabit
   `SingleStepDefectBound`; **no guarded bundle is inhabited, no guard trips**.

4. **`eigShift_le_delta_at_pair` (contrast).**  At the SAME pair the ADDITIVE Route-I
   bound `w₁₁³ − w₁₀³ ≤ δ` DOES hold (`43561/2299968 ≤ 64/1331`, `decide`).  So the
   genuine residual is the *additive* eigenvalue-shift bound `EigenvalueShiftDefect`,
   NOT the *multiplicative* `singleStep` — the two are genuinely different, and the
   fixed-spacing eigenvalue margin satisfies only the former.

## Honest verdict (Rule 6 / Rule 9)

The construction is CONCRETE (dissolves the *free-field* vacuity by exhibiting a real
`Nat → Q'`), but it is **NOT** the physical dimensionless margin `m_lat(a_k)/a_k`:
the fixed-spacing eigenvalue margin `1 − w_k³ → 0` as `w_k → 1` (deep UV), whereas the
dimensionless physical margin converges to `m_phys > 0`.  A sequence tending to `0`
cannot satisfy a MULTIPLICATIVE recursion `(1−δ_k)·m_k ≤ m_{k+1}` with SUMMABLE `δ_k`
and a POSITIVE floor (that would force `m_k ≥ m_0·∏(1−δ_k) > 0`) — which is exactly why
`singleStep` is refuted.  The missing ingredient is the spacing rescaling (the
accumulated block factor `b^k`) that converts the eroding fixed-spacing gap into the
RG-invariant dimensionless margin.  So the identification does NOT close
`SingleStepDefectBound`; it REDUCES the free-field vacuity to a genuine, concrete,
non-free obligation: supply the dimensionful rescaling so that the eigenvalue-shift
numerator combines with the `a_k` denominator into the multiplicative margin recursion.
`SingleStepDefectBound`, `TrueMarginRecursion`, `FrontierDAG` are NOT inhabited; the
4D Yang–Mills mass gap remains OPEN; nothing is faked; no free field is left.

## Axiom gate (Rule 1 / Rule 8)

Pure `Q'`/`Nat` construction reusing the proved `bondMovingDeltaRen`, `qpow`, `c4`,
`afCutoff`.  Every load-bearing declaration is gated below; the `decide` refutations
depend on NO axioms; the algebraic identity on `[propext]`/`[propext, Quot.sound]`.
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.RouteIEigenvalueDefect

namespace YMGap.Continuum.BlockSpinMarginConstruction

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 1. The concrete (non-free) eigenvalue margin and eigenvalue shift. -/

/-- **The CONCRETE multiplicity-blind eigenvalue margin** at RG scale `k`:
`1 − eigA(w_k, 1) = 1 − w_k^{C₄(1)} = 1 − w_k³`, with `w_k = afr.w (afCutoff afr + k)`
the AF-flowed coupling.  This is the real fixed-spacing transfer eigenvalue margin
(Route F: `reconTransfer_located_gap.sep = coeffW gw 1`; Route I: the gap edge is the
eigenvalue `eigA`, not the amplitude).  A genuine `Nat → Q'`, NOT a free field. -/
def eigMarginSeq (afr : AFRateModulus) (k : Nat) : Q' :=
  1 - qpow (afr.w (afCutoff afr + k)) (c4 1)

/-- **The eigenvalue shift** (multiplicity-blind coupling-flow degradation,
Route I `bulk_shift`): `eigA(w_{k+1}, 1) − eigA(w_k, 1) = w_{k+1}³ − w_k³`. -/
def eigShiftSeq (afr : AFRateModulus) (k : Nat) : Q' :=
  qpow (afr.w (afCutoff afr + (k + 1))) (c4 1)
    - qpow (afr.w (afCutoff afr + k)) (c4 1)

/-! ## 2. The exact additive degradation identity. -/

/-- General `Q'` identity: `(1 − a) − (1 − b) ≃ b − a`.  Pure additive algebra. -/
theorem oneSub_sub_oneSub_eqv (a b : Q') :
    ((1 - a) - (1 - b)).eqv (b - a) := by
  show (((1 : Q') + -a) + (-((1 : Q') + -b))).eqv (b + -a)
  have h1 : (-((1 : Q') + -b)).eqv ((-1 : Q') + b) :=
    Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-b))
      (Q'.add_eqv_congr_left (-1 : Q') _ _ (Q'.neg_neg_eqv b))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((1 : Q') + -a) _ _ h1) ?_
  -- ((1 + -a) + (-1 + b)).eqv (b + -a)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv ((1 : Q') + -a) (-1 : Q') b)) ?_
  -- (((1 + -a) + -1) + b).eqv (b + -a)
  have hL : (((1 : Q') + -a) + (-1 : Q')).eqv (-a) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-1 : Q') (Q'.add_comm_eqv (1 : Q') (-a))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-a) (1 : Q') (-1 : Q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
    exact q_add_zero_eqv (-a)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ b hL) ?_
  exact Q'.add_comm_eqv (-a) b

/-- **The exact additive degradation identity.**  The per-step degradation of the
CONCRETE eigenvalue margin equals the multiplicity-blind coupling-flow eigenvalue
shift, for EVERY AF rate:

    eigMarginSeq afr k − eigMarginSeq afr (k+1)  ≃  eigShiftSeq afr k
                                                 =  w_{k+1}³ − w_k³ . -/
theorem eigMargin_degradation_eq_shift (afr : AFRateModulus) (k : Nat) :
    (eigMarginSeq afr k - eigMarginSeq afr (k + 1)).eqv (eigShiftSeq afr k) := by
  unfold eigMarginSeq eigShiftSeq
  exact oneSub_sub_oneSub_eqv _ _

/-! ## 3. THE CRUX — the constructed margin FAILS the multiplicative `singleStep`.

`afDefectSeq afr k = renDefect afr pMult (afCutoff afr + k)
   = bondMovingDeltaRen 1 1 (afr.w (afCutoff afr + k))` (`pMult = 1`), so the model
defect at coupling `w` is exactly `bondMovingDeltaRen 1 1 w`.  We instantiate the
`singleStep` predicate `(1 − δ)·(1 − w³) ≤ 1 − w'³` at the genuine consecutive
canonical AF-trajectory couplings `w = 10/11 = w₁₀`, `w' = 11/12 = w₁₁`
(`afRateModulus_canonical.w k = 1 − 1/(k+1)`), and REFUTE it. -/

/-- `w₁₀ = 10/11`, the canonical AF-trajectory coupling at scale `10`. -/
def wTen : Q' := Q'.mkPos 10 11 (by decide)

/-- `w₁₁ = 11/12`, the canonical AF-trajectory coupling at scale `11`. -/
def wEleven : Q' := Q'.mkPos 11 12 (by decide)

/-- **THE MACHINE-REFUTATION.**  The CONCRETE eigenvalue margin does NOT satisfy the
MULTIPLICATIVE `singleStep` inequality `(1 − δ_model)·(1 − w³) ≤ 1 − w'³` at the
genuine canonical AF pair `w = 10/11`, `w' = 11/12`, with the REAL model defect
`δ_model = bondMovingDeltaRen 1 1 (10/11)`.  Exact values:

    (1 − δ)·(1 − w³) = 419377/1771561 ≈ 0.23673  >  1 − w'³ = 397/1728 ≈ 0.22975 .

Hence `SingleStepDefectBound` canNOT be inhabited by `trueMargin := eigMarginSeq`:
the fixed-spacing eigenvalue margin `1 − w_k³` (which erodes to `0` as `w → 1`) is NOT
the RG-invariant dimensionless margin the multiplicative recursion demands.  Proved by
kernel `decide` (ZERO axioms). -/
theorem eigMargin_fails_singleStep :
    ¬ ((1 - bondMovingDeltaRen 1 1 wTen) * (1 - qpow wTen (c4 1))
        ≤ 1 - qpow wEleven (c4 1)) := by decide

/-- **The additive Route-I bound HOLDS at the same pair (contrast).**  The
multiplicity-blind eigenvalue shift is dominated by the model defect additively:

    w'³ − w³ = 43561/2299968  ≤  δ_model = bondMovingDeltaRen 1 1 (10/11) = 64/1331 .

So the genuine residual is the ADDITIVE eigenvalue-shift bound (`EigenvalueShiftDefect`,
`RouteIEigenvalueDefect`), which the constructed margin's degradation obeys — NOT the
multiplicative `singleStep`, which it violates.  Kernel `decide` (ZERO axioms). -/
theorem eigShift_le_delta_at_pair :
    qpow wEleven (c4 1) - qpow wTen (c4 1) ≤ bondMovingDeltaRen 1 1 wTen := by decide

/-- The two facts bundled: the constructed eigenvalue margin obeys the ADDITIVE
eigenvalue-shift bound but VIOLATES the multiplicative `singleStep`, at the same
genuine canonical AF pair.  This is the precise statement that the fixed-spacing
eigenvalue margin reduces the free-field vacuity to the additive residual while
demonstrating it is NOT the multiplicative margin `SingleStepDefectBound` requires. -/
theorem additive_holds_multiplicative_fails :
    (qpow wEleven (c4 1) - qpow wTen (c4 1) ≤ bondMovingDeltaRen 1 1 wTen)
    ∧ ¬ ((1 - bondMovingDeltaRen 1 1 wTen) * (1 - qpow wTen (c4 1))
          ≤ 1 - qpow wEleven (c4 1)) :=
  ⟨eigShift_le_delta_at_pair, eigMargin_fails_singleStep⟩

/-! ## 4. Honesty theorem (documentation carrier). -/

/-- **HONEST VERDICT.**  `eigMarginSeq` is a CONCRETE (non-free) `Nat → Q'` — the real
fixed-spacing multiplicity-blind eigenvalue margin `1 − w_k³` (Route F/I) — whose exact
per-step degradation is the eigenvalue shift `w_{k+1}³ − w_k³`
(`eigMargin_degradation_eq_shift`).  It obeys the ADDITIVE eigenvalue-shift bound
(`eigShift_le_delta_at_pair`) but PROVABLY VIOLATES the MULTIPLICATIVE `singleStep`
(`eigMargin_fails_singleStep`), because `1 − w_k³ → 0` as `w_k → 1` while a positive
multiplicative floor demands `m_k ≥ m_0·∏(1−δ_k) > 0`.  Therefore the construction does
NOT inhabit `SingleStepDefectBound` / `TrueMarginRecursion` / `FrontierDAG`: it dissolves
the *free-field* vacuity (a concrete object, tied to the real transfer eigenvalue) but
reveals the identification `realLeak = δ_ren` does NOT close the MULTIPLICATIVE margin
recursion — the genuine remaining obligation is the dimensionful spacing rescaling that
turns the eroding fixed-spacing eigenvalue margin into the RG-invariant dimensionless
margin `m_lat/a`.  No guarded bundle is inhabited; the 4D Yang–Mills mass gap remains
OPEN; nothing is faked. -/
theorem blockSpinMargin_honesty : True := trivial

end YMGap.Continuum.BlockSpinMarginConstruction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BlockSpinMarginConstruction.oneSub_sub_oneSub_eqv
#print axioms YMGap.Continuum.BlockSpinMarginConstruction.eigMargin_degradation_eq_shift
#print axioms YMGap.Continuum.BlockSpinMarginConstruction.eigMargin_fails_singleStep
#print axioms YMGap.Continuum.BlockSpinMarginConstruction.eigShift_le_delta_at_pair
#print axioms YMGap.Continuum.BlockSpinMarginConstruction.additive_holds_multiplicative_fails
