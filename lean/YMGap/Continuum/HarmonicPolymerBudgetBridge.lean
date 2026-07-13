/-
# Harmonic-to-polymer budget bridge

The canonical harmonic tail starts exactly at the defect cutoff used by the
proved inverse-square summability theorem.  This module transports that
unshifted tail estimate to `afDefectSeq`, proves that its closed rational
budget is strictly below one, and composes it with the concrete harmonic
true-margin drop.  Thus no additional summability hypothesis remains between
the harmonic single-step estimate and the multiscale polymer floor.

This does not assume or inhabit `HarmonicTrueMarginDrop`; that cross-scale
physical estimate remains the sole input of the composition.
-/

import YMGap.Continuum.HarmonicTrueMarginStep
import YMGap.Continuum.MultiScalePolymerAssembly

namespace YMGap.Continuum.HarmonicPolymerBudgetBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.HarmonicTrueMarginStep
open YMGap.Continuum.MultiScalePolymerAssembly
open YMGap.Continuum.SingleStepDefectReduction
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.UniformCouplingFromAF

/-- Shifting the model defect into `afDefectSeq` only changes the starting
index of the same finite tail sum. -/
theorem afDefectSeq_tailSum_shift (afr : AFRateModulus) :
    ∀ K : Nat,
      tailSum (afDefectSeq afr) 0 K =
        tailSum (renDefect afr pMult) (afCutoff afr) K
  | 0 => rfl
  | K + 1 => by
      rw [tailSum_succ, tailSum_succ, afDefectSeq_tailSum_shift afr K]
      unfold afDefectSeq
      rw [Nat.zero_add]

/-- The exact rational budget inherited by the tail-shifted model defect. -/
def harmonicModelBudget : Q' :=
  tailR afRateModulus_canonical pMult
    (afCutoff afRateModulus_canonical)

/-- The derived budget is the exact rational `72/145`: `Aconst = 72` and the
cutoff potential is `1/145`. -/
theorem harmonicModelBudget_eqv_72_145 :
    harmonicModelBudget.eqv (Q'.mkPos 72 145 (by decide)) := by
  decide

/-- Every canonical model-defect prefix is controlled by the closed harmonic
budget. -/
theorem canonical_model_budget (K : Nat) :
    tailSum (afDefectSeq afRateModulus_canonical) 0 K ≤
      harmonicModelBudget := by
  rw [afDefectSeq_tailSum_shift]
  exact renDefect_summable afRateModulus_canonical pMult
    (afCutoff afRateModulus_canonical) K

/-- At the derived cutoff `144`, the closed inverse-square budget is strictly
below one.  This is kernel evaluation of an exact rational, not measurement. -/
theorem harmonicModelBudget_lt_one : harmonicModelBudget < (1 : Q') := by
  decide

/-- A harmonic true-margin drop supplies the positive multiscale floor with
the already-proved canonical model budget; no independent budget hypothesis
is required. -/
theorem harmonic_trueMargin_multiscale_floor (H : HarmonicTrueMarginDrop) :
    ∀ k : Nat,
      (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 ≤
          canonicalHarmonicTrueMargin k ∧
        (0 : Q') <
          (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 := by
  let S := singleStepDefectBound_of_harmonicDrop H
  exact trueMargin_multiscale_floor_of_budget S harmonicModelBudget
    canonical_model_budget harmonicModelBudget_lt_one

#print axioms afDefectSeq_tailSum_shift
#print axioms harmonicModelBudget_eqv_72_145
#print axioms canonical_model_budget
#print axioms harmonicModelBudget_lt_one
#print axioms harmonic_trueMargin_multiscale_floor

end YMGap.Continuum.HarmonicPolymerBudgetBridge
