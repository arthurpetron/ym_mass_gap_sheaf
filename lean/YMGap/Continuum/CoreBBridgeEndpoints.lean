/-
Core-B endpoint closure.

The general implication

    AcNReserveAnalytic.FiniteSMargin w → FiniteSMarginWorstcase.CrossRatioMonotone w

is an honest interior residual.  This file closes both endpoints without assuming that
implication: at `w = wH` the cross inequality is reflexive, while at `w = 0` the factor
`acN 0 (s+1) (s+2)` vanishes term by term.  Thus any remaining obstruction is strictly an
interior-coupling phenomenon.
-/

import YMGap.Continuum.FiniteSMarginWorstcase
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.R1EvenCentreBound

namespace YMGap.Continuum.CoreBBridgeEndpoints

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FiniteSMarginWorstcase

/-- The upper off-centre autoconvolution at zero coupling vanishes exactly. -/
theorem acN_zero_upper (s : Nat) :
    (acN (0 : Q') (s + 1) (s + 2)).eqv 0 := by
  unfold acN
  apply FusionQuotientCollapse.fsum_zero_below
  intro p hp
  have hk : 1 ≤ s + 2 - p := by omega
  have hc : (coeffW (0 : Q') (s + 2 - p)).eqv 0 :=
    R1EvenCentreBound.coeffW_zero (Q'.eqv_refl 0) (s + 2 - p) hk
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (coeffW (0 : Q') p) _ _ hc) ?_
  exact Q'.mul_zero_eqv _

/-- At the worst coupling `wH`, the cross-ratio comparison is equality. -/
def crossRatioMonotone_wH : CrossRatioMonotone wH where
  cross := fun _ => Q'.le_refl' _

/-- At zero coupling, the left cross-ratio product vanishes and the right side is nonnegative. -/
def crossRatioMonotone_zero : CrossRatioMonotone (0 : Q') where
  cross := fun s => by
    have hB : (acN (0 : Q') (s + 1) (s + 2)).eqv 0 := acN_zero_upper s
    have hAB :
        (acN (0 : Q') (s + 1) s * acN (0 : Q') (s + 1) (s + 2)).eqv 0 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (acN (0 : Q') (s + 1) s) _ _ hB) ?_
      exact Q'.mul_zero_eqv _
    have hleft :
        ((acN (0 : Q') (s + 1) s * acN (0 : Q') (s + 1) (s + 2)) *
          (acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1))).eqv 0 := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _
          (acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1)) hAB) ?_
      exact Q'.zero_mul_eqv _
    have hright : (0 : Q') ≤
        (acN wH (s + 1) s * acN wH (s + 1) (s + 2)) *
          (acN (0 : Q') (s + 1) (s + 1) * acN (0 : Q') (s + 1) (s + 1)) := by
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (acN_nonneg (by decide) _ _) (acN_nonneg (by decide) _ _))
        (Q'.mul_nonneg _ _ (acN_nonneg (by decide) _ _) (acN_nonneg (by decide) _ _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hright

/-- The named Core-B implication is inhabited at the worst-coupling endpoint. -/
def finiteSMargin_to_crossRatio_wH (_ : FiniteSMargin wH) : CrossRatioMonotone wH :=
  crossRatioMonotone_wH

/-- The named Core-B implication is inhabited at the zero-coupling endpoint. -/
def finiteSMargin_to_crossRatio_zero (_ : FiniteSMargin (0 : Q')) :
    CrossRatioMonotone (0 : Q') :=
  crossRatioMonotone_zero

end YMGap.Continuum.CoreBBridgeEndpoints

#print axioms YMGap.Continuum.CoreBBridgeEndpoints.acN_zero_upper
#print axioms YMGap.Continuum.CoreBBridgeEndpoints.crossRatioMonotone_wH
#print axioms YMGap.Continuum.CoreBBridgeEndpoints.crossRatioMonotone_zero
#print axioms YMGap.Continuum.CoreBBridgeEndpoints.finiteSMargin_to_crossRatio_wH
#print axioms YMGap.Continuum.CoreBBridgeEndpoints.finiteSMargin_to_crossRatio_zero
