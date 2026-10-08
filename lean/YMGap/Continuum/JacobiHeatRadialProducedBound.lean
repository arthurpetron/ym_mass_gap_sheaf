/-
# Actual finite heat radial inequality with a produced cost

The general-nome SAME-product ceiling and its signed finite-tail transport
now supply the missing analytic cost to the existing radial-mixture consumer.
All jets are the actual normalized Jacobi heat polynomial evaluated at 1+x.
The explicit cost is transverseCap(w)+radialTailPayment(w,N), past the stated
small-omitted-factor onset. There is no supplied product-cost inequality.

This is scalar pointwise nonnegativity, NOT a Haar square certificate or an
original interacting conditional/OS bound. The nome defect is not physical
time; no continuum or physical mass assertion is made.
-/

import YMGap.Continuum.ThetaProductRadialCeiling
import YMGap.Continuum.JacobiHeatRadialMomentJets

namespace YMGap.Continuum.JacobiHeatRadialProducedBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.JacobiHeatTransverseCurvature (transverseCap)
open YMGap.Continuum.JacobiProductRadialSignedTail (eighth radialTailPayment)
open YMGap.Continuum.JacobiHeatRadialMomentJets (heatRadialExpression heat_radial_nonnegative_of_productCost)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

/-- Actual finite radial cost, with the negative omitted-tail payment retained. -/
def radialCap (w : Q') (N : Nat) : Q' := transverseCap w + radialTailPayment w N

/-- Explicit sufficient cutoff for the omitted-factor onset; depends on w only. -/
def radialOnset (w : Q') : Nat := HKConvGen.powBaseCutoff w eighth

theorem radialOnset_small_factor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN : radialOnset w ≤ N) : HKPos.geoAmp w N ≤ eighth :=
  Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (m := N) (n := 2*N+1) (by omega))
    (Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hN)
      (HKConvGen.pow_base_le_cutoff hw0 hw1 (by decide : (0 : Q') < eighth)))

theorem radialCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (N : Nat) :
    (0 : Q') ≤ radialCap w N :=
  Q'.zero_le_add _ _
    (HKConvGen.geoTailBase_nonneg
      (Q'.zero_le_add _ _ (Q'.le_of_lt hw0) (Q'.le_of_lt hw0))
      (SumOfSquares.q_mul_self_nonneg w) 0)
    (HKConvGen.geoTailBase_nonneg
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 4)
        (Q'.pow_nonneg w (Q'.le_of_lt hw0) _))
      (SumOfSquares.q_mul_self_nonneg w) 0)

private theorem square_le_one {x : Q'} (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    x*x ≤ (1 : Q') := by
  have hp : (0 : Q') ≤ 1+x := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.add_neg_self_eqv 1)) (Q'.add_le_add_left 1 (-1) x hx0)
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hx1) hp)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 0)))
      (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
      (by decide) (fun _ => x)))

/-- Produced radial inequality for the SAME heat jets on the whole interval.
Empty prefixes are not excluded if they meet the explicit onset. -/
theorem heat_radial_nonnegative {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) :
    (0 : Q') ≤ heatRadialExpression w x (radialCap w N) N :=
  heat_radial_nonnegative_of_productCost hw0 hw1 hx0 (radialCap w N) N
    (radialCap_nonnegative hw0 N) (square_le_one hx0 hx1)
    (ThetaProductRadialCeiling.productRadialCost_le_cap_add_tail hw0 hw1 hx0 hx1 N hN)

/-- SAME finite heat inequality at the constructed coordinate-independent onset. -/
theorem heat_radial_nonnegative_at_onset {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN : radialOnset w ≤ N) :
    (0 : Q') ≤ heatRadialExpression w x (radialCap w N) N :=
  heat_radial_nonnegative hw0 hw1 hx0 hx1 N (radialOnset_small_factor hw0 hw1 N hN)

end YMGap.Continuum.JacobiHeatRadialProducedBound

#print axioms YMGap.Continuum.JacobiHeatRadialProducedBound.radialCap
#print axioms YMGap.Continuum.JacobiHeatRadialProducedBound.radialOnset
#print axioms YMGap.Continuum.JacobiHeatRadialProducedBound.radialOnset_small_factor
#print axioms YMGap.Continuum.JacobiHeatRadialProducedBound.radialCap_nonnegative
#print axioms YMGap.Continuum.JacobiHeatRadialProducedBound.heat_radial_nonnegative
#print axioms YMGap.Continuum.JacobiHeatRadialProducedBound.heat_radial_nonnegative_at_onset
