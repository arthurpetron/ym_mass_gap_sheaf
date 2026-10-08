/-
# Produced general-nome ceiling on the SAME Jacobi product radial cost

The actual completed addition square has a nonnegative right side on [-1,1].
The original product's explicit positive floor cancels its normalization,
without a reciprocal in the upper-bound coefficient. The actual endpoint
ceiling gives D(x) <= 2*w/(1-w*w) at every strict nome. Signed finite tails
then pay the original finite costs, including their negative omitted terms.

The scaled estimate is in the scalar nome defect 1-w, not a physical clock.
No coupling/spacing calibration, Haar certificate, original conditional form,
OS operator bound or continuum gap is asserted.
The sharper finite endpoint telescope also passes through the SAME completed
addition comparison, giving 1+1/(1-w*w) globally with the explicit finite tail.
No hemisphere support of the original interacting law is assumed.
-/

import YMGap.Continuum.ThetaCompletedAdditionSquare
import YMGap.Continuum.ThetaProductStrictFloor
import YMGap.Continuum.JacobiProductRadialEndpoint
import YMGap.Continuum.JacobiProductRadialNearFlatBound
import YMGap.Continuum.RCBilinearDifference
import YMGap.Continuum.RateMatchFloor

namespace YMGap.Continuum.ThetaProductRadialCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaOneSidedSeriesCompletion (alternatingCReal)
open YMGap.Continuum.JacobiProductRadialLimit
open YMGap.Continuum.JacobiProductRadialSignedTail
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation (productRadialCost)
open YMGap.Continuum.JacobiHeatTransverseCurvature (transverseCap transverseCap_nome_defect_le_one)
open YMGap.Continuum.RateMatchFloor (geRat_equiv_transfer leEv_of_geRat_sub)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

/-- The cancellation floor is computed from the original product floor only. -/
def normalizationFloor (w : Q') : Q' :=
  (ThetaProductStrictFloor.floor w*ThetaProductStrictFloor.floor w)*
    (ThetaProductStrictFloor.floor w*ThetaProductStrictFloor.floor w)

theorem normalizationFloor_pos {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < normalizationFloor w := by
  have hf := ThetaProductStrictFloor.floor_pos hw0 hw1
  exact Q'.mul_pos (Q'.mul_pos hf hf) (Q'.mul_pos hf hf)

/-- The actual product cost everywhere on the interval is at most its endpoint cost. -/
theorem productRadialCostCReal_le_endpoint {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.leEv (productRadialCostCReal hw0 hw1 hx0 hx1)
      (productRadialCostCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)) := by
  let P := ThetaConvGen.thetaConvCRealGen hw0 hw1 hx0 hx1
  let P1 := ThetaConvGen.thetaConvCRealGen (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)
  let D := productRadialCostCReal hw0 hw1 hx0 hx1
  let D1 := productRadialCostCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)
  let A := alternatingCReal hw0 hw1 hx0 hx1
  let A1 := alternatingCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1)
  let norm := CReal.mul (CReal.mul P1 P1) (CReal.mul P P)
  have hf := ThetaProductStrictFloor.floor_pos hw0 hw1
  have hnorm : ∀ n, normalizationFloor w ≤ norm.approx n := by
    intro n
    have h1 := ThetaProductStrictFloor.floor_le_Ppart (x := 1) hw0 hw1 (by decide) n
    have hx := ThetaProductStrictFloor.floor_le_Ppart hw0 hw1 hx0 n
    have hs1 := HKConv.mul_le_mul' (Q'.le_of_lt hf)
      (Q'.le_trans' _ _ _ (Q'.le_of_lt hf) h1) h1 h1
    have hsx := HKConv.mul_le_mul' (Q'.le_of_lt hf)
      (Q'.le_trans' _ _ _ (Q'.le_of_lt hf) hx) hx hx
    exact HKConv.mul_le_mul' (SumOfSquares.q_mul_self_nonneg _)
      (SumOfSquares.q_mul_self_nonneg _) hs1 hsx
  have hright : ExpPos.geRat
      (CReal.mul (CReal.ofQ' (2*w*(1 + -x)))
        (CReal.mul (CReal.mul A A) (CReal.mul A1 A1))) 0 :=
    CReal.mul_nonneg
      (SumOfSquares.geRat_ofQ'_nonneg (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (Q'.le_of_lt hw0))
        (Q'.sub_nonneg_of_le hx1)))
      (CReal.mul_nonneg (SumOfSquares.geRat_sq_nonneg A) (SumOfSquares.geRat_sq_nonneg A1))
  have hleft := geRat_equiv_transfer
    (ThetaCompletedAdditionSquare.cleared_addition_square hw0 hw1 hx0 hx1) hright
  have hdiff : CReal.Equiv
      (CReal.sub (CReal.mul D1 norm) (CReal.mul D norm))
      (CReal.mul (CReal.mul P1 P1) (CReal.mul (CReal.sub D1 D) (CReal.mul P P))) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 2) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
        (.neg (.mul (.var 3) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))))
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.add (.var 2) (.neg (.var 3))) (.mul (.var 1) (.var 1))))
      (by decide) (fun
        | 0 => P1.approx n
        | 1 => P.approx n
        | 2 => D1.approx n
        | _ => D.approx n)
  exact RCBilinearDifference.cancel_positive_factor (normalizationFloor w)
    (normalizationFloor_pos hw0 hw1) hnorm
    (leEv_of_geRat_sub (geRat_equiv_transfer hdiff hleft))

set_option maxHeartbeats 800000 in
/-- Produced ceiling at every strict nome, uniformly in the scalar coordinate.
The bound depends explicitly on w; no analytic ceiling is supplied as input. -/
theorem productRadialCostCReal_le_cap {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.leRat (productRadialCostCReal hw0 hw1 hx0 hx1) (transverseCap w) := by
  change CReal.leEv (productRadialCostCReal hw0 hw1 hx0 hx1) (CReal.ofQ' (transverseCap w))
  exact CReal.leEv_trans
    (y := productRadialCostCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1))
    (productRadialCostCReal_le_endpoint hw0 hw1 hx0 hx1)
    (JacobiProductRadialEndpoint.productRadialCostCReal_at_one_le_cap hw0 hw1)

/-- The SAME finite cost with its explicit signed tail; the completed ceiling
is produced above, not passed in as an unsupplied hypothesis. -/
theorem productRadialCost_le_cap_add_tail {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) :
    productRadialCost (HKConv.sTerm w x) N x ≤ transverseCap w + radialTailPayment w N :=
  productRadialCost_le_limit_ceiling hw0 hw1 hx0 hx1 (transverseCap w)
    (productRadialCostCReal_le_cap hw0 hw1 hx0 hx1) N hN

/-- Useful nome-defect budget on actual finite costs; NOT a physical mass calibration. -/
theorem productRadialCost_nome_defect_le_three_halves {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) :
    (1 + -w)*productRadialCost (HKConv.sTerm w x) N x ≤ 1 + HalfPow.half := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (1 + -w)
    (productRadialCost_le_cap_add_tail hw0 hw1 hx0 hx1 N hN)
    (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
      (Q'.add_le_add (transverseCap_nome_defect_le_one hw0 hw1)
        (radialTailPayment_nome_defect_le_half hw0 hw1 N hN)))

/-- The produced finite endpoint ceiling passes to its SAME constructed
limit; every actual approximant is bounded, including the empty one. -/
theorem productRadialCostCReal_at_one_le_nearFlatCap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.leRat (productRadialCostCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1))
      (JacobiProductRadialNearFlatBound.nearFlatCap w) :=
  CReal.leRat_of_eventually ⟨0, fun N _ =>
    JacobiProductRadialNearFlatBound.productRadialCost_le_nearFlatCap hw0 hw1
      (by decide) (Q'.le_refl' 1) N⟩

/-- Global sharper bound via the EXISTING completed addition square, not
via hemisphere support, a southern-region premise or a PDE theorem. -/
theorem productRadialCostCReal_le_nearFlatCap {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.leRat (productRadialCostCReal hw0 hw1 hx0 hx1)
      (JacobiProductRadialNearFlatBound.nearFlatCap w) := by
  change CReal.leEv (productRadialCostCReal hw0 hw1 hx0 hx1)
    (CReal.ofQ' (JacobiProductRadialNearFlatBound.nearFlatCap w))
  exact CReal.leEv_trans
    (y := productRadialCostCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1))
    (productRadialCostCReal_le_endpoint hw0 hw1 hx0 hx1)
    (productRadialCostCReal_at_one_le_nearFlatCap hw0 hw1)

/-- Actual finite cost globally, with its signed-tail payment retained.
The nome and cutoff dependence are explicit; no original-action gap follows. -/
theorem productRadialCost_le_nearFlatCap_add_tail {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) :
    productRadialCost (HKConv.sTerm w x) N x ≤
      JacobiProductRadialNearFlatBound.nearFlatCap w + radialTailPayment w N :=
  productRadialCost_le_limit_ceiling hw0 hw1 hx0 hx1
    (JacobiProductRadialNearFlatBound.nearFlatCap w)
    (productRadialCostCReal_le_nearFlatCap hw0 hw1 hx0 hx1) N hN

end YMGap.Continuum.ThetaProductRadialCeiling

#print axioms YMGap.Continuum.ThetaProductRadialCeiling.normalizationFloor
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.normalizationFloor_pos
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.productRadialCostCReal_le_endpoint
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.productRadialCostCReal_le_cap
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.productRadialCost_le_cap_add_tail
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.productRadialCost_nome_defect_le_three_halves
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.productRadialCostCReal_at_one_le_nearFlatCap
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.productRadialCostCReal_le_nearFlatCap
#print axioms YMGap.Continuum.ThetaProductRadialCeiling.productRadialCost_le_nearFlatCap_add_tail
