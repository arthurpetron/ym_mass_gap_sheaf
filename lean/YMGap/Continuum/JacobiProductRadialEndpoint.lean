/-
# Constructed endpoint ceiling for the actual signed radial cost

At x=1 the radial cost is exactly the first factor moment. Every actual
sTerm is at most 2*c_i because its denominator is at least one. The existing
geometric transverse ceiling therefore bounds both the finite endpoint cost
and its SAME constructed CReal limit, without a density-floor reciprocal.

This supplies the endpoint side of the proposed addition-square argument.
It does NOT prove that the cost at other x is at most the endpoint cost;
the completed convolution and its derivative pins remain required.
-/

import YMGap.Continuum.JacobiProductRadialLimit
import YMGap.Continuum.JacobiHeatTransverseCurvature

namespace YMGap.Continuum.JacobiProductRadialEndpoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation
open YMGap.Continuum.JacobiProductRadialLimit
open YMGap.Continuum.JacobiHeatTransverseCurvature

local infix:50 " ≈ " => Q'.eqv

/-- No endpoint jet or normalization is replaced: D_N(1)=sum_i r_i(1). -/
theorem productRadialCost_at_one_pin (w : Q') (N : Nat) :
    productRadialCost (HKConv.sTerm w 1) N 1 ≈ M1 (HKConv.sTerm w 1) N :=
  poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.neg (.mul (.const 1) (.const 1)))) (.var 0))
      (.mul (.const 1) (.var 1)))
    (.var 1) (by decide)
    (fun | 0 => M2 (HKConv.sTerm w 1) N | _ => M1 (HKConv.sTerm w 1) N)

/-- Each ACTUAL endpoint logarithmic factor ratio is paid by 2*c_i. -/
theorem endpoint_sTerm_le_rate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (i : Nat) :
    HKConv.sTerm w 1 i ≤ transverseRate w i := by
  let c := HKPos.geoAmp w i
  have hc : (0 : Q') ≤ c := Q'.pow_nonneg w (Q'.le_of_lt hw0) (2*i+1)
  have ht : (0 : Q') ≤ HKPos.two c := Q'.zero_le_add _ _ hc hc
  have hf : (1 : Q') ≤ HKPos.factor c 1 :=
    Q'.add_le_self_of_nonneg 1 _ (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ ht Q'.zero_le_one) (Q'.mul_nonneg _ _ hc hc))
  apply HKConv.divPos_le_of_le (HKConv.factor_num_pos hw0 hw1 (by decide) i)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (HKPos.two c)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hf ht)

/-- Every finite endpoint cost has the useful inverse-linear nome ceiling. -/
theorem productRadialCost_at_one_le_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    productRadialCost (HKConv.sTerm w 1) N 1 ≤ transverseCap w :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (productRadialCost_at_one_pin w N))
    (Q'.le_trans' _ _ _
      (finSum_le_lt (HKConv.sTerm w 1) (transverseRate w) N
        (fun i _ => endpoint_sTerm_le_rate hw0 hw1 i))
      (transversePrefixCost_le_cap hw0 hw1 N))

/-- This is a produced ceiling on the SAME actual endpoint limit, not an
addition identity or a whole-interval curvature ceiling supplied as input. -/
theorem productRadialCostCReal_at_one_le_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.leRat (productRadialCostCReal (x := 1) hw0 hw1 (by decide) (Q'.le_refl' 1))
      (transverseCap w) :=
  CReal.leRat_of_eventually ⟨0, fun N _ => productRadialCost_at_one_le_cap hw0 hw1 N⟩

end YMGap.Continuum.JacobiProductRadialEndpoint

#print axioms YMGap.Continuum.JacobiProductRadialEndpoint.productRadialCost_at_one_pin
#print axioms YMGap.Continuum.JacobiProductRadialEndpoint.endpoint_sTerm_le_rate
#print axioms YMGap.Continuum.JacobiProductRadialEndpoint.productRadialCost_at_one_le_cap
#print axioms YMGap.Continuum.JacobiProductRadialEndpoint.productRadialCostCReal_at_one_le_cap
