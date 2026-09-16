/-
# Rational coefficient changes in the SAME union squared distance

The literal difference of two scalar multiples is tested against the
original union pairing. Its proved rational bilinearity gives the exact
coefficient-square factor without selecting a common support for a stream.

The existing computed coefficientTolerance then spends epsilon/4 on a
coefficient change at a vector with supplied squared-norm ceiling. This
is the dense estimate consumed by the real-scalar Cauchy construction;
it does not itself assert a completed real-scalar action or continuum result.
-/

import YMGap.Continuum.BF4SpatialUnionLinear
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.BF4SpatialUnionScalarDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionPairingData (pairing_symm)
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (coefficientTolerance coefficientTolerance_pos coefficientTolerance_budget)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A)
    (ha : Q'.abs a ≤ A) : a*a ≤ A*A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "d" => distSq hw0 hw1 hsmall hd hs

private theorem scalar_difference_pairing (a b : Q') (x y : Stage) :
    Equiv (P (difference (smulStage a x) (smulStage b x)) y)
      (mul (ofQ' (a + -b)) (P x y)) := by
  have h := pairing_add_left hw0 hw1 hsmall hd hs (smulStage a x)
    (smulStage (-1) (smulStage b x)) y
  have hscaled := Equiv_add (pairing_smul_left hw0 hw1 hsmall hd hs a x y)
    ((pairing_smul_left hw0 hw1 hsmall hd hs (-1) (smulStage b x) y).trans
      (TrigSignedAdd.mul_congr_right (pairing_smul_left hw0 hw1 hsmall hd hs b x y)))
  exact h.trans (hscaled.trans (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.mul (.const (-1)) (.mul (.var 1) (.var 2))))
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (by decide) (fun | 0 => a | 1 => b | _ => (P x y).approx n))))

/-- Both sides refer to the original union distance and original union pairing. -/
theorem distSq_scalar_difference (a b : Q') (x : Stage) :
    Equiv (d (smulStage a x) (smulStage b x))
      (mul (ofQ' ((a + -b)*(a + -b))) (P x x)) := by
  let v := difference (smulStage a x) (smulStage b x)
  have hleft := scalar_difference_pairing hw0 hw1 hsmall hd hs a b x v
  have hright := (pairing_symm hw0 hw1 hsmall hd hs x v).trans
    (scalar_difference_pairing hw0 hw1 hsmall hd hs a b x x)
  exact (distance_difference hw0 hw1 hsmall hd hs (smulStage a x) (smulStage b x)).trans
    (hleft.trans ((TrigSignedAdd.mul_congr_right hright).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.eqv_symm (Q'.mul_assoc_eqv (a + -b) (a + -b) ((P x x).approx n))))))

/-- The existing explicit coefficient tolerance controls the squared error. -/
theorem scalar_change_bound (a b B epsilon : Q') (hB : (0 : Q') ≤ B)
    (he : (0 : Q') < epsilon) (x : Stage) (hnorm : leEv (P x x) (ofQ' B))
    (hab : a ≤ b + coefficientTolerance B hB epsilon ∧
      b ≤ a + coefficientTolerance B hB epsilon) :
    leEv (d (smulStage a x) (smulStage b x)) (ofQ' (quarter epsilon)) := by
  let delta := coefficientTolerance B hB epsilon
  have hdelta := Q'.le_of_lt (coefficientTolerance_pos B hB he)
  have habs : Q'.abs (a + -b) ≤ delta :=
    Q'.abs_le (Q'.neg_le_sub_of_le_add hab.2) (Q'.sub_le_of_le_add hab.1)
  have hsquare := square_le_of_abs_le hdelta habs
  have hfactor : leEv czero (ofQ' ((a + -b)*(a + -b))) :=
    leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg (a + -b))
  exact leEv_trans (leEv_of_equiv (distSq_scalar_difference hw0 hw1 hsmall hd hs a b x))
    (leEv_trans (leEv_mul_nonneg_left hfactor hnorm)
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare hB)
        (coefficientTolerance_budget B hB he))))

end YMGap.Continuum.BF4SpatialUnionScalarDistance

#print axioms YMGap.Continuum.BF4SpatialUnionScalarDistance.distSq_scalar_difference
#print axioms YMGap.Continuum.BF4SpatialUnionScalarDistance.scalar_change_bound
