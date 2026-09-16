/-
# Covariance normalization with one unchanged positive partition

A determinant estimate relative to Z squared gives the connected normalized
correlation with the SAME reciprocal in its joint and marginal terms. Only
Z is inverted; all three insertions may be signed or zero. This is rational
algebra, not a claim that any physical covariance estimate is available.
-/

import YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison

namespace YMGap.Continuum.RationalCommonPartitionCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Cancel the one actual partition twice, without a reciprocal ceiling or
a sign assumption on the joint or marginal numerators. -/
theorem covariance_bound (A B C Z E : Q') (hZ : (0 : Q') < Z)
    (h : Q'.abs (A*Z + -(B*C)) ≤ E*(Z*Z)) :
    Q'.abs (A*Q'.recipPos Z hZ +
      -((B*Q'.recipPos Z hZ)*(C*Q'.recipPos Z hZ))) ≤ E := by
  let r := Q'.recipPos Z hZ
  have hc : ((B*r)*C)*Z ≈ B*C :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 3)) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => B | 1 => C | 2 => Z | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv _))
  have hn := BF4ExactSlabFaceSetBoundaryComparison.ratio_difference_bound
    A ((B*r)*C) Z Z E hZ hZ
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hc)))) h)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_assoc_eqv (B*r) C r))))) hn

end YMGap.Continuum.RationalCommonPartitionCovariance

#print axioms YMGap.Continuum.RationalCommonPartitionCovariance.covariance_bound
