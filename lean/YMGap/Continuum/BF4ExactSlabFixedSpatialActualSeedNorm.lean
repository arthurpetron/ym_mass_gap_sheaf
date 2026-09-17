/-
# Finite-degree norm control for the ACTUAL weighted residual seeds

For the original nu and its constructed lower window ell, every finite
inverse degree satisfies ell*H[nu*q_i^2] <= H[tau^2]. Weighted conditional
centering contracts the integrated norm; the inverse multiplier is bounded
by one by its existing square certificate. No exact inverse, conditional
centering of tau, or weighted orthogonality of different tests is assumed.

The lower window retains nome, cutoff, width and depth. This is not a
regulator-uniform cost estimate or a spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
import YMGap.Continuum.SU2QuaternionWeightedResidualNorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported marginalCertificate marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionWeightedResidualNorm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_sub (blocks : Nat) (p q : RatPoly) :
    quaternionHaar blocks (polyAdd p (polyNeg q)) ≈ quaternionHaar blocks p + -(quaternionHaar blocks q) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append blocks p (polyNeg q))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks q))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- Sharp multiplier control for the inverse used by the actual seed code. -/
def inverseMultiplierCertificate (i : Nat) (hi : i < N width) (k : Nat) :
    Certificate (N width) (polyAdd polyOne (polyNeg (polyMul
      (polyMul (denominator w K width n i) (inverse hw0 hw1 K width hK n i k))
      (polyMul (denominator w K width n i) (inverse hw0 hw1 K width hK n i k))))) := by
  have hl := lower_positive hw0 hw1 K width hK n
  have hu := upper_positive hw0 hw1 K width hK n
  have hle : lower w K width n * lower w K width n ≤
      upper w K width n * upper w K width n :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (lower_le_upper w K width n) (Q'.le_of_lt hl))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (lower_le_upper w K width n) (Q'.le_of_lt hu))
  exact QuaternionHaarPositiveWindowInverse.multiplierSquareCertificate
    (denominator_supported w K width n i) (Q'.mul_pos hl hl) (Q'.mul_pos hu hu) hle
    (denominatorLowerCertificate hw0 hw1 K width hK n i hi)
    (denominatorUpperCertificate hw0 hw1 K width hK n i hi) k

/-- Pointwise certificate only for the UNCENTERED scaled seed. The later
centering contraction is an integrated inequality, not a pointwise claim. -/
def scaledSeedCertificate (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    Certificate (N width) (polyAdd (polyMul tau tau) (polyNeg
      (polySmul (lower w K width n) (polyMul (marginalWeight w K width n)
        (polyMul
          (polyMul (project i (marginalWeight w K width n)) (seed hw0 hw1 K width hK n i k tau))
          (polyMul (project i (marginalWeight w K width n)) (seed hw0 hw1 K width hK n i k tau))))))) := by
  let a := marginalWeight w K width n
  let m := project i a
  let J := inverse hw0 hw1 K width hK n i k
  let ell := lower w K width n
  let z := polyMul m (polyMul J tau)
  have hz : SupportedQuaternionBlocks (N width) z :=
    supported_polyMul (project_supported i (marginalWeight_supported w K width n))
      (seed_supported hw0 hw1 K width hK n i k ht)
  have C := ((inverseMultiplierCertificate hw0 hw1 K width hK n i hi k).mul
    (.square tau ht)).add
      (((marginalCertificate hw0 hw1 K width hK n).mul
        (lowerCertificate hw0 hw1 K width hK n)).mul (.square z hz))
  refine .ofCoeff (((RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.neg (cap_mul_left ell _).symm)).trans ?_) C
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 0)
      (.mul (.mul (.var 1) (.mul (.var 2) (.var 3)))
        (.mul (.var 1) (.mul (.var 2) (.var 3))))))))
    (.add
      (.mul (.add (.const 1) (.neg (.mul
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 1)) (.var 2))))) (.mul (.var 3) (.var 3)))
      (.mul (.mul (.var 0) (.add (.var 0) (.neg (.var 4))))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 3)))
          (.mul (.var 1) (.mul (.var 2) (.var 3))))))
    (by decide) (fun | 0 => a | 1 => m | 2 => J | 3 => tau | _ => cap ell)

/-- Degree-independent bound on the actual exactly centered polynomial test.
No condition P_i(tau)=0 is needed for this estimate. -/
theorem test_norm_le (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    lower w K width n * marginalPair w K width n
      (test hw0 hw1 K width hK n i k tau) (test hw0 hw1 K width hK n i k tau) ≤
      quaternionHaar (N width) (polyMul tau tau) := by
  have hcenter := weightedResidual_square_le (N width) i hi
    (marginalWeight_supported w K width n)
    (seed_supported hw0 hw1 K width hK n i k ht)
    (marginalCertificate hw0 hw1 K width hK n)
  have hscaled := (scaledSeedCertificate hw0 hw1 K width hK n i hi k ht).haar_nonnegative
  have hcap := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (haar_sub (N width) _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ (quaternionHaar_polySmul _ _ _))))))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcenter
      (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n))) hcap

end YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm.inverseMultiplierCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm.scaledSeedCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm.test_norm_le
