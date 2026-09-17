/-
# Retain the reciprocal-weighted source in the actual finite seed norm

For the original nu, M=P_i nu, the actual polynomial inverse J, and
q=M*(J*tau)-P_i(nu*J*tau), weighted conditional Pythagoras gives
  H[nu*q^2] <= H[(M*J)*tau^2].
The comparison uses the certified nonnegative factors M, J and 1-nu*M*J.
No exact inverse or global lower-density loss enters this first inequality.

The retained budget also satisfies ell*H[(M*J)*tau^2] <= H[tau^2],
so it refines the existing finite-window bound. J and ell retain all
original regulators. This does not prove a uniform family cost, a bound
after discarding fringe tests, or a physical spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedNorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm

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
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate (project_certificate)
open YMGap.Continuum.SU2QuaternionWeightedResidualNorm
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (corrector residual)
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse (residualCertificate)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private def correctorCertificate {blocks : Nat} {R : RatPoly}
    (C : Certificate blocks (polyNeg R)) : (k : Nat) → Certificate blocks (corrector R k)
  | 0 => .ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (.constant blocks 0 (by decide))
  | k+1 => (Certificate.one blocks).add (C.mul (correctorCertificate C k))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_le {blocks : Nat} {p q : RatPoly}
    (C : Certificate blocks (polyAdd p (polyNeg q))) :
    quaternionHaar blocks q ≤ quaternionHaar blocks p :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ C.haar_nonnegative (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks q)))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

include hw0 hw1 hK in
private theorem upperSquare_positive : (0 : Q') < upper w K width n * upper w K width n :=
  Q'.mul_pos (upper_positive hw0 hw1 K width hK n) (upper_positive hw0 hw1 K width hK n)

/-- Positivity of the actual finite inverse polynomial, by its geometric sum. -/
def inverseCertificate (i : Nat) (hi : i < N width) (k : Nat) :
    Certificate (N width) (inverse hw0 hw1 K width hK n i k) := by
  let u := upper w K width n * upper w K width n
  let hu := upperSquare_positive hw0 hw1 K width hK n
  have C := QuaternionHaarPositiveWindowInverse.remainderNegative hu
    (denominatorUpperCertificate hw0 hw1 K width hK n i hi)
  change Certificate (N width)
    (polySmul (QuaternionHaarPositiveWindowInverse.scale u hu)
      (corrector (QuaternionHaarPositiveWindowInverse.remainder (denominator w K width n i) u hu) k))
  exact .smul _ (Q'.le_of_lt (QuaternionHaarPositiveWindowInverse.scale_positive u hu))
    (correctorCertificate C k)

/-- The actual multiplier lies below one, with a nonnegative polynomial residue. -/
def inverseResidualCertificate (i : Nat) (hi : i < N width) (k : Nat) :
    Certificate (N width) (inverseError hw0 hw1 K width hK n i k) := by
  let u := upper w K width n * upper w K width n
  let hu := upperSquare_positive hw0 hw1 K width hK n
  let B := denominator w K width n i
  let J := inverse hw0 hw1 K width hK n i k
  let R := QuaternionHaarPositiveWindowInverse.remainder B u hu
  have C := residualCertificate (QuaternionHaarPositiveWindowInverse.remainderNegative hu
    (denominatorUpperCertificate hw0 hw1 K width hK n i hi)) k
  have he : RatPolyCoeffEqv (inverseError hw0 hw1 K width hK n i k) (residual R k) :=
    (((QuaternionHaarPositiveWindowInverse.reciprocal_cancellation B u hu k).symm.add
      (RatPolyCoeffEqv.refl (polyNeg (polyMul B J))))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1) (by decide)
        (fun | 0 => polyMul B J | _ => residual R k))
  exact .ofCoeff he C

/-- The retained reciprocal-source budget is a nonnegative original polynomial. -/
def reciprocalSourceCertificate (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    Certificate (N width) (polyMul
      (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
      (polyMul tau tau)) :=
  ((project_certificate (N width) i hi (marginalWeight_supported w K width n)
    (marginalCertificate hw0 hw1 K width hK n)).mul
      (inverseCertificate hw0 hw1 K width hK n i hi k)).mul (.square tau ht)

/-- No global ell is lost: retain the actual finite reciprocal-weighted source.
Only conditional Pythagoras is integrated; no pointwise centered-norm claim is made. -/
theorem test_norm_le_reciprocal_source (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    marginalPair w K width n (test hw0 hw1 K width hK n i k tau)
      (test hw0 hw1 K width hK n i k tau) ≤
      quaternionHaar (N width) (polyMul
        (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
        (polyMul tau tau)) := by
  let a := marginalWeight w K width n
  let m := project i a
  let J := inverse hw0 hw1 K width hK n i k
  have M := project_certificate (N width) i hi (marginalWeight_supported w K width n)
    (marginalCertificate hw0 hw1 K width hK n)
  have C := (((M.mul (inverseCertificate hw0 hw1 K width hK n i hi k)).mul
    (inverseResidualCertificate hw0 hw1 K width hK n i hi k)).mul (.square tau ht))
  have P : Certificate (N width) (polyAdd
      (polyMul (polyMul m J) (polyMul tau tau))
      (polyNeg (polyMul a (polyMul (polyMul m (polyMul J tau)) (polyMul m (polyMul J tau)))))) :=
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 3)))
        (.neg (.mul (.var 0) (.mul (.mul (.var 1) (.mul (.var 2) (.var 3)))
          (.mul (.var 1) (.mul (.var 2) (.var 3)))))))
      (.mul (.mul (.mul (.var 1) (.var 2))
        (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))))
        (.mul (.var 3) (.var 3))) (by decide)
      (fun | 0 => a | 1 => m | 2 => J | _ => tau)) C
  exact Q'.le_trans' _ _ _ (weightedResidual_square_le (N width) i hi
    (marginalWeight_supported w K width n) (seed_supported hw0 hw1 K width hK n i k ht)
    (marginalCertificate hw0 hw1 K width hK n)) (haar_le P)

/-- The retained budget is no worse than the old explicit ell-scaled source square. -/
theorem reciprocal_source_le_scaled_square (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau) :
    lower w K width n * quaternionHaar (N width) (polyMul
      (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
      (polyMul tau tau)) ≤ quaternionHaar (N width) (polyMul tau tau) := by
  let a := marginalWeight w K width n
  let m := project i a
  let J := inverse hw0 hw1 K width hK n i k
  let ell := lower w K width n
  let s := polyMul (polyMul m J) (polyMul tau tau)
  have M := project_certificate (N width) i hi (marginalWeight_supported w K width n)
    (marginalCertificate hw0 hw1 K width hK n)
  have C := ((inverseResidualCertificate hw0 hw1 K width hK n i hi k).add
    ((lowerCertificate hw0 hw1 K width hK n).mul
      (M.mul (inverseCertificate hw0 hw1 K width hK n i hi k)))).mul (.square tau ht)
  have P : Certificate (N width) (polyAdd (polyMul tau tau) (polyNeg (polySmul ell s))) :=
    .ofCoeff (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left ell s).symm)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 3) (.var 3))
          (.neg (.mul (.var 4) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 3))))))
        (.mul
          (.add (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
            (.mul (.add (.var 0) (.neg (.var 4))) (.mul (.var 1) (.var 2))))
          (.mul (.var 3) (.var 3))) (by decide)
        (fun | 0 => a | 1 => m | 2 => J | 3 => tau | _ => cap ell))) C
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (quaternionHaar_polySmul (N width) ell s)) (haar_le P)

end YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm.inverseCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm.inverseResidualCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm.reciprocalSourceCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm.test_norm_le_reciprocal_source
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm.reciprocal_source_le_scaled_square
