/-
# Two-coupling stability of an ORIGINAL normalized expectation

Change one face nome u to v, retaining the entire positive shared-link
background. The heat-variation interval and the later face's retained-head
floor give relative mass/moment bounds. Cancel both actual partition factors
only after bounding the signed determinant.

The explicit Lipschitz cap is independent of cutoff and background volume,
for 0<u<=v<=W<1 and cutoffs beyond BOTH positive-head thresholds.
It is not uniform as W approaches one. Telescoping over all faces still
costs their number without a summable spatial response estimate. This theorem
does not construct cross-scale OS identifications or continuum survival.
-/
import YMGap.Continuum.BF4ExactSlabCouplingVariationInterval
import YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability

namespace YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison (ratio_difference_bound)
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.BF4ExactSlabCouplingVariationInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

def relativeVariation (W u v : Q') : Q' := HKConv.divPos (variationCap W u v) (headFloor v)

theorem relativeVariation_nonnegative {W : Q'} (hW0 : (0 : Q') < W) (u v : Q') :
    (0 : Q') ≤ relativeVariation W u v := HKConv.divPos_nonneg (variationCap_nonnegative hW0 u v)

theorem relativeVariation_floor {W u v : Q'} (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) :
    relativeVariation W u v * headFloor v ≈ variationCap W u v :=
  HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (headFloor_positive hv0 hv1))

private theorem insertion_difference (u v : Q') (K extent id : Nat) (p : RatPoly) :
    quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial v K extent id)) +
      -(quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial u K extent id))) ≈
    quaternionHaar (blocks extent) (polyMul p (faceDifference u v K extent id)) := by
  have h := Q'.eqv_trans _ _ _ (haar_of_coeff ((faceDifference_pin u v K extent id).mul_left p))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right p _ _))
      (quaternionHaar_append (blocks extent) _ _))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun
        | 0 => quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial u K extent id))
        | _ => quaternionHaar (blocks extent) (polyMul p (faceDifference u v K extent id))))

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))

include hu0 huv in
private theorem v_pos : (0 : Q') < v := Q'.pos_of_lt_of_le hu0 huv
include hvW hW1 in
private theorem v_lt_one : v < (1 : Q') := Q'.lt_of_le_of_lt hvW hW1
include huv hvW hW1 in
private theorem u_lt_one : u < (1 : Q') := Q'.lt_of_le_of_lt huv (v_lt_one hvW hW1)
include hu0 huv hvW in
private theorem W_pos : (0 : Q') < W := Q'.pos_of_lt_of_le (v_pos hu0 huv) hvW

variable (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
  (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
  {B : RatPoly} (H : Certificate (blocks extent) B)

include hu0 huv hvW hW1 hi in
def relativeDifferenceInterval :
    Interval (blocks extent) (faceDifference u v K extent id) (relativeVariation W u v*headFloor v) :=
  (faceDifferenceInterval (Q'.le_of_lt hu0) huv hvW (W_pos hu0 huv hvW) hW1 K extent id hi).changeCap
    (Q'.eqv_symm (relativeVariation_floor (v_pos hu0 huv) (v_lt_one hvW hW1)))

include hu0 huv hvW hW1 hi hKv H in
theorem mass_difference_bound :
    Q'.abs (faceMass v K extent id B + -(faceMass u K extent id B)) ≤
      relativeVariation W u v * faceMass v K extent id B := by
  have R := relativeDifferenceInterval hu0 huv hvW hW1 K extent id hi
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (insertion_difference u v K extent id B)))
    (Q'.le_trans' _ _ _ (R.weighted_haar_bound H)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (faceHead_weighted_floor (v_pos hu0 huv) (v_lt_one hvW hW1) K extent id hi hKv H)
          (relativeVariation_nonnegative (W_pos hu0 huv hvW) u v))))

include hu0 huv hvW hW1 hi hKv H in
theorem moment_difference_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment v K extent id B p + -(faceMoment u K extent id B p)) ≤
      (c*relativeVariation W u v) * faceMass v K extent id B := by
  have R := relativeDifferenceInterval hu0 huv hvW hW1 K extent id hi
  have hp := @haar_of_coeff (blocks extent) _ _ (((RatPolyCoeffEqv.mul_comm p B).mul_right
    (faceDifference u v K extent id)).trans (RatPolyCoeffEqv.mul_assoc B p _))
  have hb := (P.mul R).weighted_haar_bound H
  have hc : (0 : Q') ≤ c*relativeVariation W u v := Q'.mul_nonneg _ _ P.nonnegative
    (relativeVariation_nonnegative (W_pos hu0 huv hvW) u v)
  have horder : (c*(relativeVariation W u v*headFloor v))*quaternionHaar (blocks extent) B ≈
      (c*relativeVariation W u v)*(headFloor v*quaternionHaar (blocks extent) B) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_trans _ _ _ (insertion_difference u v K extent id (polyMul p B)) hp)))
    (Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder)
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (faceHead_weighted_floor (v_pos hu0 huv) (v_lt_one hvW hW1) K extent id hi hKv H) hc)))

include hu0 huv hvW hW1 hi hKu H in
theorem old_moment_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment u K extent id B p) ≤ c*faceMass u K extent id B := by
  have hp := @haar_of_coeff (blocks extent) _ _ ((RatPolyCoeffEqv.mul_assoc p B (faceHeatPolynomial u K extent id)).trans
    (RatPolyCoeffEqv.mul_comm p (polyMul B (faceHeatPolynomial u K extent id))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp))
    (P.weighted_haar_bound (H.mul (faceHead_certificate hu0 (u_lt_one huv hvW hW1) K extent id hi hKu)))

include hu0 huv hvW hW1 hi hKu hKv H in
theorem determinant_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment v K extent id B p * faceMass u K extent id B +
      -(faceMoment u K extent id B p * faceMass v K extent id B)) ≤
      (2*c*relativeVariation W u v)*(faceMass v K extent id B * faceMass u K extent id B) :=
  RationalRelativePerturbation.relative_determinant_bound _ _ _ _ c (relativeVariation W u v)
    P.nonnegative (relativeVariation_nonnegative (W_pos hu0 huv hvW) u v)
    (H.mul (faceHead_certificate hu0 (u_lt_one huv hvW hW1) K extent id hi hKu)).haar_nonnegative
    (H.mul (faceHead_certificate (v_pos hu0 huv) (v_lt_one hvW hW1) K extent id hi hKv)).haar_nonnegative
    (old_moment_bound hu0 huv hvW hW1 K extent id hi hKu H P)
    (moment_difference_bound hu0 huv hvW hW1 K extent id hi hKv H P)
    (mass_difference_bound hu0 huv hvW hW1 K extent id hi hKv H)

include hu0 huv hvW hW1 hi hKu hKv H in
/-- Both actual positive partitions cancel. The bound names no cutoff or volume. -/
theorem normalized_difference_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c)
    (hB : (0 : Q') < quaternionHaar (blocks extent) B) :
    Q'.abs
      (faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B)
          (faceMass_positive (v_pos hu0 huv) (v_lt_one hvW hW1) extent id hi H K hKv hB) +
       -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B)
          (faceMass_positive hu0 (u_lt_one huv hvW hW1) extent id hi H K hKu hB))) ≤
      2*c*relativeVariation W u v :=
  ratio_difference_bound _ _ _ _ _ _ _
    (determinant_bound hu0 huv hvW hW1 K extent id hi hKu hKv H P)

include hu0 huv hvW hW1 hi hKu hKv in
/-- Actual spectator heat product, at its OWN nome w and cutoff J. Shared
links are never factored, and background positivity is constructed. -/
theorem original_background_normalized {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (J : Nat) (hJ : headCutoff w ≤ J) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    let B := polynomialProduct (faceHeatPolynomial w J extent) ids
    let HB := headProduct_certificate hw0 hw1 J extent hJ ids hids
    let hB : (0 : Q') < quaternionHaar (blocks extent) B :=
      Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
        (partition_floor hw0 hw1 extent ids hids J hJ)
    Q'.abs
      (faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B)
          (faceMass_positive (v_pos hu0 huv) (v_lt_one hvW hW1) extent id hi HB K hKv hB) +
       -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B)
          (faceMass_positive hu0 (u_lt_one huv hvW hW1) extent id hi HB K hKu hB))) ≤
      2*c*relativeVariation W u v :=
  normalized_difference_bound hu0 huv hvW hW1 K extent id hi hKu hKv
    (headProduct_certificate hw0 hw1 J extent hJ ids hids) P
    (Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partition_floor hw0 hw1 extent ids hids J hJ))

end YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability

#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.relativeVariation
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.relativeVariation_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.relativeVariation_floor
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.relativeDifferenceInterval
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.mass_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.moment_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.old_moment_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.determinant_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.normalized_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability.original_background_normalized
