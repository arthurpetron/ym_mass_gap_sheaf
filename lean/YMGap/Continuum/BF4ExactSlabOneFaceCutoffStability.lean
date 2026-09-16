/-
# Volume-independent normalized change of ONE original face cutoff

The whole positive background B remains fixed, with all its shared links.
Only one actual heat prefix changes from K to K+L. Its high-spin tail has
absolute cap eta*headFloor(w); the same positive floor holds at BOTH
endpoints. Bound the changed moments relative to the later partition and
the old moment relative to the old partition before canceling their product.
The resulting normalized error is at most 2*c*eta, with no inverse-floor
or volume factor. No eta<1 guard is needed.

This controls one local representation truncation, not spatial separation.
The retained interacting head's connected covariance is not discarded.
Finite telescoping would incur a face-count factor. Volume-independent control
of arbitrarily many changed faces still needs a summable spatial response estimate.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
import YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison
import YMGap.Continuum.RationalRelativePerturbation

namespace YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison (ratio_difference_bound)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

def faceMass (w : Q') (K extent id : Nat) (B : RatPoly) : Q' :=
  quaternionHaar (blocks extent) (polyMul B (faceHeatPolynomial w K extent id))

def faceMoment (w : Q') (K extent id : Nat) (B p : RatPoly) : Q' :=
  quaternionHaar (blocks extent) (polyMul (polyMul p B) (faceHeatPolynomial w K extent id))

private theorem insertion_difference (w : Q') (K L extent id : Nat) (p : RatPoly) :
    quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w (K+L) extent id)) +
      -(quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id))) ≈
    quaternionHaar (blocks extent) (polyMul p (faceHeatTail w extent id (K+1) L)) := by
  rw [faceHeatPolynomial_cutoff_append]
  have h := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right p
    (faceHeatPolynomial w K extent id) (faceHeatTail w extent id (K+1) L)))
    (quaternionHaar_append (blocks extent) _ _)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun
        | 0 => quaternionHaar (blocks extent) (polyMul p (faceHeatPolynomial w K extent id))
        | _ => quaternionHaar (blocks extent) (polyMul p (faceHeatTail w extent id (K+1) L))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (eta : Q') (he : (0 : Q') < eta) (K L extent id : Nat)
  (hi : id ∈ slabPhysicalFaceEdges extent) (hK : relativeCutoff w eta ≤ K)
  {B : RatPoly} (H : Certificate (blocks extent) B)

include hK in
private theorem late_head : headCutoff w ≤ K+L :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hK) (Nat.le_add_right _ _)

include hw0 hw1 he hi hK H

/-- The SAME absolute tail is paid by the LATER original partition. -/
theorem mass_difference_bound :
    Q'.abs (faceMass w (K+L) extent id B + -(faceMass w K extent id B)) ≤
      eta * faceMass w (K+L) extent id B := by
  have ht := Nat.le_trans (Nat.le_max_right _ _) hK
  have R := faceTailInterval hw0 hw1 extent id hi (eta*headFloor w)
    (Q'.mul_pos he (headFloor_positive hw0 hw1)) K L ht
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (insertion_difference w K L extent id B)))
    (Q'.le_trans' _ _ _ (R.weighted_haar_bound H)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (faceHead_weighted_floor hw0 hw1 (K+L) extent id hi (late_head eta K L hK) H) (Q'.le_of_lt he))))

theorem moment_difference_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment w (K+L) extent id B p + -(faceMoment w K extent id B p)) ≤
      (c*eta) * faceMass w (K+L) extent id B := by
  have ht := Nat.le_trans (Nat.le_max_right _ _) hK
  have R := faceTailInterval hw0 hw1 extent id hi (eta*headFloor w)
    (Q'.mul_pos he (headFloor_positive hw0 hw1)) K L ht
  have hp := @haar_of_coeff (blocks extent) _ _ (((RatPolyCoeffEqv.mul_comm p B).mul_right
    (faceHeatTail w extent id (K+1) L)).trans (RatPolyCoeffEqv.mul_assoc B p _))
  have hb := (P.mul R).weighted_haar_bound H
  have hc : (0 : Q') ≤ c*eta := Q'.mul_nonneg _ _ P.nonnegative (Q'.le_of_lt he)
  have horder : (c*(eta*headFloor w))*quaternionHaar (blocks extent) B ≈
      (c*eta)*(headFloor w*quaternionHaar (blocks extent) B) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_trans _ _ _ (insertion_difference w K L extent id (polyMul p B)) hp)))
    (Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder)
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (faceHead_weighted_floor hw0 hw1 (K+L) extent id hi (late_head eta K L hK) H) hc)))

omit he in
theorem old_moment_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment w K extent id B p) ≤ c*faceMass w K extent id B := by
  have hp := @haar_of_coeff (blocks extent) _ _ ((RatPolyCoeffEqv.mul_assoc p B (faceHeatPolynomial w K extent id)).trans
    (RatPolyCoeffEqv.mul_comm p (polyMul B (faceHeatPolynomial w K extent id))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp))
    (P.weighted_haar_bound (H.mul (faceHead_certificate hw0 hw1 K extent id hi
      (Nat.le_trans (Nat.le_max_left _ _) hK))))

/-- Both DIFFERENT partitions remain, before division. No spatial decay is inferred. -/
theorem determinant_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (faceMoment w (K+L) extent id B p * faceMass w K extent id B +
      -(faceMoment w K extent id B p * faceMass w (K+L) extent id B)) ≤
      (2*c*eta)*(faceMass w (K+L) extent id B * faceMass w K extent id B) :=
  RationalRelativePerturbation.relative_determinant_bound _ _ _ _ c eta
    P.nonnegative (Q'.le_of_lt he)
    (H.mul (faceHead_certificate hw0 hw1 K extent id hi (Nat.le_trans (Nat.le_max_left _ _) hK))).haar_nonnegative
    (H.mul (faceHead_certificate hw0 hw1 (K+L) extent id hi (late_head eta K L hK))).haar_nonnegative
    (old_moment_bound hw0 hw1 eta K extent id hi hK H P)
    (moment_difference_bound hw0 hw1 eta he K L extent id hi hK H P)
    (mass_difference_bound hw0 hw1 eta he K L extent id hi hK H)

omit eta he K L hK in
theorem faceMass_positive (J : Nat) (hJ : headCutoff w ≤ J)
    (hB : (0 : Q') < quaternionHaar (blocks extent) B) : (0 : Q') < faceMass w J extent id B :=
  Q'.pos_of_lt_of_le (Q'.mul_pos (headFloor_positive hw0 hw1) hB)
    (faceHead_weighted_floor hw0 hw1 J extent id hi hJ H)

theorem normalized_difference_bound {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c)
    (hB : (0 : Q') < quaternionHaar (blocks extent) B) :
    Q'.abs
      (faceMoment w (K+L) extent id B p * Q'.recipPos (faceMass w (K+L) extent id B)
          (faceMass_positive hw0 hw1 extent id hi H (K+L) (late_head eta K L hK) hB) +
       -(faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B)
          (faceMass_positive hw0 hw1 extent id hi H K (Nat.le_trans (Nat.le_max_left _ _) hK) hB))) ≤ 2*c*eta :=
  ratio_difference_bound _ _ _ _ (2*c*eta) _ _
    (determinant_bound hw0 hw1 eta he K L extent id hi hK H P)

omit H in
/-- Actual original spectator heat product, with its own cutoff and all
shared links retained. Only the displayed single occurrence changes cutoff. -/
theorem original_background_determinant (J : Nat) (hJ : headCutoff w ≤ J) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    let B := polynomialProduct (faceHeatPolynomial w J extent) ids
    Q'.abs (faceMoment w (K+L) extent id B p * faceMass w K extent id B +
      -(faceMoment w K extent id B p * faceMass w (K+L) extent id B)) ≤
      (2*c*eta)*(faceMass w (K+L) extent id B * faceMass w K extent id B) :=
  determinant_bound hw0 hw1 eta he K L extent id hi hK
    (headProduct_certificate hw0 hw1 J extent hJ ids hids) P

omit H in
/-- Normalized ORIGINAL heat products, with both positive denominators
constructed from the actual factors; no extra positivity premise is assumed. -/
theorem original_background_normalized (J : Nat) (hJ : headCutoff w ≤ J) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    let B := polynomialProduct (faceHeatPolynomial w J extent) ids
    let HB := headProduct_certificate hw0 hw1 J extent hJ ids hids
    let hB : (0 : Q') < quaternionHaar (blocks extent) B :=
      Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
        (partition_floor hw0 hw1 extent ids hids J hJ)
    Q'.abs
      (faceMoment w (K+L) extent id B p * Q'.recipPos (faceMass w (K+L) extent id B)
          (faceMass_positive hw0 hw1 extent id hi HB (K+L) (late_head eta K L hK) hB) +
       -(faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B)
          (faceMass_positive hw0 hw1 extent id hi HB K (Nat.le_trans (Nat.le_max_left _ _) hK) hB))) ≤ 2*c*eta :=
  normalized_difference_bound hw0 hw1 eta he K L extent id hi hK
    (headProduct_certificate hw0 hw1 J extent hJ ids hids) P
    (Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partition_floor hw0 hw1 extent ids hids J hJ))

end YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability

#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.mass_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.moment_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.old_moment_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.determinant_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.faceMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.normalized_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.original_background_determinant
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability.original_background_normalized
