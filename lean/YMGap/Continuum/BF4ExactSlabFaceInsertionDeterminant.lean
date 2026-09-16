/-
# One-face insertion with both original partition factors retained

Appending one actual heat factor turns the change-of-action determinant
into its exact covariance numerator under the preceding selected action.
Both actions use the same quaternion Haar carrier and cutoff. The mixed
action endpoints retain Z_(S++[f]) * Z_S, not a square of either partition.

These are finite polynomial identities for arbitrary selected face lists.
No independence, positivity, normalization, decay, or telescoping estimate
is assumed or concluded.
-/

import YMGap.Continuum.BF4ExactSlabMixedAction

namespace YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

private theorem product_append_face (factor : Nat → RatPoly) (ids : List Nat) (id : Nat) :
    RatPolyCoeffEqv (polynomialProduct factor (ids ++ [id]))
      (polyMul (factor id) (polynomialProduct factor ids)) :=
  (polynomialProduct_append factor ids [id]).trans
    (((RatPolyCoeffEqv.mul_one (factor id)).mul_left _).trans
      (RatPolyCoeffEqv.mul_comm _ _))

/-- The observable retains the actual newly inserted face heat polynomial. -/
theorem numerator_append_face (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p : RatPoly) :
    numerator w (blocks extent) extent (ids ++ [id]) p K ≈
      numerator w (blocks extent) extent ids (polyMul p (faceHeatPolynomial w K extent id)) K :=
  haar_of_coeff
    (((product_append_face (faceHeatPolynomial w K extent) ids id).mul_left p).trans
      (RatPolyCoeffEqv.mul_assoc p (faceHeatPolynomial w K extent id)
        (polynomialProduct (faceHeatPolynomial w K extent) ids)).symm)

/-- The new partition is the old-action moment of the actual inserted heat. -/
theorem partition_append_face (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) :
    heatProductHaar w (blocks extent) extent (ids ++ [id]) K ≈
      numerator w (blocks extent) extent ids (faceHeatPolynomial w K extent id) K :=
  haar_of_coeff (product_append_face (faceHeatPolynomial w K extent) ids id)

/-- Exact one-face change-of-action determinant, before any normalization. -/
theorem face_insertion_determinant (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p : RatPoly) :
    numerator w (blocks extent) extent (ids ++ [id]) p K *
        heatProductHaar w (blocks extent) extent ids K +
      -(numerator w (blocks extent) extent ids p K *
        heatProductHaar w (blocks extent) extent (ids ++ [id]) K) ≈
    numerator w (blocks extent) extent ids (polyMul p (faceHeatPolynomial w K extent id)) K *
        heatProductHaar w (blocks extent) extent ids K +
      -(numerator w (blocks extent) extent ids p K *
        numerator w (blocks extent) extent ids (faceHeatPolynomial w K extent id) K) :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (numerator_append_face w K extent ids id p))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _ (partition_append_face w K extent ids id)))

private theorem inside_append_face (keep : Nat → Bool) (ids : List Nat) (id : Nat)
    (hids : ∀ j, j ∈ ids → keep j = true) (hid : keep id = false) :
    inside keep (ids ++ [id]) = ids := by
  unfold inside
  rw [List.filter_append, List.filter_eq_self.mpr hids]
  simp [hid]

/-- The existing mixed numerator specializes to the same one-face covariance. -/
theorem mixedNumerator_append_face (w : Q') (K extent : Nat) (keep : Nat → Bool)
    (ids : List Nat) (id : Nat) (p : RatPoly)
    (hids : ∀ j, j ∈ ids → keep j = true) (hid : keep id = false) :
    mixedNumerator w K extent keep p (ids ++ [id]) ≈
      numerator w (blocks extent) extent ids (polyMul p (faceHeatPolynomial w K extent id)) K *
          heatProductHaar w (blocks extent) extent ids K +
        -(numerator w (blocks extent) extent ids p K *
          numerator w (blocks extent) extent ids (faceHeatPolynomial w K extent id) K) := by
  unfold mixedNumerator
  rw [inside_append_face keep ids id hids hid]
  exact face_insertion_determinant w K extent ids id p

/-- The normalization remains the product of the two DIFFERENT action partitions. -/
theorem mixedPartition_append_face (w : Q') (K extent : Nat) (keep : Nat → Bool)
    (ids : List Nat) (id : Nat)
    (hids : ∀ j, j ∈ ids → keep j = true) (hid : keep id = false) :
    mixedPartition w K extent keep (ids ++ [id]) =
      heatProductHaar w (blocks extent) extent (ids ++ [id]) K *
        heatProductHaar w (blocks extent) extent ids K := by
  unfold mixedPartition
  rw [inside_append_face keep ids id hids hid]

end YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant

#print axioms YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant.numerator_append_face
#print axioms YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant.partition_append_face
#print axioms YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant.face_insertion_determinant
#print axioms YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant.mixedNumerator_append_face
#print axioms YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant.mixedPartition_append_face
