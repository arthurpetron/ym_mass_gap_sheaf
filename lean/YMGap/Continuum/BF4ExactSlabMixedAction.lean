/-
# The ORIGINAL boundary determinant as a mixed-action face functional

The first copy contains every selected face; the second contains just the
faces passing a supplied Boolean interior test. Both moments use the SAME
original Haar carrier and representation cutoff. The determinant is pinned
to the existing bulk boundary numerator for the actual embedded-interior
test. Its partition factor is a product of TWO different original actions,
not an interior partition square.

When all selected faces are interior the determinant vanishes identically,
and so does its finite-difference coefficient. No smallness or independence
assumption enters these finite identities.
-/

import YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
import YMGap.Continuum.BF4ExactSlabSpectatorResummation
import YMGap.Continuum.FiniteSelectionOrder

namespace YMGap.Continuum.BF4ExactSlabMixedAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def inside (keep : Nat → Bool) (ids : List Nat) : List Nat := ids.filter keep

def mixedPartition (w : Q') (K extent : Nat) (keep : Nat → Bool) (ids : List Nat) : Q' :=
  heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K *
    heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (inside keep ids) K

def mixedNumerator (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (ids : List Nat) : Q' :=
  numerator w (boundaryCompleteSlabLinks extent).length extent ids p K *
    heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (inside keep ids) K +
  -(numerator w (boundaryCompleteSlabLinks extent).length extent (inside keep ids) p K *
    heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K)

def mixedCoefficient (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (ids : List Nat) : Q' :=
  coefficient (mixedNumerator w K extent keep p) ids

def mixedPartitionCoefficient (w : Q') (K extent : Nat) (keep : Nat → Bool) (ids : List Nat) : Q' :=
  coefficient (mixedPartition w K extent keep) ids

theorem unit_numerator (w : Q') (K extent : Nat) (ids : List Nat) :
    numerator w (boundaryCompleteSlabLinks extent).length extent ids polyOne K ≈
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K :=
  haar_of_coeff (RatPolyCoeffEqv.one_mul _)

theorem moment_perm (w : Q') (K extent : Nat) (p : RatPoly) {xs ys : List Nat} (h : xs.Perm ys) :
    numerator w (boundaryCompleteSlabLinks extent).length extent xs p K ≈
      numerator w (boundaryCompleteSlabLinks extent).length extent ys p K :=
  haar_of_coeff ((RatPolyCoeffEqv.refl p).mul (polynomialProduct_perm (faceHeatPolynomial w K extent) h))

theorem partition_perm (w : Q') (K extent : Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    heatProductHaar w (boundaryCompleteSlabLinks extent).length extent xs K ≈
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ys K :=
  haar_of_coeff (polynomialProduct_perm (faceHeatPolynomial w K extent) h)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem mixedNumerator_perm (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly)
    {xs ys : List Nat} (h : xs.Perm ys) :
    mixedNumerator w K extent keep p xs ≈ mixedNumerator w K extent keep p ys :=
  Q'.add_eqv_congr' (qmul (moment_perm w K extent p h) (partition_perm w K extent (h.filter keep)))
    (Q'.neg_eqv_congr _ _ (qmul (moment_perm w K extent p (h.filter keep)) (partition_perm w K extent h)))

theorem mixedCoefficient_perm (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly)
    {xs ys : List Nat} (h : xs.Perm ys) :
    mixedCoefficient w K extent keep p xs ≈ mixedCoefficient w K extent keep p ys :=
  coefficient_perm h _ (fun _ _ hp => mixedNumerator_perm w K extent keep p hp)

theorem mixedNumerator_inside_zero (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly)
    (ids : List Nat) (hi : ∀ id, id ∈ ids → keep id = true) : mixedNumerator w K extent keep p ids ≈ 0 := by
  have he : inside keep ids = ids := List.filter_eq_self.mpr hi
  unfold mixedNumerator
  rw [he]
  exact Q'.add_neg_self_eqv _

theorem mixedCoefficient_inside_zero (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly)
    (ids : List Nat) (hi : ∀ id, id ∈ ids → keep id = true) : mixedCoefficient w K extent keep p ids ≈ 0 :=
  coefficient_zero_on _ _ (fun ys hy => mixedNumerator_inside_zero w K extent keep p ys
    (fun id hid => hi id (selected_mem hy id hid)))

def boundaryKeep (half padding : Nat) (id : Nat) : Bool := decide (id ∈ embeddedIds half padding)

/-- Exact pin to the pre-existing determinant; no change of action or carrier. -/
theorem boundary_mixedNumerator (w : Q') (K half padding : Nat) (p : RatPoly) :
    boundaryNumerator w half padding p K ≈
      mixedNumerator w K (centralExtent (half+padding)) (boundaryKeep half padding) p
        (slabPhysicalFaceEdges (centralExtent (half+padding))) :=
  Q'.add_eqv_congr'
    (qmul (Q'.eqv_refl _) (unit_numerator w K (centralExtent (half+padding)) (interiorIds half padding)))
    (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl _)
      (unit_numerator w K (centralExtent (half+padding)) (slabPhysicalFaceEdges (centralExtent (half+padding))))))

end YMGap.Continuum.BF4ExactSlabMixedAction

#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.inside
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedPartition
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedNumerator
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedPartitionCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.unit_numerator
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.moment_perm
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.partition_perm
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedNumerator_perm
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedCoefficient_perm
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedNumerator_inside_zero
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.mixedCoefficient_inside_zero
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.boundaryKeep
#print axioms YMGap.Continuum.BF4ExactSlabMixedAction.boundary_mixedNumerator
