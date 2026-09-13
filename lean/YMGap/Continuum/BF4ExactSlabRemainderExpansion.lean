/-
# Exact ORIGINAL face-remainder expansion and uniform per-selection bounds

These are the original shared-link heat polynomials and Haar integral, not
the multiplicity-product law. Every finite original moment is the exact sum
over computed selections of positive-label face remainders. Their signed
activities obey delta(w)^n, with one small factor per selected face, uniformly
in representation cutoff and slab extent under the explicit small-nome guard.

All selections are still present. This is not yet the connected-cluster
reorganization, a bound on the normalized connected correlation, or decay
in separation. Counting all selections can still produce volume growth.
-/

import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.FinitePolynomialSubsetExpansion
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit

namespace YMGap.Continuum.BF4ExactSlabRemainderExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def remainderProduct (w : Q') (K extent : Nat) (ids : List Nat) : RatPoly :=
  polynomialProduct (fun id => faceHeatTail w extent id 1 K) ids

def activity (w : Q') (K extent : Nat) (ids : List Nat) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks extent).length (remainderProduct w K extent ids)

def insertedActivity (w : Q') (K extent : Nat) (p : RatPoly) (ids : List Nat) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul p (remainderProduct w K extent ids))

/-- The existing original numerator, expanded at its SAME cutoff and carrier. -/
theorem moment_expansion (w : Q') (K extent : Nat) (ids : List Nat) (p : RatPoly) :
    Q'.eqv (numerator w (boundaryCompleteSlabLinks extent).length extent ids p K)
      (listQSum (insertedActivity w K extent p) (selections ids)) :=
  haar_expansion _ (faceHeatPolynomial w K extent) (fun id => faceHeatTail w extent id 1 K)
    (fun id => faceHeat_eq_one_add w extent id K) p ids

theorem partition_expansion (w : Q') (K extent : Nat) (ids : List Nat) :
    Q'.eqv (heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K)
      (listQSum (activity w K extent) (selections ids)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (product_expansion (faceHeatPolynomial w K extent)
    (fun id => faceHeatTail w extent id 1 K) (fun id => faceHeat_eq_one_add w extent id K) ids))
    (quaternionHaar_finitePolySum _ _ _)

theorem fullAction_expansion (w : Q') (K half : Nat) :
    Q'.eqv (fullActionValue w K half)
      (listQSum (activity w K (centralExtent half)) (selections (slabPhysicalFaceEdges (centralExtent half)))) :=
  partition_expansion w K _ _

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)
include hw0 hw1 hsmall

def productInterval (K extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length (remainderProduct w K extent ids) ((heatRemainderBound w)^ids.length) :=
  Interval.productUniform _ _ ids (fun id hid => faceRemainderInterval hw0 hw1 hsmall extent id (hi id hid) K)

theorem activity_bound (K extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (activity w K extent ids) ≤ (heatRemainderBound w)^ids.length :=
  (productInterval hw0 hw1 hsmall K extent ids hi).haar_bound

theorem selected_activity_bound (K extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (ys : List Nat) (hy : ys ∈ selections ids) :
    Q'.abs (activity w K extent ys) ≤ (heatRemainderBound w)^ys.length :=
  activity_bound hw0 hw1 hsmall K extent ys (fun id hid => hi id (selected_mem hy id hid))

theorem inserted_activity_bound (K extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) {p : RatPoly} {c : Q'}
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) :
    Q'.abs (insertedActivity w K extent p ids) ≤ c*(heatRemainderBound w)^ids.length :=
  (P.mul (productInterval hw0 hw1 hsmall K extent ids hi)).haar_bound

/-- The background can share all link variables with the selected faces. -/
theorem positive_background_bound (K extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) {p : RatPoly}
    (P : Certificate (boundaryCompleteSlabLinks extent).length p) :
    Q'.abs (insertedActivity w K extent p ids) ≤
      (heatRemainderBound w)^ids.length * quaternionHaar (boundaryCompleteSlabLinks extent).length p :=
  (productInterval hw0 hw1 hsmall K extent ids hi).weighted_haar_bound P

/-- Background premise discharged for an actual original interacting sub-action. -/
theorem original_background_bound (hdelta : heatRemainderBound w ≤ 1) (K extent : Nat)
    (ids background : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (insertedActivity w K extent (polynomialProduct (faceHeatPolynomial w K extent) background) ids) ≤
      (heatRemainderBound w)^ids.length * heatProductHaar w (boundaryCompleteSlabLinks extent).length extent background K :=
  positive_background_bound hw0 hw1 hsmall K extent ids hi (faceProductCertificate hw0 hw1 hsmall hdelta K extent background hb)

end SmallNome
end YMGap.Continuum.BF4ExactSlabRemainderExpansion

#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.remainderProduct
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.activity
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.insertedActivity
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.moment_expansion
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.partition_expansion
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.fullAction_expansion
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.productInterval
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.activity_bound
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.selected_activity_bound
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.inserted_activity_bound
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.positive_background_bound
#print axioms YMGap.Continuum.BF4ExactSlabRemainderExpansion.original_background_bound
