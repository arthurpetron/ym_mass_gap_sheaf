/-
# Exact covariance transport for translated selected actions

An arbitrary finite selected ORIGINAL action and two supported observables
are transported through the existing injective slab `Placement`.  The target
law contains exactly the translated selected face factors, not the full target
action.  Finite covariance and its cutoff-removed constructive-real limit are
both pinned without changing the cutoff or normalization.

This is a carrier bridge, not a boundary-smallness estimate, omitted-face
telescope, thermodynamic limit, or mass-gap result.
-/

import YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

namespace YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPhysicalFaceEdges)

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- Exact finite covariance transport.  Both observables and every selected
action face pass through the same placement. -/
theorem finiteCovariance_pin
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length p)
    (hq : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length q)
    (stage : Nat) :
    finiteCovariance w hw0 hw1 P.target
        (selectedIds P ids) (selectedIds_physical P ids hids)
        (P.embedding.polynomial p) (P.embedding.polynomial q) stage ≈
      finiteCovariance w hw0 hw1 P.source ids hids p q stage := by
  have hproduct := finiteValue_pin P hw0 hw1 ids hids
    (polyMul p q) (supported_polyMul hp hq) stage
  rw [P.embedding.polynomial_mul] at hproduct
  have hleft := finiteValue_pin P hw0 hw1 ids hids p hp stage
  have hright := finiteValue_pin P hw0 hw1 ids hids q hq stage
  unfold finiteCovariance
  exact Q'.add_eqv_congr' hproduct
    (Q'.neg_eqv_congr _ _ (qmul hleft hright))

/-- Exact finite covariance transport to any literal target representatives
prefix-equivalent to the two embedded source observables. -/
theorem finiteCovariance_pin_of_prefix
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length p)
    (hq : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length q)
    (pTarget qTarget : RatPoly)
    (hpTarget : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.target).length pTarget)
    (hqTarget : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.target).length qTarget)
    (hpPrefix : QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial p) pTarget)
    (hqPrefix : QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial q) qTarget)
    (stage : Nat) :
    finiteCovariance w hw0 hw1 P.target
        (selectedIds P ids) (selectedIds_physical P ids hids)
        pTarget qTarget stage ≈
      finiteCovariance w hw0 hw1 P.source ids hids p q stage := by
  have hproduct := finiteValue_pin_of_prefix P hw0 hw1 ids hids
    (polyMul p q) (supported_polyMul hp hq)
    (polyMul pTarget qTarget) (supported_polyMul hpTarget hqTarget)
    (by
      rw [P.embedding.polynomial_mul]
      exact hpPrefix.mul hqPrefix)
    stage
  have hleft := finiteValue_pin_of_prefix P hw0 hw1 ids hids
    p hp pTarget hpTarget hpPrefix stage
  have hright := finiteValue_pin_of_prefix P hw0 hw1 ids hids
    q hq qTarget hqTarget hqPrefix stage
  unfold finiteCovariance
  exact Q'.add_eqv_congr' hproduct
    (Q'.neg_eqv_congr _ _ (qmul hleft hright))

/-- The same exact transport after the existing fixed-volume cutoff removal.
No new limit or comparison law is introduced. -/
theorem covariance_pin
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length p)
    (hq : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length q) :
    Equiv
      (covariance w hw0 hw1 P.target
        (selectedIds P ids) (selectedIds_physical P ids hids)
        (P.embedding.polynomial p) (P.embedding.polynomial q))
      (covariance w hw0 hw1 P.source ids hids p q) := by
  have hproduct := expectation_pin P hw0 hw1 ids hids
    (polyMul p q) (supported_polyMul hp hq)
  rw [P.embedding.polynomial_mul] at hproduct
  have hleft := expectation_pin P hw0 hw1 ids hids p hp
  have hright := expectation_pin P hw0 hw1 ids hids q hq
  unfold covariance
  exact (CReal.sub_congr_left hproduct).trans
    (CReal.sub_congr_right
      ((Pivot2.mul_congr_left hleft).trans
        (Pivot2.mul_congr_right hright)))

/-- The prefix-representative transport after the existing fixed-volume
cutoff removal. -/
theorem covariance_pin_of_prefix
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges P.source)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length p)
    (hq : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.source).length q)
    (pTarget qTarget : RatPoly)
    (hpTarget : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.target).length pTarget)
    (hqTarget : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks P.target).length qTarget)
    (hpPrefix : QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial p) pTarget)
    (hqPrefix : QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial q) qTarget) :
    Equiv
      (covariance w hw0 hw1 P.target
        (selectedIds P ids) (selectedIds_physical P ids hids)
        pTarget qTarget)
      (covariance w hw0 hw1 P.source ids hids p q) := by
  have hproduct := expectation_pin_of_prefix P hw0 hw1 ids hids
    (polyMul p q) (supported_polyMul hp hq)
    (polyMul pTarget qTarget) (supported_polyMul hpTarget hqTarget)
    (by
      rw [P.embedding.polynomial_mul]
      exact hpPrefix.mul hqPrefix)
  have hleft := expectation_pin_of_prefix P hw0 hw1 ids hids
    p hp pTarget hpTarget hpPrefix
  have hright := expectation_pin_of_prefix P hw0 hw1 ids hids
    q hq qTarget hqTarget hqPrefix
  unfold covariance
  exact (CReal.sub_congr_left hproduct).trans
    (CReal.sub_congr_right
      ((Pivot2.mul_congr_left hleft).trans
        (Pivot2.mul_congr_right hright)))

end YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance

#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance.finiteCovariance_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance.finiteCovariance_pin_of_prefix
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance.covariance_pin
#print axioms YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance.covariance_pin_of_prefix
