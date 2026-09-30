/-
# Uncrossed ORIGINAL face pairs cancel under replica exchange

The selected physical links determine a literal involution of the doubled
original quaternion carrier. Every original plaquette pair wholly on one
side stays unchanged under arbitrary Haar insertions. The full pair product
is pinned to the product of the two ORIGINAL action polynomials, not an
independent-face measure. Crossing faces are retained for quantitative
comparison; no conditional-normalizer or Poincare estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionReplicaPairSwap
import YMGap.Continuum.BF4ExactSlabCutFaceGeometry
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal

namespace YMGap.Continuum.BF4ExactSlabReplicaCutLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionReplicaPairSwap
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabCutFaceGeometry
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Physical selection recoded to exactly the original in-range blocks. -/
def selectedBlocks (extent : Nat) (selected : List Z4Link) : List Nat :=
  (List.range (blocks extent)).filter
    (fun j => decide (correctedSlabLinkAt extent j ∈ selected))

theorem mem_selectedBlocks (extent : Nat) (selected : List Z4Link) (j : Nat) :
    j ∈ selectedBlocks extent selected ↔
      j < blocks extent ∧ correctedSlabLinkAt extent j ∈ selected := by
  simp [selectedBlocks]

def cutSwap (extent : Nat) (selected : List Z4Link) :
    QuaternionBlockInvolution (blocks extent + blocks extent) :=
  SU2QuaternionPartialSliceSwap.swap (blocks extent) (selectedBlocks extent selected)

def facePair (w : Q') (K extent id : Nat) : RatPoly :=
  let p := faceHeatPolynomial w K extent id
  polyMul p (liftBoundary (blocks extent) p)

def swappedFacePair (w : Q') (K extent : Nat) (selected : List Z4Link) (id : Nat) : RatPoly :=
  reindexQuaternionPolynomial (cutSwap extent selected) (facePair w K extent id)

def crossingMask (extent : Nat) (selected : List Z4Link) (id : Nat) : Bool :=
  cutCrossingFace selected (slabPlaquetteAt extent id)

/-- Exact whole-side cancellation for an ORIGINAL plaquette pair. -/
theorem uncrossed_face_pair (w : Q') (K extent : Nat) (selected : List Z4Link)
    (id : Nat) (hcross : crossingMask extent selected id = false) :
    HaarCarrierEqv (blocks extent + blocks extent)
      (swappedFacePair w K extent selected id) (facePair w K extent id) := by
  let face := slabPlaquetteAt extent id
  have hp := heatFace_supported w K extent id
  have hl := heatFace_local w K extent id
  by_cases hs : (edgesOf face).any (fun link => decide (link ∈ selected)) = true
  · have hall : ∀ link, link ∈ edgesOf face → link ∈ selected := by
      intro link hedge
      by_cases hm : link ∈ selected
      · exact hm
      · have hu : (edgesOf face).any (fun link => decide (link ∉ selected)) = true :=
          List.any_eq_true.mpr ⟨link, hedge, decide_eq_true hm⟩
        have hc : crossingMask extent selected id = true :=
          (Bool.and_eq_true _ _).mpr ⟨hs, hu⟩
        rw [hcross] at hc
        exact False.elim (Bool.false_ne_true hc)
    apply selected_pair_fixed (blocks extent) (selectedBlocks extent selected) _ hp
    intro j hj hnot
    apply independent_of_local hl hj
    intro he
    exact hnot ((mem_selectedBlocks extent selected j).mpr ⟨hj, hall _ he⟩)
  · have hnone : ∀ link, link ∈ edgesOf face → link ∉ selected := by
      intro link hedge hm
      exact hs (List.any_eq_true.mpr ⟨link, hedge, decide_eq_true hm⟩)
    apply unselected_pair_fixed (blocks extent) (selectedBlocks extent selected) _ hp
    intro j hj hmem
    apply independent_of_local hl hj
    intro he
    exact hnone _ he ((mem_selectedBlocks extent selected j).mp hmem).2

private theorem lift_one_carrier (n : Nat) :
    HaarCarrierEqv (n+n) (liftBoundary n polyOne) polyOne :=
  carrier_of_supported (lift_supported (supported_one n) n) (supported_one _)
    (SupportedHaarEqv.of_padded (lift_one (n+n) n)
      (lift_supported (supported_one n) n) (supported_one _))

/-- Pairwise face multiplication is the literal two-copy action product;
shared links within each copy have not been separated. -/
theorem facePair_product_pin (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    HaarCarrierEqv (blocks extent + blocks extent)
      (polynomialProduct (facePair w K extent) ids)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (liftBoundary (blocks extent) (polynomialProduct (faceHeatPolynomial w K extent) ids)))
  | [] => (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul polyOne)).symm.trans
      (HaarCarrierEqv.mul_left polyOne (lift_one_carrier (blocks extent)).symm)
  | id::ids => by
      change HaarCarrierEqv _
        (polyMul (facePair w K extent id) (polynomialProduct (facePair w K extent) ids)) _
      have h := HaarCarrierEqv.mul_left (facePair w K extent id)
        (facePair_product_pin w K extent ids)
      refine h.trans ?_
      change HaarCarrierEqv _
        (polyMul (polyMul (faceHeatPolynomial w K extent id)
            (liftBoundary (blocks extent) (faceHeatPolynomial w K extent id)))
          (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
            (liftBoundary (blocks extent) (polynomialProduct (faceHeatPolynomial w K extent) ids))))
        (polyMul (polyMul (faceHeatPolynomial w K extent id)
            (polynomialProduct (faceHeatPolynomial w K extent) ids))
          (liftBoundary (blocks extent) (polyMul (faceHeatPolynomial w K extent id)
            (polynomialProduct (faceHeatPolynomial w K extent) ids))))
      rw [lift_product]
      exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_four_swap _ _ _ _)

#print axioms selectedBlocks
#print axioms mem_selectedBlocks
#print axioms cutSwap
#print axioms facePair
#print axioms swappedFacePair
#print axioms crossingMask
#print axioms uncrossed_face_pair
#print axioms facePair_product_pin

end YMGap.Continuum.BF4ExactSlabReplicaCutLocality
