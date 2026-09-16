/-
# Spatial boundary decay for an original selected-chain plaquette character

The aligned smaller-chain mask removes only spatially distant target faces.
Its actual active cores therefore have at least r+1 faces. The singleton
carrier, literal link locality and character interval certificate feed the
existing original-action determinant estimate, with no supplied decay bound.

Both original partition factors cancel at the finite cutoff. The same
coefficient then bounds the constructed cutoff limits. The coefficient
depends on the nome and spin, but not on the time buffer, cutoff, base size,
outer spatial padding or root time. Physical placement and the small-nome
guards remain explicit. No smaller-state transport, spatial limit or
continuum conclusion is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction
import YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison
import YMGap.Continuum.QuaternionHaarUnitScalarSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- The original plaquette word on the target chart's original Haar carrier. -/
def placedCharacter (base margin H t timeOrigin : Nat) (face : Z4Plaq)
    (spin : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial (chartExtent base margin H t)
    (shiftFace (margin+1) timeOrigin face)).scalar spin

def characterCap (spin : Nat) : Q' := 2*(16 : Q')^spin

def characterAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (spin : Nat) : Q' :=
  (characterCap spin+characterCap spin)*singlePlaquetteAmplitude w hd hs

/-- A constructed two-sided polynomial certificate, not a pointwise bound premise. -/
def placedCharacter_interval (base margin H t timeOrigin : Nat) (face : Z4Plaq)
    (hface : shiftFace (margin+1) timeOrigin face ∈
      boundaryCompleteSlabPlaquettes (chartExtent base margin H t)) (spin : Nat) :
    Interval (boundaryCompleteSlabLinks (chartExtent base margin H t)).length
      (placedCharacter base margin H t timeOrigin face spin) (characterCap spin) :=
  characterInterval (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette hface)) spin

theorem placedCharacter_local (base margin H t timeOrigin : Nat) (face : Z4Plaq)
    (spin : Nat) :
    LinkLocal (chartExtent base margin H t) (edgesOf (shiftFace (margin+1) timeOrigin face))
      (placedCharacter base margin H t timeOrigin face spin) :=
  (face_scalar_local _ _).character spin

/-- The singleton probe pays the entire spatial separation, including r+1. -/
theorem active_core_size_floor (base r d H t timeOrigin : Nat) (face : Z4Plaq)
    (hp : face ∈ spatialFaces base) {anchor : List Nat}
    (ha : anchor ∈ activeAnchors (chartExtent base (r+d) H t)
      (edgesOf (shiftFace (r+d+1) timeOrigin face)) (keep base r d H t)
      (chartIds base (r+d) H t)) : r+1 ≤ anchor.length := by
  have h := active_core_linf_floor (distance := r+1)
    (singletonCarrier (shiftFace (r+d+1) timeOrigin face))
    (chartIds_nodup base (r+d) H t) (fun _ hi => chartIds_physical hi) ha (by
      intro id hi ho
      exact omitted_separation base r d H t timeOrigin hp hi (of_decide_eq_false ho))
  change (r+1)+1 ≤ 1+anchor.length at h
  omega

/-- Actual original determinant with its two different original partitions. -/
theorem determinant_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K base r d H t timeOrigin : Nat) (face : Z4Plaq) (hp : face ∈ spatialFaces base)
    (hface : shiftFace (r+d+1) timeOrigin face ∈
      boundaryCompleteSlabPlaquettes (chartExtent base (r+d) H t)) (spin : Nat) :
    Q'.abs (mixedNumerator w K (chartExtent base (r+d) H t) (keep base r d H t)
      (placedCharacter base (r+d) H t timeOrigin face spin) (chartIds base (r+d) H t)) ≤
      (characterAmplitude w hd hs spin * (entropyRate 625 (adjustedCoreRate w hd))^(r+1)) *
        mixedPartition w K (chartExtent base (r+d) H t) (keep base r d H t)
          (chartIds base (r+d) H t) := by
  have h := mixedNumerator_tail_bound hw0 hw1 hsmall hd hs K (chartExtent base (r+d) H t)
    (keep base r d H t) (placedCharacter base (r+d) H t timeOrigin face spin) (characterCap spin)
    (placedCharacter_interval base (r+d) H t timeOrigin face hface spin)
    (edgesOf (shiftFace (r+d+1) timeOrigin face))
    (singletonCarrier (shiftFace (r+d+1) timeOrigin face))
    (placedCharacter_local base (r+d) H t timeOrigin face spin)
    (chartIds base (r+d) H t) (r+1) (chartIds_nodup base (r+d) H t)
    (fun _ hi => chartIds_physical hi)
    (fun _ ha => active_core_size_floor base r d H t timeOrigin face hp ha)
  rw [singleton_budget_pin] at h
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (characterCap spin+characterCap spin) _ _
        (singlePlaquetteBudget_factor w hd hs (r+1)))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

/-- Stage-uniform original normalized comparison on the SAME target carrier. -/
theorem finiteValue_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r d H t timeOrigin : Nat) (face : Z4Plaq) (hp : face ∈ spatialFaces base)
    (hface : shiftFace (r+d+1) timeOrigin face ∈
      boundaryCompleteSlabPlaquettes (chartExtent base (r+d) H t)) (spin stage : Nat) :
    Q'.abs (finiteValue w hw0 hw1 (chartExtent base (r+d) H t)
      (chartIds base (r+d) H t) (fun _ hi => chartIds_physical hi)
      (placedCharacter base (r+d) H t timeOrigin face spin) stage +
      -(finiteValue w hw0 hw1 (chartExtent base (r+d) H t)
        (insideIds base r d H t) (insideIds_physical base r d H t)
        (placedCharacter base (r+d) H t timeOrigin face spin) stage)) ≤
      characterAmplitude w hd hs spin * (entropyRate 625 (adjustedCoreRate w hd))^(r+1) := by
  apply finite_comparison_bound w hw0 hw1 (chartExtent base (r+d) H t)
    (chartIds base (r+d) H t) (fun _ hi => chartIds_physical hi)
    (insideIds base r d H t) (insideIds_physical base r d H t)
    (placedCharacter base (r+d) H t timeOrigin face spin) _ stage
  exact determinant_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs
    (headCutoff w+stage) base r d H t timeOrigin face hp hface spin

/-- The same coefficient survives removal of the representation cutoff. -/
theorem expectation_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r d H t timeOrigin : Nat) (face : Z4Plaq) (hp : face ∈ spatialFaces base)
    (hface : shiftFace (r+d+1) timeOrigin face ∈
      boundaryCompleteSlabPlaquettes (chartExtent base (r+d) H t)) (spin : Nat) :
    leEv (CReal.abs (CReal.sub
      (expectation w hw0 hw1 (chartExtent base (r+d) H t)
        (chartIds base (r+d) H t) (fun _ hi => chartIds_physical hi)
        (placedCharacter base (r+d) H t timeOrigin face spin))
      (expectation w hw0 hw1 (chartExtent base (r+d) H t)
        (insideIds base r d H t) (insideIds_physical base r d H t)
        (placedCharacter base (r+d) H t timeOrigin face spin))))
      (ofQ' (characterAmplitude w hd hs spin * (entropyRate 625 (adjustedCoreRate w hd))^(r+1))) := by
  apply comparison_bound_eventually w hw0 hw1 (chartExtent base (r+d) H t)
    (chartIds base (r+d) H t) (fun _ hi => chartIds_physical hi)
    (insideIds base r d H t) (insideIds_physical base r d H t)
    (placedCharacter base (r+d) H t timeOrigin face spin) _ 0
  intro K _
  exact determinant_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs
    K base r d H t timeOrigin face hp hface spin

#print axioms placedCharacter
#print axioms characterCap
#print axioms characterAmplitude
#print axioms placedCharacter_interval
#print axioms placedCharacter_local
#print axioms active_core_size_floor
#print axioms determinant_bound
#print axioms finiteValue_bound
#print axioms expectation_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteBoundary
