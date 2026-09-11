/-
# Anchor control of the fine positive-time occupation

The positive-time defect envelope uses the normalized physical event mass,
whereas the strong-coupling one-face estimates were proved through the
expanded fine-source enumeration.  This module closes that representation
seam exactly.  The expanded positive-source mass is the normalized physical
positive-face probability, so both the original `8/17` estimate and the
distinct-partner-face refinement `64/425` apply to the fine event in the
coherent occupation envelope.

The resulting estimate is deliberately parameter-correct: it applies only
when the fine datum is identified with `anchorSlabPhysicalData cutoff half`.
No coupling-uniform, cutoff-uniform, volume-uniform, lattice-spacing,
coarse-output, reflection-positivity, transfer-gap, or continuum claim is
made.

## Axiom gate

Finite event disintegration and exact positive-rational division only.  No
classical choice, placeholder, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimePushedOccupation
import YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
import YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorOccupation

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimePushedOccupation
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalGeometric
open YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem qeqv_of_le_of_ge_local {left right : Q'}
    (hle : left ≤ right) (hge : right ≤ left) : left ≈ right := by
  show left.num * (right.den : Int) = right.num * (left.den : Int)
  exact Int.le_antisymm hle hge

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hnumerator : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le right denominator hdenominator
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.divPos_mul_eqv left denominator hdenominator)
        hnumerator)
  · apply Q'.le_divPos_of_mul_le left denominator hdenominator
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.divPos_mul_eqv right denominator hdenominator)
        (Q'.eqv_symm hnumerator))

/-- The normalized positive-face event probability is exactly the expanded
positive-source mass used by the removal-fiber contraction. -/
theorem normalizedSlabFacePositiveMass_eqv_expandedMass
    (D : SlabPhysicalData) (faceId : Nat) :
    normalizedSlabEventMass D (slabPhysicalFacePositiveB faceId) ≈
      slabObservablePositiveExpandedMass D faceId := by
  let hpartition := slabParametricKPhysicalPartition_pos
    D.coupling_nonnegative D.cutoff D.extent
  refine Q'.eqv_trans _
    (finiteWeightedEventProbability
      D.physicalLabellings D.physicalTerm D.physicalPartition
      hpartition (slabPhysicalFacePositiveB faceId)) _
    (normalizedSlabEventMass_eqv_probability
      D (slabPhysicalFacePositiveB faceId)) ?_
  unfold finiteWeightedEventProbability
    slabObservablePositiveExpandedMass
  exact divPos_eqv_congr_numerator_local hpartition
    (Q'.eqv_symm
      (slabObservablePositiveSourceWeight_eqv_physicalEventMass
        D faceId))

/-- At the named SU(2) strong-coupling anchor, the genuine normalized
one-face occupation is at most `8/17`. -/
theorem normalizedAnchorSlabFacePositiveMass_le_eightSeventeenths
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    normalizedSlabEventMass (anchorSlabPhysicalData cutoff half)
        (slabPhysicalFacePositiveB faceId) ≤
      Q'.mkPos 8 17 (by decide) := by
  exact Q'.le_trans' _
    (slabObservablePositiveExpandedMass
      (anchorSlabPhysicalData cutoff half) faceId) _
    (Q'.le_of_eqv
      (normalizedSlabFacePositiveMass_eqv_expandedMass
        (anchorSlabPhysicalData cutoff half) faceId))
    (slabObservablePositiveExpandedMass_le_eightSeventeenths
      cutoff half faceId hface)

/-- Using the distinct partner face in every physical strand component, the
same genuine normalized one-face occupation sharpens to `64/425`. -/
theorem normalizedAnchorSlabFacePositiveMass_le_sixtyFourFourTwentyFive
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    normalizedSlabEventMass (anchorSlabPhysicalData cutoff half)
        (slabPhysicalFacePositiveB faceId) ≤
      Q'.mkPos 64 425 (by decide) := by
  exact Q'.le_trans' _
    (slabObservablePositiveExpandedMass
      (anchorSlabPhysicalData cutoff half) faceId) _
    (Q'.le_of_eqv
      (normalizedSlabFacePositiveMass_eqv_expandedMass
        (anchorSlabPhysicalData cutoff half) faceId))
    (slabObservablePositiveExpandedMass_le_sixtyFourFourTwentyFive
      cutoff half faceId hface)

/-- If the fine branch is the named anchor datum, the coherent fine-source
occupation in the new positive-time envelope inherits the same `8/17`
bound. -/
theorem coherentFineFaceSourceMass_le_eightSeventeenths
    (S : SlabScalePair) (cutoff half faceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    coherentFineEventSourceMass S
        (slabPhysicalFacePositiveB faceId) ≤
      Q'.mkPos 8 17 (by decide) := by
  refine Q'.le_trans' _
    (normalizedSlabEventMass S.fine
      (slabPhysicalFacePositiveB faceId)) _
    (coherentFineEventSourceMass_le_normalizedSlabEventMass
      S (slabPhysicalFacePositiveB faceId)) ?_
  rw [hfine]
  exact normalizedAnchorSlabFacePositiveMass_le_eightSeventeenths
    cutoff half faceId hface

/-- The coherent fine-source occupation inherits the sharpened `64/425`
anchor bound under the same explicit identification of its fine datum. -/
theorem coherentFineFaceSourceMass_le_sixtyFourFourTwentyFive
    (S : SlabScalePair) (cutoff half faceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    coherentFineEventSourceMass S
        (slabPhysicalFacePositiveB faceId) ≤
      Q'.mkPos 64 425 (by decide) := by
  refine Q'.le_trans' _
    (normalizedSlabEventMass S.fine
      (slabPhysicalFacePositiveB faceId)) _
    (coherentFineEventSourceMass_le_normalizedSlabEventMass
      S (slabPhysicalFacePositiveB faceId)) ?_
  rw [hfine]
  exact normalizedAnchorSlabFacePositiveMass_le_sixtyFourFourTwentyFive
    cutoff half faceId hface

#print axioms normalizedSlabFacePositiveMass_eqv_expandedMass
#print axioms normalizedAnchorSlabFacePositiveMass_le_eightSeventeenths
#print axioms normalizedAnchorSlabFacePositiveMass_le_sixtyFourFourTwentyFive
#print axioms coherentFineFaceSourceMass_le_eightSeventeenths
#print axioms coherentFineFaceSourceMass_le_sixtyFourFourTwentyFive

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorOccupation
