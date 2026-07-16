/-
# Weight envelope for the slab connected carrier

The exact slab source-pair weight is bounded by one strong-coupling envelope
factor per face in the colored union support, times the exact activities of
the ambient and slab-supported path-deleted backgrounds.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
import YMGap.Continuum.Z4CanonicalConnectedCarrierWeight

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

theorem slabConnectedCarrierSupport_length_le_pathFaceCount
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    (slabConnectedCarrierSupport defaultRoot entry).length ≤
      familyFaceCount (slabConnectedPathLeftFamily defaultRoot entry) +
        familyFaceCount (slabConnectedPathRightFamily defaultRoot entry) := by
  have hbound := familyUnionSupport_length_le_familyFaceCount (extent + 1)
    (slabConnectedPathLeftFamily defaultRoot entry ++
      slabConnectedPathRightFamily defaultRoot entry)
  rw [familyFaceCount_append] at hbound
  exact hbound

theorem slabConnectedPathPairWeight_le_totalFacePow
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedPathPairWeight defaultRoot entry ≤
      anchorPerFaceEnvelope ^
        (familyFaceCount (slabConnectedPathLeftFamily defaultRoot entry) +
          familyFaceCount
            (slabConnectedPathRightFamily defaultRoot entry)) := by
  have hleft := compatibleFamily_activity_le_totalFacePow
    (slabConnectedPathLeftFamily_mem defaultRoot entry)
  have hright := compatibleFamily_activity_le_totalFacePow
    (slabConnectedPathRightFamily_mem defaultRoot entry)
  have hright0 := canonicalSurfaceFamilyActivity_nonnegative (extent + 1)
    (slabConnectedPathRightFamily defaultRoot entry)
  have hleftPow0 : (0 : Q') ≤ anchorPerFaceEnvelope ^
      familyFaceCount (slabConnectedPathLeftFamily defaultRoot entry) :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  unfold slabConnectedPathPairWeight
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.pow_add_eqv anchorPerFaceEnvelope
          (familyFaceCount
            (slabConnectedPathLeftFamily defaultRoot entry))
          (familyFaceCount
            (slabConnectedPathRightFamily defaultRoot entry))))))

theorem slabConnectedPathPairWeight_le_supportPow
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedPathPairWeight defaultRoot entry ≤
      anchorPerFaceEnvelope ^
        (slabConnectedCarrierSupport defaultRoot entry).length := by
  exact Q'.le_trans' _ _ _
    (slabConnectedPathPairWeight_le_totalFacePow defaultRoot entry)
    (pow_base_antitone (r := anchorPerFaceEnvelope)
      (by decide) (by decide)
      (slabConnectedCarrierSupport_length_le_pathFaceCount
        defaultRoot entry))

theorem slabConnectedBackgroundPairWeight_nonnegative
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    (0 : Q') ≤ slabConnectedBackgroundPairWeight defaultRoot entry := by
  unfold slabConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (canonicalSurfaceFamilyActivity_nonnegative (extent + 1) _)
    (canonicalSurfaceFamilyActivity_nonnegative (extent + 1) _)

theorem slabConnectedSourcePairWeight_le_support_background
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabCylinderSourcePairWeight entry.val ≤
      anchorPerFaceEnvelope ^
          (slabConnectedCarrierSupport defaultRoot entry).length *
        slabConnectedBackgroundPairWeight defaultRoot entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabConnectedSourcePairWeight_factor defaultRoot entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (slabConnectedPathPairWeight_le_supportPow defaultRoot entry)
      (slabConnectedBackgroundPairWeight_nonnegative defaultRoot entry))

#print axioms slabConnectedCarrierSupport_length_le_pathFaceCount
#print axioms slabConnectedPathPairWeight_le_supportPow
#print axioms slabConnectedSourcePairWeight_le_support_background

end YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierWeight
