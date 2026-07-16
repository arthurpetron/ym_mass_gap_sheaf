/-
# Weight envelope for a colored connected carrier

The two path-color families may overlap across replicas, so their total face
count is larger than the size of their physical union.  Since the exact
per-face envelope is at most one, this only improves the bound: the entire
path-pair activity is dominated by one envelope factor per union face.  The
source-pair weight therefore factors into a connected-animal weight times
the exact activity of two compatible backgrounds.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
import YMGap.Continuum.Z4CanonicalPinnedPolymerBound

namespace YMGap.Continuum.Z4CanonicalConnectedCarrierWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. A union support has no more faces than its occurrences -/

theorem familyFaceCount_eq_flatMapLength :
    ∀ family : List (List Nat),
      (family.flatMap (fun polymer => polymer)).length =
        familyFaceCount family
  | [] => rfl
  | polymer :: rest => by
      simp only [List.flatMap_cons, List.length_append, familyFaceCount]
      rw [familyFaceCount_eq_flatMapLength rest]

theorem familyFaceCount_append :
    ∀ first second : List (List Nat),
      familyFaceCount (first ++ second) =
        familyFaceCount first + familyFaceCount second
  | [], second => by simp [familyFaceCount]
  | polymer :: rest, second => by
      change polymer.length + familyFaceCount (rest ++ second) =
        polymer.length + familyFaceCount rest + familyFaceCount second
      rw [familyFaceCount_append rest second]
      omega

theorem familyUnionSupport_length_le_familyFaceCount
    (n : Nat) (family : List (List Nat)) :
    (familyUnionSupport n family).length ≤ familyFaceCount family := by
  have hsupport : familyUnionSupport n family ∈
      sublists (physicalFaceEdges n) :=
    familyUnionSupport_mem_cutoffOneFaceSupports n family
  have hnodup : (familyUnionSupport n family).Nodup :=
    nodup_of_mem_sublists (physicalFaceEdges n)
      (familyUnionSupport n family) (physicalFaceEdges_nodup n) hsupport
  have hlength := length_le_of_unique_representation
    (fun face occurrence : Nat => face = occurrence)
    (familyUnionSupport n family)
    (family.flatMap (fun polymer => polymer)) hnodup
    (fun face hface => by
      obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
        (mem_familyUnionSupport_iff n family face).1 hface |>.2
      exact ⟨face,
        List.mem_flatMap.mpr ⟨polymer, hpolymer, hfacePolymer⟩, rfl⟩)
    (fun left _ right _ occurrence hleft hright =>
      hleft.trans hright.symm)
  rw [familyFaceCount_eq_flatMapLength] at hlength
  exact hlength

theorem connectedCarrierSupport_length_le_pathFaceCount
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    (connectedCarrierSupport hsmall entry).length ≤
      familyFaceCount (connectedPathLeftFamily hsmall entry) +
        familyFaceCount (connectedPathRightFamily hsmall entry) := by
  have hbound := familyUnionSupport_length_le_familyFaceCount n
    (connectedPathLeftFamily hsmall entry ++
      connectedPathRightFamily hsmall entry)
  rw [familyFaceCount_append] at hbound
  exact hbound

/-! ## 2. Exact path and source-pair envelopes -/

theorem connectedPathPairWeight_le_totalFacePow
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedPathPairWeight hsmall entry ≤
      anchorPerFaceEnvelope ^
        (familyFaceCount (connectedPathLeftFamily hsmall entry) +
          familyFaceCount (connectedPathRightFamily hsmall entry)) := by
  have hleft := compatibleFamily_activity_le_totalFacePow
    (connectedPathLeftFamily_mem hsmall entry)
  have hright := compatibleFamily_activity_le_totalFacePow
    (connectedPathRightFamily_mem hsmall entry)
  have hright0 := canonicalSurfaceFamilyActivity_nonnegative n
    (connectedPathRightFamily hsmall entry)
  have hleftPow0 : (0 : Q') ≤ anchorPerFaceEnvelope ^
      familyFaceCount (connectedPathLeftFamily hsmall entry) :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  unfold connectedPathPairWeight
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.pow_add_eqv anchorPerFaceEnvelope
          (familyFaceCount (connectedPathLeftFamily hsmall entry))
          (familyFaceCount (connectedPathRightFamily hsmall entry))))))

theorem connectedPathPairWeight_le_supportPow
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedPathPairWeight hsmall entry ≤
      anchorPerFaceEnvelope ^
        (connectedCarrierSupport hsmall entry).length := by
  exact Q'.le_trans' _ _ _
    (connectedPathPairWeight_le_totalFacePow hsmall entry)
    (pow_base_antitone (r := anchorPerFaceEnvelope)
      (by decide) (by decide)
      (connectedCarrierSupport_length_le_pathFaceCount hsmall entry))

theorem connectedBackgroundPairWeight_nonnegative
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    (0 : Q') ≤ connectedBackgroundPairWeight hsmall entry := by
  unfold connectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (canonicalSurfaceFamilyActivity_nonnegative n _)
    (canonicalSurfaceFamilyActivity_nonnegative n _)

theorem connectedSourcePairWeight_le_support_background
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    sourcePairWeight entry.val ≤
      anchorPerFaceEnvelope ^
          (connectedCarrierSupport hsmall entry).length *
        connectedBackgroundPairWeight hsmall entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (connectedSourcePairWeight_factor hsmall entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (connectedPathPairWeight_le_supportPow hsmall entry)
      (connectedBackgroundPairWeight_nonnegative hsmall entry))

end YMGap.Continuum.Z4CanonicalConnectedCarrierWeight

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierWeight.familyUnionSupport_length_le_familyFaceCount
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierWeight.connectedCarrierSupport_length_le_pathFaceCount
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierWeight.connectedPathPairWeight_le_supportPow
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierWeight.connectedSourcePairWeight_le_support_background
