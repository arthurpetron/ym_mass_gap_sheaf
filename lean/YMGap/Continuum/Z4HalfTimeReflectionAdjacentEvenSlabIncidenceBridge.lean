/-
# Exact incidence bridge from the adjacent-even slab to fusion words

The production slab uses external face cutoff `K` but the geometry-derived
fusion-complete link window `linkAuxiliaryCutoff K = 6*K`.  This file keeps
those two roles distinct and rewrites every literal slab link multiplicity
as a fusion path on its actual incident face word, stably partitioned into
lower, fixed, and upper parts for the adjacent-even reflection plane.

This is the enumeration/incidence bridge required before the fixed-interface
sum can be compared with a tensor-network kernel.  No face variable is
duplicated: the same global labelling is read at every incident link.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenInterfaceLinkGram
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
import YMGap.Continuum.Z4FusionMultiplicityPermutationLift

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Actual incident-list partition -/

def adjacentEvenIncidentFaceIdParts
    (radius : Nat) (link : Z4Link) :
    List Nat × List Nat × List Nat :=
  partitionBySide
    (fun id => adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id))
    (slabIncidentPlaqIds (adjacentEvenExtent radius) link)

def adjacentEvenIncidentLowerSpins
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) : List Nat :=
  (adjacentEvenIncidentFaceIdParts radius link).1.map physical

def adjacentEvenIncidentFixedSpins
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) : List Nat :=
  (adjacentEvenIncidentFaceIdParts radius link).2.1.map physical

def adjacentEvenIncidentUpperSpins
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) : List Nat :=
  (adjacentEvenIncidentFaceIdParts radius link).2.2.map physical

def adjacentEvenPartitionedIncidentSpins
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) : List Nat :=
  adjacentEvenIncidentLowerSpins radius physical link ++
    adjacentEvenIncidentFixedSpins radius physical link ++
    adjacentEvenIncidentUpperSpins radius physical link

theorem adjacentEvenPartitionedIncidentSpins_perm
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) :
    (adjacentEvenPartitionedIncidentSpins radius physical link).Perm
      ((slabIncidentPlaqIds
        (adjacentEvenExtent radius) link).map physical) := by
  unfold adjacentEvenPartitionedIncidentSpins
    adjacentEvenIncidentLowerSpins
    adjacentEvenIncidentFixedSpins
    adjacentEvenIncidentUpperSpins
  have hparts := partitionBySide_perm
    (fun id => adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id))
    (slabIncidentPlaqIds (adjacentEvenExtent radius) link)
  simpa only [List.map_append] using hparts.map physical

theorem adjacentEvenPartitionedIncidentSpins_length_le_six
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) :
    (adjacentEvenPartitionedIncidentSpins radius physical link).length ≤ 6 := by
  rw [(adjacentEvenPartitionedIncidentSpins_perm
    radius physical link).length_eq, List.length_map]
  exact slabIncidentPlaqIds_length_le_six
    (adjacentEvenExtent radius) link

theorem adjacentEvenPartitionedIncidentSpins_bounded
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    SpinsBounded K
      (adjacentEvenPartitionedIncidentSpins radius physical link) := by
  have horiginal := slabIncidentSpins_bounded hphysical link
  exact spinsBounded_of_perm
    (adjacentEvenPartitionedIncidentSpins_perm
      radius physical link).symm horiginal

/-! ## 2. One production link equals its partitioned fusion word -/

/-- Exact production normalization: external labels are cutoff by `K`, while
the path count runs in the complete auxiliary window `6*K`. -/
theorem slabExplicitLinkMultiplicity_eq_partitionedFusionPath
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    slabExplicitLinkMultiplicity K (adjacentEvenExtent radius)
        physical link =
      fusionPathMultiplicity (linkAuxiliaryCutoff K)
        (adjacentEvenPartitionedIncidentSpins radius physical link) := by
  let original :=
    (slabIncidentPlaqIds (adjacentEvenExtent radius) link).map physical
  let partitioned :=
    adjacentEvenPartitionedIncidentSpins radius physical link
  have horiginalLength : original.length ≤ 6 := by
    unfold original
    rw [List.length_map]
    exact slabIncidentPlaqIds_length_le_six
      (adjacentEvenExtent radius) link
  have horiginalBounded : SpinsBounded K original := by
    unfold original
    exact slabIncidentSpins_bounded hphysical link
  have horiginalAux : SpinsBounded (linkAuxiliaryCutoff K) original := by
    intro spin hspin
    exact Nat.le_trans (horiginalBounded spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hpartitionPerm : partitioned.Perm original := by
    unfold partitioned original
    exact adjacentEvenPartitionedIncidentSpins_perm
      radius physical link
  have hpartitionLength : partitioned.length ≤ 6 := by
    rw [hpartitionPerm.length_eq]
    exact horiginalLength
  have hpartitionBounded : SpinsBounded K partitioned :=
    spinsBounded_of_perm hpartitionPerm.symm horiginalBounded
  have hpathPerm := fusionPathMultiplicity_physical_perm
    hpartitionPerm hpartitionLength hpartitionBounded
  unfold slabExplicitLinkMultiplicity
  change explicitValenceMultiplicity (linkAuxiliaryCutoff K)
      original.length (externalSpinsOfList original) = _
  exact (fusionPathMultiplicity_eq_explicit_of_length_le_six
      original horiginalLength horiginalAux).symm.trans hpathPerm.symm

/-! ## 3. Exact product bridge on the concrete fixed-link list -/

def adjacentEvenPartitionedLinkMultiplicity
    (K radius : Nat) (physical : Nat → Nat) (link : Z4Link) : Nat :=
  fusionPathMultiplicity (linkAuxiliaryCutoff K)
    (adjacentEvenPartitionedIncidentSpins radius physical link)

def adjacentEvenFixedLinks (radius : Nat) : List Z4Link :=
  (adjacentEvenSlabLinkParts radius).2.1

def adjacentEvenPartitionedFixedLinkProduct
    (K radius : Nat) (physical : Nat → Nat) : Nat :=
  natListProduct
    (adjacentEvenPartitionedLinkMultiplicity K radius physical)
    (adjacentEvenFixedLinks radius)

/-- The complete literal fixed-link product in the adjacent-even slab is
exactly the product of the partitioned lower/fixed/upper fusion words. -/
theorem slabFixedLinkMultiplicityProduct_eq_partitioned
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical) :
    slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
        physical (adjacentEvenFixedLinks radius) =
      adjacentEvenPartitionedFixedLinkProduct K radius physical := by
  unfold slabLinkMultiplicityProductOn
    adjacentEvenPartitionedFixedLinkProduct
  apply natListProduct_congr
  intro link _
  exact slabExplicitLinkMultiplicity_eq_partitionedFusionPath
    hphysical link

#print axioms adjacentEvenPartitionedIncidentSpins_perm
#print axioms adjacentEvenPartitionedIncidentSpins_length_le_six
#print axioms adjacentEvenPartitionedIncidentSpins_bounded
#print axioms slabExplicitLinkMultiplicity_eq_partitionedFusionPath
#print axioms slabFixedLinkMultiplicityProduct_eq_partitioned

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
