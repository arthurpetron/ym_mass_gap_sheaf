/-
# Deterministic lower endpoints for adjacent-even fixed links

A fixed spatial link on the integer reflection slice has only one possible
lower incident plaquette: its backward temporal plaquette.  This leaf proves
that statement uniformly in the radius, transports it to the numerical slab
face identifiers, and collapses every lower fusion-channel amplitude to a
literal endpoint indicator.

The proof is local and symbolic.  It never materializes the exponentially
large list of bounded half-state labellings.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSupportGeneric
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenDeterministicLowerEndpoint

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. The unique possible lower plaquette -/

/-- The backward temporal plaquette is the only possible lower plaquette at a
fixed adjacent-even link.  The fixed-link hypothesis below ensures that the
link direction is spatial, so `planeOf link.2 .x3` is genuinely temporal. -/
def adjacentEvenFixedLinkLowerPlaquette (link : Z4Link) : Z4Plaq :=
  (subE link.1 .x3, planeOf link.2 .x3)

theorem adjacentEvenFixedLink_lowerPlaquette_eq_backwardTemporal
    {radius : Nat} {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedLinks radius)
    {id : Nat}
    (hid : id ∈ (adjacentEvenIncidentFaceIdParts radius link).1) :
    slabPlaquetteAt (adjacentEvenExtent radius) id =
      adjacentEvenFixedLinkLowerPlaquette link := by
  have hfixed := (mem_adjacentEvenFixedSlabLinks).mp hlink
  have hparts :=
    (mem_partitionBySide_lower
      (fun faceId => adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) faceId))
      id (slabIncidentPlaqIds (adjacentEvenExtent radius) link)).mp hid
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    (mem_slabIncidentPlaqIds.mp hparts.1)
  have hlookup :
      slabPlaquetteAt (adjacentEvenExtent radius) id = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  have hlisted := edge_complete plaquette link.1 link.2 hedge
  rw [hlookup]
  rw [hlookup] at hparts
  obtain ⟨⟨a, b, c, time⟩, direction⟩ := link
  cases direction <;>
    simp only [edgePlaqs, List.mem_cons, List.not_mem_nil,
      or_false] at hlisted <;>
    rcases hlisted with hlisted | hlisted | hlisted |
      hlisted | hlisted | hlisted <;>
    simp_all [adjacentEvenFixedLinkLowerPlaquette,
      adjacentEvenLinkSide, adjacentEvenPlaquetteSide,
      adjacentEvenSpatialSide, adjacentEvenTemporalSide,
      adjacentEvenCenter, subE, planeOf]

private theorem adjacentEvenFixedLink_lowerId_unique
    {radius : Nat} {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedLinks radius)
    {left right : Nat}
    (hleft : left ∈ (adjacentEvenIncidentFaceIdParts radius link).1)
    (hright : right ∈ (adjacentEvenIncidentFaceIdParts radius link).1) :
    left = right := by
  apply slabPlaquetteAt_injective_on_physical
  · exact slabIncidentPlaqId_physical
      ((mem_partitionBySide_lower
        (fun faceId => adjacentEvenPlaquetteSide radius
          (slabPlaquetteAt (adjacentEvenExtent radius) faceId))
        left (slabIncidentPlaqIds (adjacentEvenExtent radius) link)).mp
          hleft).1
  · exact slabIncidentPlaqId_physical
      ((mem_partitionBySide_lower
        (fun faceId => adjacentEvenPlaquetteSide radius
          (slabPlaquetteAt (adjacentEvenExtent radius) faceId))
        right (slabIncidentPlaqIds (adjacentEvenExtent radius) link)).mp
          hright).1
  · rw [adjacentEvenFixedLink_lowerPlaquette_eq_backwardTemporal hlink hleft,
      adjacentEvenFixedLink_lowerPlaquette_eq_backwardTemporal hlink hright]

/-! ## 2. At most one lower face and one deterministic endpoint -/

theorem adjacentEvenFixedLink_lowerIds_length_le_one
    (radius : Nat) {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedLinks radius) :
    (adjacentEvenIncidentFaceIdParts radius link).1.length ≤ 1 := by
  have hfull := slabIncidentPlaqIds_nodup
    (adjacentEvenExtent radius) link
  have hall :
      ((adjacentEvenIncidentFaceIdParts radius link).1 ++
        (adjacentEvenIncidentFaceIdParts radius link).2.1 ++
        (adjacentEvenIncidentFaceIdParts radius link).2.2).Nodup :=
    (partitionBySide_perm
      (fun id => adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id))
      (slabIncidentPlaqIds (adjacentEvenExtent radius) link)).symm.nodup
        hfull
  have houter := List.nodup_append.mp hall
  have hlowerFixed := List.nodup_append.mp houter.1
  have hlower := hlowerFixed.1
  cases hids : (adjacentEvenIncidentFaceIdParts radius link).1 with
  | nil => simp
  | cons head tail =>
      cases htail : tail with
      | nil => simp
      | cons second rest =>
          have hhead : head ∈
              (adjacentEvenIncidentFaceIdParts radius link).1 := by
            rw [hids]
            exact List.mem_cons_self
          have hsecond : second ∈
              (adjacentEvenIncidentFaceIdParts radius link).1 := by
            rw [hids, htail]
            exact List.mem_cons_of_mem head List.mem_cons_self
          have heq := adjacentEvenFixedLink_lowerId_unique
            hlink hhead hsecond
          have hnodup : (head :: second :: rest).Nodup := by
            simpa [hids, htail] using hlower
          have hnot := (List.nodup_cons.mp hnodup).1
          exact False.elim
            (hnot (heq ▸ List.mem_cons_self))

theorem adjacentEvenLowerSpins_length_le_one
    (radius : Nat) (physical : Nat → Nat) {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedLinks radius) :
    (adjacentEvenIncidentLowerSpins radius physical link).length ≤ 1 := by
  unfold adjacentEvenIncidentLowerSpins
  rw [List.length_map]
  exact adjacentEvenFixedLink_lowerIds_length_le_one radius hlink

/-- The lower endpoint is zero when the lower word is empty and is its unique
spin when that word is a singleton. -/
def adjacentEvenCommonLowerEndpoint
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) : Nat :=
  (adjacentEvenIncidentLowerSpins radius physical link).getD 0 0

theorem adjacentEvenCommonLowerEndpoint_le
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    adjacentEvenCommonLowerEndpoint radius physical link ≤ K := by
  have hbounded :=
    adjacentEvenPartitionedIncidentSpins_bounded hphysical link
  cases hlower : adjacentEvenIncidentLowerSpins radius physical link with
  | nil =>
      simp [adjacentEvenCommonLowerEndpoint, hlower]
  | cons head tail =>
      unfold adjacentEvenCommonLowerEndpoint
      rw [hlower]
      simp only [List.getD_cons_zero]
      apply hbounded head
      unfold adjacentEvenPartitionedIncidentSpins
      apply List.mem_append_left
      apply List.mem_append_left
      rw [hlower]
      exact List.mem_cons_self

/-! ## 3. Exact lower-channel delta -/

theorem adjacentEvenLowerChannelAmplitude_eq_indicator
    (cutoff radius : Nat) (physical : Nat → Nat)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks radius)
    (channel : Nat) :
    fusionChannelAmplitude cutoff
        (adjacentEvenIncidentLowerSpins radius physical link) channel =
      boolMultiplicity (decide
        (channel = adjacentEvenCommonLowerEndpoint radius physical link)) := by
  have hlength := adjacentEvenLowerSpins_length_le_one
    radius physical hlink
  cases hlower : adjacentEvenIncidentLowerSpins radius physical link with
  | nil =>
      unfold fusionChannelAmplitude adjacentEvenCommonLowerEndpoint
      simp [hlower, fusionPathMultiplicity_singleton,
        boolMultiplicity]
  | cons head tail =>
      cases tail with
      | nil =>
          have hendpoint :
              adjacentEvenCommonLowerEndpoint radius physical link =
                head := by
            unfold adjacentEvenCommonLowerEndpoint
            rw [hlower]
            rfl
          rw [hendpoint]
          unfold fusionChannelAmplitude
          change fusionPathMultiplicity cutoff [head, channel] =
            boolMultiplicity (decide (channel = head))
          rw [fusionPathMultiplicity_two,
            fusionOK_zero_output_eq_decide]
          simp [eq_comm]
      | cons second rest =>
          simp [hlower] at hlength

theorem adjacentEvenLowerLinkAmplitude_eq_indicator
    (K radius : Nat) (physical : Nat → Nat)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks radius)
    (channel : Nat) :
    adjacentEvenLowerLinkAmplitude K radius physical link channel =
      Q'.ofNat (boolMultiplicity (decide
        (channel = adjacentEvenCommonLowerEndpoint
          radius physical link))) := by
  unfold adjacentEvenLowerLinkAmplitude
  rw [adjacentEvenLowerChannelAmplitude_eq_indicator
    (linkAuxiliaryCutoff K) radius physical hlink channel]

#print axioms adjacentEvenFixedLink_lowerPlaquette_eq_backwardTemporal
#print axioms adjacentEvenFixedLink_lowerIds_length_le_one
#print axioms adjacentEvenLowerSpins_length_le_one
#print axioms adjacentEvenCommonLowerEndpoint_le
#print axioms adjacentEvenLowerChannelAmplitude_eq_indicator
#print axioms adjacentEvenLowerLinkAmplitude_eq_indicator

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenDeterministicLowerEndpoint
