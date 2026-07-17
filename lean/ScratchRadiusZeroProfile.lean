import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSupportGeneric

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

private theorem adjacentEvenLinkSide_zero_fixed_time
    (a b c t : Nat) (direction : Dir4)
    (hfixed : adjacentEvenLinkSide 0 ((a, b, c, t), direction) =
      .fixed) : t = 1 := by
  by_cases heq : t = 1
  · exact heq
  · exfalso
    cases direction <;> by_cases hlt : t < 1 <;>
      simp [adjacentEvenLinkSide, adjacentEvenSpatialSide,
        adjacentEvenTemporalSide, adjacentEvenCenter, hlt, heq] at hfixed

private theorem adjacentEvenPlaquetteSide_zero_lower_time
    (a b c t : Nat) (plane : Z4Plane)
    (hlower : adjacentEvenPlaquetteSide 0 ((a, b, c, t), plane) =
      .lower) : t = 0 := by
  by_cases heq : t = 0
  · exact heq
  · have hnotlt : ¬ t < 1 := by omega
    exfalso
    cases plane <;> by_cases hone : t = 1 <;>
      simp [adjacentEvenPlaquetteSide, adjacentEvenSpatialSide,
        adjacentEvenTemporalSide, adjacentEvenCenter, hnotlt, hone] at hlower

theorem radiusZeroLowerIncidentLookup_unique
    {link : Z4Link}
    (hfixed : adjacentEvenLinkSide 0 link = .fixed)
    {left right : Nat}
    (hleft : left ∈ (adjacentEvenIncidentFaceIdParts 0 link).1)
    (hright : right ∈ (adjacentEvenIncidentFaceIdParts 0 link).1) :
    slabPlaquetteAt (adjacentEvenExtent 0) left =
      slabPlaquetteAt (adjacentEvenExtent 0) right := by
  have hleftParts := (mem_partitionBySide_lower
    (fun id => adjacentEvenPlaquetteSide 0
      (slabPlaquetteAt (adjacentEvenExtent 0) id))
    left (slabIncidentPlaqIds (adjacentEvenExtent 0) link)).mp hleft
  have hrightParts := (mem_partitionBySide_lower
    (fun id => adjacentEvenPlaquetteSide 0
      (slabPlaquetteAt (adjacentEvenExtent 0) id))
    right (slabIncidentPlaqIds (adjacentEvenExtent 0) link)).mp hright
  have hleftSide := hleftParts.2
  have hrightSide := hrightParts.2
  have hleftEdge : link ∈ edgesOf
      (slabPlaquetteAt (adjacentEvenExtent 0) left) := by
    obtain ⟨plaquette, hindexed, hedge⟩ :=
      mem_slabIncidentPlaqIds.mp hleftParts.1
    have hlookup : slabPlaquetteAt (adjacentEvenExtent 0) left =
        plaquette := by
      unfold slabPlaquetteAt
      exact enumerate_getD_of_mem fallbackPlaquette hindexed
    simpa only [hlookup] using hedge
  have hrightEdge : link ∈ edgesOf
      (slabPlaquetteAt (adjacentEvenExtent 0) right) := by
    obtain ⟨plaquette, hindexed, hedge⟩ :=
      mem_slabIncidentPlaqIds.mp hrightParts.1
    have hlookup : slabPlaquetteAt (adjacentEvenExtent 0) right =
        plaquette := by
      unfold slabPlaquetteAt
      exact enumerate_getD_of_mem fallbackPlaquette hindexed
    simpa only [hlookup] using hedge
  let leftPlaq := slabPlaquetteAt (adjacentEvenExtent 0) left
  let rightPlaq := slabPlaquetteAt (adjacentEvenExtent 0) right
  change leftPlaq = rightPlaq
  change adjacentEvenPlaquetteSide 0 leftPlaq = .lower at hleftSide
  change adjacentEvenPlaquetteSide 0 rightPlaq = .lower at hrightSide
  change link ∈ edgesOf leftPlaq at hleftEdge
  change link ∈ edgesOf rightPlaq at hrightEdge
  obtain ⟨⟨a, b, c, t⟩, direction⟩ := link
  obtain ⟨⟨la, lb, lc, lt⟩, leftPlane⟩ := leftPlaq
  obtain ⟨⟨ra, rb, rc, rt⟩, rightPlane⟩ := rightPlaq
  have htime := adjacentEvenLinkSide_zero_fixed_time
    a b c t direction hfixed
  have hleftTime := adjacentEvenPlaquetteSide_zero_lower_time
    la lb lc lt leftPlane hleftSide
  have hrightTime := adjacentEvenPlaquetteSide_zero_lower_time
    ra rb rc rt rightPlane hrightSide
  cases direction <;> cases leftPlane <;> cases rightPlane
  all_goals
    simp [edgesOf, dirsOf, addE] at hleftEdge hrightEdge ⊢ <;>
      omega

theorem radiusZeroFixedLink_lowerIds_length_le_one
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks 0) :
    (adjacentEvenIncidentFaceIdParts 0 link).1.length ≤ 1 := by
  change link ∈
    YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini.adjacentEvenFixedSlabLinks 0 at hlink
  have hfixed :=
    (YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini.mem_adjacentEvenFixedSlabLinks.mp hlink).2
  let ids := (adjacentEvenIncidentFaceIdParts 0 link).1
  change ids.length ≤ 1
  have hfull := slabIncidentPlaqIds_nodup
    (adjacentEvenExtent 0) link
  have hall :
      ((adjacentEvenIncidentFaceIdParts 0 link).1 ++
        (adjacentEvenIncidentFaceIdParts 0 link).2.1 ++
        (adjacentEvenIncidentFaceIdParts 0 link).2.2).Nodup :=
    (partitionBySide_perm
      (fun id => adjacentEvenPlaquetteSide 0
        (slabPlaquetteAt (adjacentEvenExtent 0) id))
      (slabIncidentPlaqIds (adjacentEvenExtent 0) link)).symm.nodup
        hfull
  have hnodup : ids.Nodup := by
    have houter := List.nodup_append.mp hall
    have hlowerFixed := List.nodup_append.mp houter.1
    exact hlowerFixed.1
  cases hids : ids with
  | nil => simp
  | cons head tail =>
      cases htail : tail with
      | nil => simp
      | cons second rest =>
          have hhead : head ∈
              (adjacentEvenIncidentFaceIdParts 0 link).1 := by
            change head ∈ ids
            rw [hids]
            exact List.mem_cons_self
          have hsecond : second ∈
              (adjacentEvenIncidentFaceIdParts 0 link).1 := by
            change second ∈ ids
            rw [hids, htail]
            simp
          have hlookup := radiusZeroLowerIncidentLookup_unique
            hfixed hhead hsecond
          have hheadIncident := (mem_partitionBySide_lower
            (fun id => adjacentEvenPlaquetteSide 0
              (slabPlaquetteAt (adjacentEvenExtent 0) id))
            head (slabIncidentPlaqIds (adjacentEvenExtent 0) link)).mp hhead
          have hsecondIncident := (mem_partitionBySide_lower
            (fun id => adjacentEvenPlaquetteSide 0
              (slabPlaquetteAt (adjacentEvenExtent 0) id))
            second (slabIncidentPlaqIds (adjacentEvenExtent 0) link)).mp hsecond
          have heq : head = second :=
            slabPlaquetteAt_injective_on_physical
              (slabIncidentPlaqId_physical hheadIncident.1)
              (slabIncidentPlaqId_physical hsecondIncident.1)
              hlookup
          subst second
          rw [hids, htail] at hnodup
          simp at hnodup
