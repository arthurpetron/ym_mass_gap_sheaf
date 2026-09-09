/-
# Attached spin-four endpoint lift up to the slab-boundary seam

An attached coarse endpoint carries one literal accepted global intertwiner
assignment.  The local SU(2) parity rule at every link therefore makes the
endpoint's odd-spin plaquette support a closed binary surface.  Combining
that surface with the global spin-zero-through-four XOR assembly produces a
canonical finite, duplicate-free, closed fine support with the exact dyadic
block count of every coarse spin.

Positive-boundary one-valent links force every nonzero accepted coarse face
to have the exact spatial margin needed by the pair bubbles.  Thus, at fine
cutoff one, this module discharges `PairBubbleSlabAdmissible`, constructs an
unconditional lift for every attached endpoint, and feeds that lift through
the existing positive raw-coverage compiler to make the finite unreachable
receiver mass exactly zero.  It does not assert an all-cutoff contraction or
a continuum, Osterwalder--Schrader, Hamiltonian, or Clay conclusion.

## Axiom gate

Finite list algebra, explicit accepted intertwiner witnesses, and audited
cellular geometry only.  No `Classical.*`, `sorry`, `native_decide`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
import YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier
import YMGap.Continuum.Z4DyadicSpinFourXorAssembly

namespace YMGap.Continuum.Z4DyadicSpinFourEndpointLift

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The attached coarse endpoint's odd-spin surface -/

def attachedEndpointCarrier (S : SlabScalePair) : List Z4Plaq :=
  boundaryCompleteSlabPlaquettes S.coarse.extent

def attachedEndpointSpin
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : Z4Plaq → Nat :=
  slabSpinAtPlaquette S.coarse.extent endpoint.1.1

def attachedEndpointOddSpinSupport
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : List Z4Plaq :=
  oddSpinSupport (attachedEndpointCarrier S)
    (attachedEndpointSpin S endpoint)

theorem attachedEndpointCarrier_nodup (S : SlabScalePair) :
    (attachedEndpointCarrier S).Nodup := by
  exact boundaryCompleteSlabPlaquettes_nodup S.coarse.extent

theorem attachedEndpointCarrier_self_subset
    (S : SlabScalePair) :
    ∀ plaquette, plaquette ∈ attachedEndpointCarrier S →
      plaquette ∈ boundaryCompleteSlabPlaquettes S.coarse.extent := by
  intro plaquette hmem
  exact hmem

private theorem slabBinaryOddSpinSupport_eq_mod_two_local
    {extent : Nat} {state : EdgeLabelling} {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    slabBinarySupportLabelling extent
        (oddSpinSupport
          (boundaryCompleteSlabPlaquettes extent)
          (slabSpinAtPlaquette extent state)) id =
      state id % 2 := by
  have hsupport :
      slabPlaquetteAt extent id ∈
          oddSpinSupport
            (boundaryCompleteSlabPlaquettes extent)
            (slabSpinAtPlaquette extent state) ↔
        state id % 2 = 1 := by
    unfold oddSpinSupport
    simp only [List.mem_filter, slabPlaquetteAt_mem hid,
      decide_eq_true_eq, true_and]
    rw [slabSpinAtPlaquette_slabPlaquetteAt extent state hid]
  rw [slabBinarySupportLabelling_eq_indicator hid]
  by_cases hodd : state id % 2 = 1
  · rw [if_pos (hsupport.mpr hodd), hodd]
  · rw [if_neg (fun hmem => hodd (hsupport.mp hmem))]
    have hlt : state id % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

private theorem oddSpinSupport_incidenceParity_local
    (extent : Nat) (state : EdgeLabelling) (link : Z4Link) :
    faceIncidenceCount link
          (oddSpinSupport
            (boundaryCompleteSlabPlaquettes extent)
            (slabSpinAtPlaquette extent state)) % 2 =
      localExternalSpinSum
          (slabIncidentPlaqIds extent link).length
          (externalSpinsOfList
            ((slabIncidentPlaqIds extent link).map state)) % 2 := by
  let support :=
    oddSpinSupport
      (boundaryCompleteSlabPlaquettes extent)
      (slabSpinAtPlaquette extent state)
  let binaryState := slabBinarySupportLabelling extent support
  have hbinarySum :=
    slabBinarySupport_localExternalSpinSum
      (support := support)
      (fun _ hmem => (List.mem_filter.mp hmem).1)
      (oddSpinSupport_nodup
        (boundaryCompleteSlabPlaquettes_nodup extent)
        (slabSpinAtPlaquette extent state)) link
  have hbinaryWord :=
    localExternalSpinSum_externalSpinsOfList_allCutoff
      ((slabIncidentPlaqIds extent link).map binaryState)
  have hstateWord :=
    localExternalSpinSum_externalSpinsOfList_allCutoff
      ((slabIncidentPlaqIds extent link).map state)
  simp only [List.length_map] at hbinaryWord hstateWord
  have hwordParity :
      natListSum
          ((slabIncidentPlaqIds extent link).map binaryState) % 2 =
        natListSum
          ((slabIncidentPlaqIds extent link).map state) % 2 := by
    apply natListSum_map_mod_two_congr binaryState state
    intro id hid
    unfold binaryState support
    rw [slabBinaryOddSpinSupport_eq_mod_two_local
      (slabIncidentPlaqId_physical hid)]
    exact Nat.mod_mod _ _
  calc
    faceIncidenceCount link
          (oddSpinSupport
            (boundaryCompleteSlabPlaquettes extent)
            (slabSpinAtPlaquette extent state)) % 2 =
        localExternalSpinSum
            (slabIncidentPlaqIds extent link).length
            (externalSpinsOfList
              ((slabIncidentPlaqIds extent link).map binaryState)) % 2 := by
      rw [hbinarySum]
    _ = natListSum
          ((slabIncidentPlaqIds extent link).map binaryState) % 2 := by
      rw [hbinaryWord]
    _ = natListSum
          ((slabIncidentPlaqIds extent link).map state) % 2 := hwordParity
    _ = localExternalSpinSum
          (slabIncidentPlaqIds extent link).length
          (externalSpinsOfList
            ((slabIncidentPlaqIds extent link).map state)) % 2 := by
      rw [hstateWord]

private theorem faceIncidenceCount_eq_zero_of_no_incidence_local
    (link : Z4Link) :
    ∀ support : List Z4Plaq,
      (∀ plaquette, plaquette ∈ support → link ∉ edgesOf plaquette) →
        faceIncidenceCount link support = 0
  | [], _ => rfl
  | head :: tail, hnone => by
      have hhead := hnone head List.mem_cons_self
      have htail : ∀ plaquette, plaquette ∈ tail →
          link ∉ edgesOf plaquette :=
        fun plaquette hmem =>
          hnone plaquette (List.mem_cons_of_mem head hmem)
      simp [faceIncidenceCount, hhead,
        faceIncidenceCount_eq_zero_of_no_incidence_local link tail htail]

/-- The accepted global coarse intertwiner assignment already carried by an
attached endpoint forces its odd-spin support to have even incidence. -/
theorem attachedEndpointOddSpinSupport_even
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse) :
    EvenFaceIncidence (attachedEndpointOddSpinSupport S endpoint) := by
  intro link
  by_cases hlink :
      link ∈ boundaryCompleteSlabLinks S.coarse.extent
  · have hassignment :=
      (mem_slabExpandedFineSources_iff.mp endpoint.2).2
    have hlocal :
        0 < slabExplicitLinkMultiplicity
          S.coarse.cutoff S.coarse.extent endpoint.1.1 link := by
      apply slabLinkMultiplicity_pos_of_globalAssignment
        S.coarse.cutoff S.coarse.extent endpoint.1.1
        (boundaryCompleteSlabLinks S.coarse.extent) endpoint.1.2
      · exact hassignment
      · exact hlink
    have hparity :=
      oddSpinSupport_incidenceParity_local
        S.coarse.extent endpoint.1.1 link
    have hnotOdd :
        faceIncidenceCount link
            (attachedEndpointOddSpinSupport S endpoint) % 2 ≠ 1 := by
      intro hodd
      apply Nat.ne_of_gt hlocal
      unfold slabExplicitLinkMultiplicity
      apply explicitValenceMultiplicity_eq_zero_of_odd_sum
      · simpa only [List.length_map] using
          slabIncidentPlaqIds_length_le_six S.coarse.extent link
      · rw [List.length_map, ← hparity]
        simpa only [attachedEndpointOddSpinSupport,
          attachedEndpointCarrier, attachedEndpointSpin] using hodd
    have hlt :
        faceIncidenceCount link
            (attachedEndpointOddSpinSupport S endpoint) % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    omega
  · rw [faceIncidenceCount_eq_zero_of_no_incidence_local]
    intro plaquette hmem hincident
    apply hlink
    exact (mem_boundaryCompleteSlabLinks_iff
      S.coarse.extent link).mpr
        ⟨plaquette,
          (List.mem_filter.mp hmem).1,
          hincident⟩

/-! ## 2. The exact spatial margin behind bubble containment -/

private theorem boundaryCompleteSlabPlaquette_not_at_x_succ
    {extent a b c d : Nat} {plane : Z4Plane}
    (ha : a = extent) :
    ((a + 1, b, c, d), plane) ∉
      boundaryCompleteSlabPlaquettes extent := by
  intro hface
  have hbox :=
    ((mem_boundaryCompleteSlabPlaquettes extent _).mp hface).1
  rw [mem_boxPlaquettes] at hbox
  have hx : a + 1 < extent + 1 := hbox.1
  rw [ha] at hx
  exact Nat.lt_irrefl _ hx

private theorem boundaryCompleteSlabPlaquette_not_at_y_succ
    {extent a b c d : Nat} {plane : Z4Plane}
    (hb : b = extent) :
    ((a, b + 1, c, d), plane) ∉
      boundaryCompleteSlabPlaquettes extent := by
  intro hface
  have hbox :=
    ((mem_boundaryCompleteSlabPlaquettes extent _).mp hface).1
  rw [mem_boxPlaquettes] at hbox
  have hy : b + 1 < extent + 1 := hbox.2.1
  rw [hb] at hy
  exact Nat.lt_irrefl _ hy

private theorem boundaryCompleteSlabPlaquette_not_at_z_succ
    {extent a b c d : Nat} {plane : Z4Plane}
    (hc : c = extent) :
    ((a, b, c + 1, d), plane) ∉
      boundaryCompleteSlabPlaquettes extent := by
  intro hface
  have hbox :=
    ((mem_boundaryCompleteSlabPlaquettes extent _).mp hface).1
  rw [mem_boxPlaquettes] at hbox
  have hz : c + 1 < extent + 1 := hbox.2.2.1
  rw [hc] at hz
  exact Nat.lt_irrefl _ hz

private theorem xBoundary_incident_unique
    {extent a b c d : Nat} (ha : a = extent)
    (direction : Dir4) (hdirection : direction ≠ .x0)
    {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent)
    (hincident : ((a + 1, b, c, d), direction) ∈ edgesOf face) :
    face = ((a, b, c, d), planeOf direction .x0) := by
  have hcandidates :=
    edge_complete face (a + 1, b, c, d) direction hincident
  cases direction with
  | x0 => exact (hdirection rfl).elim
  | x1 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
  | x2 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
  | x3 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_x_succ ha hface).elim

private theorem yBoundary_incident_unique
    {extent a b c d : Nat} (hb : b = extent)
    (direction : Dir4) (hdirection : direction ≠ .x1)
    {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent)
    (hincident : ((a, b + 1, c, d), direction) ∈ edgesOf face) :
    face = ((a, b, c, d), planeOf direction .x1) := by
  have hcandidates :=
    edge_complete face (a, b + 1, c, d) direction hincident
  cases direction with
  | x0 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
  | x1 => exact (hdirection rfl).elim
  | x2 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
  | x3 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_y_succ hb hface).elim

private theorem zBoundary_incident_unique
    {extent a b c d : Nat} (hc : c = extent)
    (direction : Dir4) (hdirection : direction ≠ .x2)
    {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent)
    (hincident : ((a, b, c + 1, d), direction) ∈ edgesOf face) :
    face = ((a, b, c, d), planeOf direction .x2) := by
  have hcandidates :=
    edge_complete face (a, b, c + 1, d) direction hincident
  cases direction with
  | x0 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
  | x1 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · exact h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
  | x2 => exact (hdirection rfl).elim
  | x3 =>
      simp only [edgePlaqs, planeOf, subE, List.mem_cons,
        List.not_mem_nil, or_false, Nat.add_sub_cancel] at hcandidates
      rcases hcandidates with h | h | h | h | h | h
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · subst face
        exact (boundaryCompleteSlabPlaquette_not_at_z_succ hc hface).elim
      · exact h

private theorem list_eq_singleton_of_nodup_mem_unique
    {A : Type} {entries : List A} {target : A}
    (hnodup : entries.Nodup) (htarget : target ∈ entries)
    (hunique : ∀ entry, entry ∈ entries → entry = target) :
    entries = [target] := by
  cases entries with
  | nil => cases htarget
  | cons head tail =>
      have hhead := hunique head List.mem_cons_self
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          have hnext := hunique next
            (List.mem_cons_of_mem target List.mem_cons_self)
          subst next
          exact ((List.nodup_cons.mp hnodup).1 List.mem_cons_self).elim

private theorem attachedEndpointSpin_eq_zero_of_unique_incident
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {coarse : Z4Plaq} {link : Z4Link}
    (hcoarse : coarse ∈ boundaryCompleteSlabPlaquettes S.coarse.extent)
    (hincident : link ∈ edgesOf coarse)
    (hunique : ∀ face,
      face ∈ boundaryCompleteSlabPlaquettes S.coarse.extent →
      link ∈ edgesOf face → face = coarse) :
    attachedEndpointSpin S endpoint coarse = 0 := by
  let targetId := listIndexOf coarse
    (boundaryCompleteSlabPlaquettes S.coarse.extent)
  have htargetPhysical :
      targetId ∈ slabPhysicalFaceEdges S.coarse.extent := by
    unfold targetId slabPhysicalFaceEdges
    exact List.mem_range.mpr
      (listIndexOf_lt_of_mem coarse
        (boundaryCompleteSlabPlaquettes S.coarse.extent) hcoarse)
  have htargetAt :
      slabPlaquetteAt S.coarse.extent targetId = coarse := by
    unfold slabPlaquetteAt targetId
    exact getD_listIndexOf_of_mem fallbackPlaquette coarse
      (boundaryCompleteSlabPlaquettes S.coarse.extent) hcoarse
  have htargetIncident :
      targetId ∈ slabIncidentPlaqIds S.coarse.extent link := by
    apply mem_slabIncidentPlaqIds.mpr
    have hindexed := slabPlaquetteAt_mem_enumerate htargetPhysical
    rw [htargetAt] at hindexed
    exact ⟨coarse, hindexed, hincident⟩
  have hincidentSingleton :
      slabIncidentPlaqIds S.coarse.extent link = [targetId] := by
    apply list_eq_singleton_of_nodup_mem_unique
      (slabIncidentPlaqIds_nodup S.coarse.extent link)
      htargetIncident
    intro id hid
    have hidPhysical := slabIncidentPlaqId_physical hid
    have hidAt := slabPlaquetteAt_mem hidPhysical
    have hidEdge :
        link ∈ edgesOf (slabPlaquetteAt S.coarse.extent id) := by
      obtain ⟨face, hindexed, hedge⟩ :=
        (mem_slabIncidentPlaqIds.mp hid)
      have hlookup : slabPlaquetteAt S.coarse.extent id = face := by
        unfold slabPlaquetteAt
        exact enumerate_getD_of_mem fallbackPlaquette hindexed
      simpa only [hlookup] using hedge
    apply slabPlaquetteAt_injective_on_physical hidPhysical htargetPhysical
    exact (hunique _ hidAt hidEdge).trans htargetAt.symm
  have hlink :
      link ∈ boundaryCompleteSlabLinks S.coarse.extent :=
    (mem_boundaryCompleteSlabLinks_iff S.coarse.extent link).mpr
      ⟨coarse, hcoarse, hincident⟩
  have hassignment := (mem_slabExpandedFineSources_iff.mp endpoint.2).2
  have hlocal :
      0 < slabExplicitLinkMultiplicity
        S.coarse.cutoff S.coarse.extent endpoint.1.1 link := by
    exact slabLinkMultiplicity_pos_of_globalAssignment
      S.coarse.cutoff S.coarse.extent endpoint.1.1
      (boundaryCompleteSlabLinks S.coarse.extent) endpoint.1.2
      hassignment link hlink
  have hzero : endpoint.1.1 targetId = 0 := by
    apply (explicitValenceMultiplicity_singleton_pos_iff_zero
      (linkAuxiliaryCutoff S.coarse.cutoff)
      (endpoint.1.1 targetId)).mp
    simpa only [slabExplicitLinkMultiplicity, hincidentSingleton,
      List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      using hlocal
  unfold attachedEndpointSpin
  rw [slabSpinAtPlaquette_eq_of_mem hcoarse]
  exact hzero

private theorem selectedSpin_two_three_four_ne_zero
    {spin : Nat} (hselected : spin = 2 ∨ spin = 3 ∨ spin = 4) :
    spin ≠ 0 := by
  intro hzero
  rcases hselected with htwo | hthree | hfour
  · rw [hzero] at htwo
    cases htwo
  · rw [hzero] at hthree
    cases hthree
  · rw [hzero] at hfour
    cases hfour

private theorem attachedEndpoint_p01_spin_zero_of_x_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p01) ∈ attachedEndpointCarrier S)
    (ha : a = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p01) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a + 1, b, c, d), .x1)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (xBoundary_incident_unique ha .x1 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p01_spin_zero_of_y_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p01) ∈ attachedEndpointCarrier S)
    (hb : b = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p01) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a, b + 1, c, d), .x0)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (yBoundary_incident_unique hb .x0 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p02_spin_zero_of_x_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p02) ∈ attachedEndpointCarrier S)
    (ha : a = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p02) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a + 1, b, c, d), .x2)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (xBoundary_incident_unique ha .x2 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p02_spin_zero_of_z_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p02) ∈ attachedEndpointCarrier S)
    (hc : c = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p02) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a, b, c + 1, d), .x0)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (zBoundary_incident_unique hc .x0 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p03_spin_zero_of_x_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p03) ∈ attachedEndpointCarrier S)
    (ha : a = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p03) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a + 1, b, c, d), .x3)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (xBoundary_incident_unique ha .x3 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p12_spin_zero_of_y_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p12) ∈ attachedEndpointCarrier S)
    (hb : b = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p12) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a, b + 1, c, d), .x2)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (yBoundary_incident_unique hb .x2 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p12_spin_zero_of_z_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p12) ∈ attachedEndpointCarrier S)
    (hc : c = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p12) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a, b, c + 1, d), .x1)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (zBoundary_incident_unique hc .x1 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p13_spin_zero_of_y_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p13) ∈ attachedEndpointCarrier S)
    (hb : b = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p13) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a, b + 1, c, d), .x3)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (yBoundary_incident_unique hb .x3 (by decide) hface hfaceEdge)

private theorem attachedEndpoint_p23_spin_zero_of_z_boundary
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    {a b c d : Nat}
    (hcoarse : ((a, b, c, d), .p23) ∈ attachedEndpointCarrier S)
    (hc : c = S.coarse.extent) :
    attachedEndpointSpin S endpoint ((a, b, c, d), .p23) = 0 := by
  apply attachedEndpointSpin_eq_zero_of_unique_incident
    (link := ((a, b, c + 1, d), .x3)) endpoint hcoarse
  · apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  · intro face hface hfaceEdge
    simpa only [planeOf] using
      (zBoundary_incident_unique hc .x3 (by decide) hface hfaceEdge)

/-- A coarse face has one positive-coordinate unit of room along each of its
own spatial directions.  Temporal directions need no extra field here: the
coarse corrected-slab time condition already supplies the fine-scale room. -/
def pairBubbleCoarseMargin (extent : Nat) : Z4Plaq → Prop
  | ((a, b, _, _), .p01) => a < extent ∧ b < extent
  | ((a, _, c, _), .p02) => a < extent ∧ c < extent
  | ((a, _, _, _), .p03) => a < extent
  | ((_, b, c, _), .p12) => b < extent ∧ c < extent
  | ((_, b, _, _), .p13) => b < extent
  | ((_, _, c, _), .p23) => c < extent

/-- Only spins selecting a pair bubble need the spatial margin. -/
def SelectedPairBubbleCoarseMargin
    (extent : Nat) (carrier : List Z4Plaq)
    (spin : Z4Plaq → Nat) : Prop :=
  ∀ coarse, coarse ∈ carrier →
    (spin coarse = 2 ∨ spin coarse = 3 ∨ spin coarse = 4) →
      pairBubbleCoarseMargin extent coarse

/-- Every selected spin-two-through-four face of an accepted endpoint lies
strictly inside each spatial direction of that face.  At a positive spatial
boundary, a displayed far edge is incident on that face alone; positivity of
the endpoint's accepted local intertwiner therefore invokes the one-valent
SU(2) vacuum rule and forces the face spin to zero, contradicting selection. -/
theorem attachedEndpointSelectedPairBubbleCoarseMargin
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse) :
    SelectedPairBubbleCoarseMargin
      S.coarse.extent (attachedEndpointCarrier S)
      (attachedEndpointSpin S endpoint) := by
  intro coarse hcoarse hselected
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  have hbox :=
    ((mem_boundaryCompleteSlabPlaquettes S.coarse.extent _).mp hcoarse).1
  rw [mem_boxPlaquettes] at hbox
  have ha : a ≤ S.coarse.extent :=
    Nat.le_of_lt_succ
      (by simpa only [Nat.succ_eq_add_one] using hbox.1)
  have hb : b ≤ S.coarse.extent :=
    Nat.le_of_lt_succ
      (by simpa only [Nat.succ_eq_add_one] using hbox.2.1)
  have hc : c ≤ S.coarse.extent :=
    Nat.le_of_lt_succ
      (by simpa only [Nat.succ_eq_add_one] using hbox.2.2.1)
  have hnonzero :
      attachedEndpointSpin S endpoint ((a, b, c, d), plane) ≠ 0 :=
    selectedSpin_two_three_four_ne_zero hselected
  cases plane with
  | p01 =>
      constructor
      · rcases Nat.lt_or_eq_of_le ha with haLt | haEq
        · exact haLt
        · exact (hnonzero
            (attachedEndpoint_p01_spin_zero_of_x_boundary
              endpoint hcoarse haEq)).elim
      · rcases Nat.lt_or_eq_of_le hb with hbLt | hbEq
        · exact hbLt
        · exact (hnonzero
            (attachedEndpoint_p01_spin_zero_of_y_boundary
              endpoint hcoarse hbEq)).elim
  | p02 =>
      constructor
      · rcases Nat.lt_or_eq_of_le ha with haLt | haEq
        · exact haLt
        · exact (hnonzero
            (attachedEndpoint_p02_spin_zero_of_x_boundary
              endpoint hcoarse haEq)).elim
      · rcases Nat.lt_or_eq_of_le hc with hcLt | hcEq
        · exact hcLt
        · exact (hnonzero
            (attachedEndpoint_p02_spin_zero_of_z_boundary
              endpoint hcoarse hcEq)).elim
  | p03 =>
      rcases Nat.lt_or_eq_of_le ha with haLt | haEq
      · exact haLt
      · exact (hnonzero
          (attachedEndpoint_p03_spin_zero_of_x_boundary
            endpoint hcoarse haEq)).elim
  | p12 =>
      constructor
      · rcases Nat.lt_or_eq_of_le hb with hbLt | hbEq
        · exact hbLt
        · exact (hnonzero
            (attachedEndpoint_p12_spin_zero_of_y_boundary
              endpoint hcoarse hbEq)).elim
      · rcases Nat.lt_or_eq_of_le hc with hcLt | hcEq
        · exact hcLt
        · exact (hnonzero
            (attachedEndpoint_p12_spin_zero_of_z_boundary
              endpoint hcoarse hcEq)).elim
  | p13 =>
      rcases Nat.lt_or_eq_of_le hb with hbLt | hbEq
      · exact hbLt
      · exact (hnonzero
          (attachedEndpoint_p13_spin_zero_of_y_boundary
            endpoint hcoarse hbEq)).elim
  | p23 =>
      rcases Nat.lt_or_eq_of_le hc with hcLt | hcEq
      · exact hcLt
      · exact (hnonzero
          (attachedEndpoint_p23_spin_zero_of_z_boundary
            endpoint hcoarse hcEq)).elim

private theorem twice_lt_fineBox_of_le
    {coordinate extent : Nat} (hcoordinate : coordinate ≤ extent) :
    2 * coordinate < 2 * extent + 1 + 1 := by
  calc
    2 * coordinate < 2 * extent + 1 :=
      Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 hcoordinate)
    _ < 2 * extent + 1 + 1 := Nat.lt_succ_self _

private theorem twice_add_one_lt_fineBox_of_le
    {coordinate extent : Nat} (hcoordinate : coordinate ≤ extent) :
    2 * coordinate + 1 < 2 * extent + 1 + 1 := by
  exact Nat.add_lt_add_right
    (Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 hcoordinate)) 1

private theorem twice_add_two_lt_fineBox_of_lt
    {coordinate extent : Nat} (hcoordinate : coordinate < extent) :
    2 * coordinate + 1 + 1 < 2 * extent + 1 + 1 := by
  have hscaled : 2 * (coordinate + 1) ≤ 2 * extent :=
    Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hcoordinate)
  calc
    2 * coordinate + 1 + 1 = 2 * (coordinate + 1) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ ≤ 2 * extent := hscaled
    _ < 2 * extent + 1 := Nat.lt_succ_self _
    _ < 2 * extent + 1 + 1 := Nat.lt_succ_self _

private theorem twice_le_fineTime_of_le
    {coordinate extent : Nat} (hcoordinate : coordinate ≤ extent) :
    2 * coordinate ≤ 2 * extent + 1 := by
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hcoordinate)
    (Nat.le_succ _)

private theorem twice_add_one_le_fineTime_of_le
    {coordinate extent : Nat} (hcoordinate : coordinate ≤ extent) :
    2 * coordinate + 1 ≤ 2 * extent + 1 := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcoordinate) 1

private theorem twice_add_one_lt_fineTime_of_lt
    {coordinate extent : Nat} (hcoordinate : coordinate < extent) :
    2 * coordinate + 1 < 2 * extent + 1 := by
  have hscaled : 2 * (coordinate + 1) ≤ 2 * extent :=
    Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hcoordinate)
  calc
    2 * coordinate + 1 < 2 * coordinate + 1 + 1 :=
      Nat.lt_succ_self _
    _ = 2 * (coordinate + 1) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ ≤ 2 * extent := hscaled
    _ < 2 * extent + 1 := Nat.lt_succ_self _

private theorem twice_add_two_le_fineTime_of_lt
    {coordinate extent : Nat} (hcoordinate : coordinate < extent) :
    2 * coordinate + 1 + 1 ≤ 2 * extent + 1 := by
  have hscaled : 2 * (coordinate + 1) ≤ 2 * extent :=
    Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hcoordinate)
  calc
    2 * coordinate + 1 + 1 = 2 * (coordinate + 1) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ ≤ 2 * extent := hscaled
    _ ≤ 2 * extent + 1 := Nat.le_succ _

/-- The simple positive-direction cube bubble stays in the doubled corrected
slab whenever its coarse target face has the exact spatial margin above. -/
theorem dyadicPairBubble_subset_boundaryCompleteFineSlab_of_margin
    {extent : Nat} {coarse fine : Z4Plaq} {upper : Bool}
    (hcoarse : coarse ∈ boundaryCompleteSlabPlaquettes extent)
    (hmargin : pairBubbleCoarseMargin extent coarse)
    (hfine : fine ∈ dyadicPairBubble coarse upper) :
    fine ∈ boundaryCompleteSlabPlaquettes
      (dyadicSlabFineExtent extent) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  have hparts :=
    (mem_boundaryCompleteSlabPlaquettes extent
      ((a, b, c, d), plane)).mp hcoarse
  have hbox := hparts.1
  have htime := hparts.2
  rw [mem_boxPlaquettes] at hbox
  change
    a < extent + 1 ∧ b < extent + 1 ∧
      c < extent + 1 ∧ d < extent + 1 at hbox
  rcases hbox with ⟨haBox, hbBox, hcBox, hdBox⟩
  have ha : a ≤ extent :=
    Nat.le_of_lt_succ (by simpa only [Nat.add_comm] using haBox)
  have hb : b ≤ extent :=
    Nat.le_of_lt_succ (by simpa only [Nat.add_comm] using hbBox)
  have hc : c ≤ extent :=
    Nat.le_of_lt_succ (by simpa only [Nat.add_comm] using hcBox)
  have hd : d ≤ extent :=
    Nat.le_of_lt_succ (by simpa only [Nat.add_comm] using hdBox)
  cases plane <;> cases upper <;>
    simp only [dyadicPairBubble, pairBubbleShape, pairBubbleOffset,
      unitCubeSurface, unitCube013Surface, unitCube023Surface,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hfine <;>
    simp only [plaquetteTimeAdmissible] at htime <;>
    simp only [pairBubbleCoarseMargin] at hmargin <;>
    rcases hfine with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply (mem_boundaryCompleteSlabPlaquettes
      (dyadicSlabFineExtent extent) _).mpr
    constructor
    · rw [mem_boxPlaquettes]
      simp only [axisShiftPlaquette, axisShiftVertex,
        dyadicSlabFineExtent, Bool.toNat_false, Bool.toNat_true,
        Nat.add_zero, Nat.zero_add, Nat.one_add, Nat.succ_eq_add_one]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
        | exact twice_lt_fineBox_of_le ha
        | exact twice_add_one_lt_fineBox_of_le ha
        | exact twice_add_two_lt_fineBox_of_lt hmargin
        | exact twice_add_two_lt_fineBox_of_lt hmargin.1
        | exact twice_add_two_lt_fineBox_of_lt hmargin.2
        | exact twice_lt_fineBox_of_le hb
        | exact twice_add_one_lt_fineBox_of_le hb
        | exact twice_add_two_lt_fineBox_of_lt hmargin
        | exact twice_add_two_lt_fineBox_of_lt hmargin.1
        | exact twice_add_two_lt_fineBox_of_lt hmargin.2
        | exact twice_lt_fineBox_of_le hc
        | exact twice_add_one_lt_fineBox_of_le hc
        | exact twice_add_two_lt_fineBox_of_lt hmargin
        | exact twice_add_two_lt_fineBox_of_lt hmargin.1
        | exact twice_add_two_lt_fineBox_of_lt hmargin.2
        | exact twice_lt_fineBox_of_le hd
        | exact twice_add_one_lt_fineBox_of_le hd
        | exact twice_add_two_lt_fineBox_of_lt htime
    · simp only [axisShiftPlaquette, axisShiftVertex,
        plaquetteTimeAdmissible, dyadicSlabFineExtent,
        Bool.toNat_false, Bool.toNat_true, Nat.add_zero, Nat.zero_add,
        Nat.one_add, Nat.succ_eq_add_one]
      first
      | exact twice_le_fineTime_of_le hd
      | exact twice_add_one_le_fineTime_of_le hd
      | exact twice_add_one_lt_fineTime_of_lt htime
      | exact twice_add_two_le_fineTime_of_lt htime

private theorem supportCoefficient_true_mem_local
    {support : List Z4Plaq} {face : Z4Plaq}
    (htrue : supportCoefficient support face = true) :
    face ∈ support := by
  unfold supportCoefficient at htrue
  exact of_decide_eq_true htrue

private theorem bool_or_of_xor_eq_true_local
    {left right : Bool} (htrue : (left ^^ right) = true) :
    left = true ∨ right = true := by
  cases left <;> cases right
  · cases htrue
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- The selected-spin margin discharges precisely the local containment
interface expected by the global XOR support. -/
theorem pairBubbleSlabAdmissible_of_selectedMargin
    {extent : Nat} {carrier : List Z4Plaq} {spin : Z4Plaq → Nat}
    (hcarrier : ∀ coarse, coarse ∈ carrier →
      coarse ∈ boundaryCompleteSlabPlaquettes extent)
    (hmargin : SelectedPairBubbleCoarseMargin extent carrier spin) :
    PairBubbleSlabAdmissible
      (dyadicSlabFineExtent extent) carrier spin := by
  intro coarse hcoarse fine hselected
  by_cases htwo : spin coarse = 2
  · have hfine : fine ∈ dyadicPairBubble coarse false := by
      unfold localPairBubbleCoefficient at hselected
      rw [if_pos htwo] at hselected
      exact supportCoefficient_true_mem_local hselected
    exact dyadicPairBubble_subset_boundaryCompleteFineSlab_of_margin
      (hcarrier coarse hcoarse)
      (hmargin coarse hcoarse (Or.inl htwo)) hfine
  · unfold localPairBubbleCoefficient at hselected
    rw [if_neg htwo] at hselected
    by_cases hthree : spin coarse = 3
    · rw [if_pos hthree] at hselected
      exact dyadicPairBubble_subset_boundaryCompleteFineSlab_of_margin
        (hcarrier coarse hcoarse)
        (hmargin coarse hcoarse (Or.inr (Or.inl hthree)))
        (supportCoefficient_true_mem_local hselected)
    · rw [if_neg hthree] at hselected
      by_cases hfour : spin coarse = 4
      · rw [if_pos hfour] at hselected
        have hcoarseMargin :=
          hmargin coarse hcoarse (Or.inr (Or.inr hfour))
        rcases bool_or_of_xor_eq_true_local hselected with
            hlower | hupper
        · exact dyadicPairBubble_subset_boundaryCompleteFineSlab_of_margin
            (hcarrier coarse hcoarse) hcoarseMargin
            (supportCoefficient_true_mem_local hlower)
        · exact dyadicPairBubble_subset_boundaryCompleteFineSlab_of_margin
            (hcarrier coarse hcoarse) hcoarseMargin
            (supportCoefficient_true_mem_local hupper)
      · rw [if_neg hfour] at hselected
        cases hselected

/-! ## 3. Exact endpoint lift conditional only on selected-bubble containment -/

private theorem slabSpinAtPlaquette_binarySupport_local
    {extent : Nat} {support : List Z4Plaq} {plaquette : Z4Plaq}
    (hsubset : ∀ face, face ∈ support →
      face ∈ boundaryCompleteSlabPlaquettes extent) :
    slabSpinAtPlaquette extent
        (slabBinarySupportLabelling extent support) plaquette =
      if plaquette ∈ support then 1 else 0 := by
  by_cases hslab : plaquette ∈ boundaryCompleteSlabPlaquettes extent
  · rw [slabSpinAtPlaquette_eq_of_mem hslab]
    have hindex :
        listIndexOf plaquette (boundaryCompleteSlabPlaquettes extent) ∈
          slabPhysicalFaceEdges extent := by
      unfold slabPhysicalFaceEdges
      exact List.mem_range.mpr
        (listIndexOf_lt_of_mem plaquette
          (boundaryCompleteSlabPlaquettes extent) hslab)
    rw [slabBinarySupportLabelling_eq_indicator hindex]
    have hlookup :
        slabPlaquetteAt extent
            (listIndexOf plaquette
              (boundaryCompleteSlabPlaquettes extent)) = plaquette := by
      unfold slabPlaquetteAt
      exact getD_listIndexOf_of_mem fallbackPlaquette plaquette
        (boundaryCompleteSlabPlaquettes extent) hslab
    rw [hlookup]
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    have hnotSupport : plaquette ∉ support := by
      intro hmem
      exact hslab (hsubset plaquette hmem)
    rw [if_neg hnotSupport]

private theorem wholeSlabFinePacket_supportCoefficient_local
    {S : SlabScalePair} {support : List Z4Plaq}
    (hsubset : ∀ fine, fine ∈ support →
      fine ∈ boundaryCompleteSlabPlaquettes S.fine.extent)
    (coarseFaceId : Nat) :
    wholeSlabFinePacket S
        (slabBinarySupportLabelling S.fine.extent support) coarseFaceId =
      dyadicFaceSpinPacket
        (fun fine => (supportCoefficient support fine).toNat)
        (slabPlaquetteAt S.coarse.extent coarseFaceId) := by
  have hspin :
      slabSpinAtPlaquette S.fine.extent
          (slabBinarySupportLabelling S.fine.extent support) =
        fun fine => (supportCoefficient support fine).toNat := by
    funext fine
    rw [slabSpinAtPlaquette_binarySupport_local hsubset]
    unfold supportCoefficient
    by_cases hmem : fine ∈ support <;> simp [hmem]
  unfold wholeSlabFinePacket
  rw [hspin]

/-- At fine cutoff one, the global spin-four XOR construction supplies the
exact endpoint lift as soon as its selected local bubbles obey the corrected
fine-slab boundary condition.  Odd-spin closure and all spin bounds are
derived from the attached endpoint itself. -/
def attachedEndpointSpinFourEvenBinarySupportLift
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hbubbles : PairBubbleSlabAdmissible
      S.fine.extent (attachedEndpointCarrier S)
      (attachedEndpointSpin S endpoint)) :
    EvenBinarySupportEndpointLift S endpoint := by
  let carrier := attachedEndpointCarrier S
  let spin := attachedEndpointSpin S endpoint
  let support := dyadicSpinFourSupport carrier spin
  have hcarrierNodup : carrier.Nodup := by
    exact attachedEndpointCarrier_nodup S
  have hcarrierSubset : ∀ coarse, coarse ∈ carrier →
      coarse ∈ boundaryCompleteSlabPlaquettes S.coarse.extent := by
    exact attachedEndpointCarrier_self_subset S
  have hbubblesDyadic : PairBubbleSlabAdmissible
      (dyadicSlabFineExtent S.coarse.extent) carrier spin := by
    rw [← S.fine_extent]
    exact hbubbles
  have hsupportSubset : ∀ fine, fine ∈ support →
      fine ∈ boundaryCompleteSlabPlaquettes S.fine.extent := by
    intro fine hmem
    rw [S.fine_extent]
    exact dyadicSpinFourSupport_subset_boundaryCompleteFineSlab
      hcarrierSubset hbubblesDyadic fine hmem
  have hsupportEven : EvenFaceIncidence support := by
    apply dyadicSpinFourSupport_evenFaceIncidence hcarrierNodup spin
    simpa only [carrier, spin, attachedEndpointOddSpinSupport,
      attachedEndpointCarrier, attachedEndpointSpin] using
        attachedEndpointOddSpinSupport_even endpoint
  refine
    { support := support
      support_subset := hsupportSubset
      support_nodup := dyadicSpinFourSupport_nodup carrier spin
      support_even := hsupportEven
      faceSpinTotal_eq := ?_ }
  intro coarseFaceId hface
  have hphysical :
      coarseFaceId ∈ slabPhysicalFaceEdges S.coarse.extent := by
    simpa only [SlabPhysicalData.faceEdges] using hface
  have hquery :
      slabPlaquetteAt S.coarse.extent coarseFaceId ∈ carrier := by
    exact slabPlaquetteAt_mem hphysical
  have hspinBound :
      spin (slabPlaquetteAt S.coarse.extent coarseFaceId) ≤ 4 := by
    have hbound :=
      SlabExpandedFineSourceEntry.physical_bounded
        endpoint coarseFaceId hface
    rw [S.coarse_cutoff, hfineCutoff] at hbound
    unfold spin attachedEndpointSpin
    rw [slabSpinAtPlaquette_slabPlaquetteAt
      S.coarse.extent endpoint.1.1 hphysical]
    omega
  rw [wholeSlabFinePacket_supportCoefficient_local hsupportSubset]
  have hpacket :=
    dyadicSpinFourSupport_faceSpinTotal
      hcarrierNodup spin hquery hspinBound
  unfold spin attachedEndpointSpin at hpacket
  rw [slabSpinAtPlaquette_slabPlaquetteAt
    S.coarse.extent endpoint.1.1 hphysical] at hpacket
  simpa only [support, endpointFaceSpinTotal, faceSpinPacketTotal] using
    hpacket

/-- Convenience form of the endpoint lift whose sole geometric input is the
explicit coarse spatial margin for faces with spins two, three, or four. -/
def attachedEndpointSpinFourEvenBinarySupportLiftOfMargin
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hmargin : SelectedPairBubbleCoarseMargin
      S.coarse.extent (attachedEndpointCarrier S)
      (attachedEndpointSpin S endpoint)) :
    EvenBinarySupportEndpointLift S endpoint := by
  apply attachedEndpointSpinFourEvenBinarySupportLift
    endpoint hfineCutoff
  have hadmissible := pairBubbleSlabAdmissible_of_selectedMargin
    (attachedEndpointCarrier_self_subset S) hmargin
  rw [← S.fine_extent] at hadmissible
  exact hadmissible

/-- At fine cutoff one, an attached accepted endpoint itself supplies every
remaining parity, margin, and local-containment premise of the finite
spin-zero-through-four dyadic support. -/
def attachedEndpointSpinFourEvenBinarySupportLiftOfAcceptedEndpoint
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1) :
    EvenBinarySupportEndpointLift S endpoint :=
  attachedEndpointSpinFourEvenBinarySupportLiftOfMargin endpoint hfineCutoff
    (attachedEndpointSelectedPairBubbleCoarseMargin endpoint)

/-! ## 4. Finite receiver coverage and zero unreachable mass -/

/-- Fine cutoff one now supplies the geometric endpoint coverage record for
every attached accepted coarse endpoint. -/
def attachedEndpointSpinFourEvenBinarySupportCoverage
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1) :
    EvenBinarySupportEndpointCoverage S where
  lift := fun endpoint =>
    attachedEndpointSpinFourEvenBinarySupportLiftOfAcceptedEndpoint
      endpoint hfineCutoff

/-- Positive fine and coarse couplings turn the geometric support coverage
into the exact positive raw endpoint coverage consumed by both receiver
columns. -/
def attachedEndpointSpinFourPositiveExpandedRawCoverage
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    PositiveExpandedRawEndpointCoverage S :=
  (((attachedEndpointSpinFourEvenBinarySupportCoverage S hfineCutoff).toFusionChannelCoverage).toPositiveExpandedCoverage
      hfineCutoff hfineCoupling).toFaceCompatibleCoverage
        hcoarseCoupling |>.toRawEndpointCoverage

/-- The concrete spin-zero-through-four construction covers both complete
finite receiver columns: its assignment-saturated unreachable mass is
exactly zero. -/
theorem attachedEndpointSpinFour_unreachableFullReceiverMass_eqv_zero
    (S : SlabScalePair) (root target : Nat)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
        S root target ≈ 0 :=
  actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_eqv_zero_of_endpointCoverage
    S root target
      (attachedEndpointSpinFourPositiveExpandedRawCoverage S hfineCutoff
        hfineCoupling hcoarseCoupling)

#print axioms attachedEndpointCarrier_nodup
#print axioms attachedEndpointOddSpinSupport_even
#print axioms xBoundary_incident_unique
#print axioms yBoundary_incident_unique
#print axioms zBoundary_incident_unique
#print axioms attachedEndpointSpin_eq_zero_of_unique_incident
#print axioms selectedSpin_two_three_four_ne_zero
#print axioms attachedEndpoint_p01_spin_zero_of_x_boundary
#print axioms attachedEndpoint_p01_spin_zero_of_y_boundary
#print axioms attachedEndpoint_p02_spin_zero_of_x_boundary
#print axioms attachedEndpoint_p02_spin_zero_of_z_boundary
#print axioms attachedEndpoint_p03_spin_zero_of_x_boundary
#print axioms attachedEndpoint_p12_spin_zero_of_y_boundary
#print axioms attachedEndpoint_p12_spin_zero_of_z_boundary
#print axioms attachedEndpoint_p13_spin_zero_of_y_boundary
#print axioms attachedEndpoint_p23_spin_zero_of_z_boundary
#print axioms attachedEndpointSelectedPairBubbleCoarseMargin
#print axioms dyadicPairBubble_subset_boundaryCompleteFineSlab_of_margin
#print axioms pairBubbleSlabAdmissible_of_selectedMargin
#print axioms attachedEndpointSpinFourEvenBinarySupportLift
#print axioms attachedEndpointSpinFourEvenBinarySupportLiftOfMargin
#print axioms attachedEndpointSpinFourEvenBinarySupportLiftOfAcceptedEndpoint
#print axioms attachedEndpointSpinFourEvenBinarySupportCoverage
#print axioms attachedEndpointSpinFourPositiveExpandedRawCoverage
#print axioms attachedEndpointSpinFour_unreachableFullReceiverMass_eqv_zero

end YMGap.Continuum.Z4DyadicSpinFourEndpointLift
