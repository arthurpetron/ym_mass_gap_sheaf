/-
# Exact annihilation outside the cutoff-one vacuum-column support

For a cutoff-one source with vacuum fixed and reflected-upper data, any
nonclosed assembled binary surface has odd incidence at an actual slab link.
This file connects the 116-block closure certificate to the production local
SU(2) multiplicity, proves that the offending link lies in the lower factor,
and concludes that the genuine central half amplitude is zero.

The only finite table is the equality between each block's bit-incidence list
and the production `slabIncidentPlaqIds` list.  Lean checks all 116 entries and
then uses the equality in a symbolic proof for arbitrary bounded sources.
No external calculation is trusted by the theorem.

This remains a finite `K = 1`, half-extent-zero statement.  No
cutoff-uniform, volume-uniform, or continuum conclusion is asserted.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnSupport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnSupport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The 116 block-to-link incidence certificate -/

/-- Face identifiers selected by the literal 72-bit incidence row of one
quaternion link block. -/
def cutoffOneBlockIncidentFaceIds (block : Nat) : List Nat :=
  (List.range 72).filter fun faceId =>
    (slabEdgeFaceIncidenceMask block).testBit faceId

/-- Executable comparison of every bit-incidence row with the production
link-incidence list. -/
def cutoffOneBlockIncidentFaceIdsCheck : Bool :=
  (List.range 116).all fun block =>
    decide
      (cutoffOneBlockIncidentFaceIds block =
        slabIncidentPlaqIds 1 (correctedSlabLinkAt 1 block))

/-- Kernel evaluation of all 116 exact list equalities. -/
theorem cutoffOneBlockIncidentFaceIdsCheck_true :
    cutoffOneBlockIncidentFaceIdsCheck = true := by
  decide

/-- Semantic projection of the checked 116-entry table. -/
theorem cutoffOneBlockIncidentFaceIds_eq
    {block : Nat} (hblock : block < 116) :
    cutoffOneBlockIncidentFaceIds block =
      slabIncidentPlaqIds 1 (correctedSlabLinkAt 1 block) := by
  exact of_decide_eq_true
    (List.all_eq_true.mp cutoffOneBlockIncidentFaceIdsCheck_true
      block (List.mem_range.mpr hblock))

/-! ## 2. Selected degree equals the production incident-spin sum -/

theorem natListSum_map_binary_eq_filter_length
    (value : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → value id ≤ 1) →
      natListSum (ids.map value) =
        (ids.filter fun id => decide (value id = 1)).length
  | [], _ => rfl
  | head :: tail, hvalue => by
      have hhead : value head = 0 ∨ value head = 1 := by
        have := hvalue head List.mem_cons_self
        omega
      have htail := natListSum_map_binary_eq_filter_length value tail
        (fun id hid => hvalue id (List.mem_cons_of_mem head hid))
      rcases hhead with hzero | hone
      · simp [natListSum, hzero, htail]
      · simp [natListSum, hone, htail, Nat.add_comm]

theorem cutoffOneBlockIncidentSelected_length
    (block : Nat) (physical : EdgeLabelling) :
    ((cutoffOneBlockIncidentFaceIds block).filter fun faceId =>
        decide (physical faceId = 1)).length =
      slabMaskIntersectionCount
        (slabEdgeFaceIncidenceMask block)
        (cutoffOneSlabMask physical) := by
  unfold cutoffOneBlockIncidentFaceIds slabMaskIntersectionCount
  rw [List.filter_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro faceId hfaceId
  rw [cutoffOneSlabMask_testBit physical faceId
    (List.mem_range.mp hfaceId)]
  exact Bool.and_comm _ _

/-- The algebraic selected degree used by the exact Haar proof is exactly the
sum of the spins passed to the production local fusion multiplicity. -/
theorem cutoffOneLinkSpinSum_eq_selectedDegree
    (block : Nat) (hblock : block < 116)
    (physical : EdgeLabelling)
    (hlabel : ∀ id, physical id ≤ 1) :
    natListSum
        ((slabIncidentPlaqIds 1
          (correctedSlabLinkAt 1 block)).map physical) =
      cutoffOneSlabSelectedBlockDegree block physical := by
  calc
    natListSum
        ((slabIncidentPlaqIds 1
          (correctedSlabLinkAt 1 block)).map physical) =
        natListSum
          ((cutoffOneBlockIncidentFaceIds block).map physical) := by
      rw [cutoffOneBlockIncidentFaceIds_eq hblock]
    _ = ((cutoffOneBlockIncidentFaceIds block).filter fun faceId =>
          decide (physical faceId = 1)).length :=
      natListSum_map_binary_eq_filter_length physical _
        (fun id _ => hlabel id)
    _ = slabMaskIntersectionCount
          (slabEdgeFaceIncidenceMask block)
          (cutoffOneSlabMask physical) :=
      cutoffOneBlockIncidentSelected_length block physical
    _ = cutoffOneSlabSelectedBlockDegree block physical :=
      (cutoffOneSlabSelectedBlockDegree_eq_maskIntersectionCount
        block hblock physical hlabel).symm

theorem natListSum_map_pos_witness
    (value : Nat → Nat) : ∀ ids : List Nat,
    0 < natListSum (ids.map value) →
      ∃ id, id ∈ ids ∧ 0 < value id
  | [], hpos => by
      simp [natListSum] at hpos
  | head :: tail, hpos => by
      simp only [List.map_cons, natListSum] at hpos
      by_cases hhead : 0 < value head
      · exact ⟨head, List.mem_cons_self, hhead⟩
      · have htail : 0 < natListSum (tail.map value) := by omega
        obtain ⟨id, hid, hpositive⟩ :=
          natListSum_map_pos_witness value tail htail
        exact ⟨id, List.mem_cons_of_mem head hid, hpositive⟩

/-! ## 3. An odd block in a lower-only assembly is a lower link -/

theorem assembledSource_nonzero_mem_lower
    (source : EdgeLabelling) {faceId : Nat}
    (hfaceId : faceId ∈ slabPhysicalFaceEdges 1)
    (hnonzero :
      assembleReflectedSlabLabelling 0 source
        zeroEdgeLabelling zeroEdgeLabelling faceId ≠ 0) :
    faceId ∈ centralLowerFaceIds 0 := by
  cases hside : plaquetteHalfSide 0 (slabPlaquetteAt 1 faceId)
  · exact mem_centralLowerFaceIds.mpr ⟨hfaceId, hside⟩
  · exfalso
    apply hnonzero
    rw [assembleReflectedSlabLabelling_fixed hfaceId hside]
    rfl
  · exfalso
    apply hnonzero
    rw [assembleReflectedSlabLabelling_upper hfaceId hside]
    rfl

theorem correctedSlabLinkAt_mem_lower_of_assembled_odd
    (source : EdgeLabelling) (block : Nat) (hblock : block < 116)
    (hlabel : ∀ id,
      assembleReflectedSlabLabelling 0 source
        zeroEdgeLabelling zeroEdgeLabelling id ≤ 1)
    (hodd :
      cutoffOneSlabSelectedBlockDegree block
        (assembleReflectedSlabLabelling 0 source
          zeroEdgeLabelling zeroEdgeLabelling) % 2 = 1) :
    correctedSlabLinkAt 1 block ∈ centralLowerLinks 0 := by
  let physical := assembleReflectedSlabLabelling 0 source
    zeroEdgeLabelling zeroEdgeLabelling
  let link := correctedSlabLinkAt 1 block
  have hsum :
      natListSum ((slabIncidentPlaqIds 1 link).map physical) =
        cutoffOneSlabSelectedBlockDegree block physical := by
    exact cutoffOneLinkSpinSum_eq_selectedDegree block hblock physical hlabel
  have hsumPos :
      0 < natListSum ((slabIncidentPlaqIds 1 link).map physical) := by
    rw [hsum]
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at hodd
    cases hodd
  obtain ⟨faceId, hfaceIncident, hfacePositive⟩ :=
    natListSum_map_pos_witness physical
      (slabIncidentPlaqIds 1 link) hsumPos
  have hfacePhysical : faceId ∈ slabPhysicalFaceEdges 1 :=
    slabIncidentPlaqId_physical hfaceIncident
  have hfaceLower : faceId ∈ centralLowerFaceIds 0 :=
    assembledSource_nonzero_mem_lower source hfacePhysical
      (Nat.ne_of_gt hfacePositive)
  have hblockMem : block ∈ correctedSlabLinkBlocks 1 := by
    unfold correctedSlabLinkBlocks
    rw [correctedSlabLinks_extent_one_length]
    exact List.mem_range.mpr hblock
  have hlinkPhysical : link ∈ boundaryCompleteSlabLinks 1 :=
    correctedSlabLinkAt_mem hblockMem
  obtain ⟨face, hindexed, hincidence⟩ :=
    (mem_slabIncidentPlaqIds.mp hfaceIncident)
  have hfaceLookup : slabPlaquetteAt 1 faceId = face := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  have hfaceSide : plaquetteHalfSide 0 face = .lower := by
    rw [← hfaceLookup]
    exact (mem_centralLowerFaceIds.mp hfaceLower).2
  apply mem_centralLowerLinks.mpr
  refine ⟨hlinkPhysical, ?_⟩
  cases hlinkSide : linkHalfSide 0 link
  · rfl
  · have hfixed := fixed_link_incident_face_fixed hlinkSide hincidence
    rw [hfaceSide] at hfixed
    cases hfixed
  · exact False.elim
      ((upper_link_incident_face_ne_lower hlinkSide hincidence) hfaceSide)

/-! ## 4. Odd local incidence annihilates the genuine lower factor -/

theorem correctedSlabLinkAt_multiplicity_zero_of_odd
    (physical : EdgeLabelling) (block : Nat) (hblock : block < 116)
    (hlabel : ∀ id, physical id ≤ 1)
    (hodd : cutoffOneSlabSelectedBlockDegree block physical % 2 = 1) :
    slabExplicitLinkMultiplicity 1 1 physical
      (correctedSlabLinkAt 1 block) = 0 := by
  unfold slabExplicitLinkMultiplicity
  let spins :=
    (slabIncidentPlaqIds 1 (correctedSlabLinkAt 1 block)).map physical
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff 1)
      spins.length (externalSpinsOfList spins) = 0
  apply explicitValenceMultiplicity_eq_zero_of_odd_sum
  · unfold spins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1
        (correctedSlabLinkAt 1 block)
  · rw [localExternalSpinSum_externalSpinsOfList spins]
    unfold spins
    rw [cutoffOneLinkSpinSum_eq_selectedDegree block hblock physical hlabel]
    exact hodd

/-- Any nonclosed cutoff-one source/vacuum/vacuum assembly is killed by one
actual link inside the production lower-half factor. -/
theorem centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_zero_of_not_closed
    (w : Q') (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates 1 0)
    (hclosed :
      slabSurfaceIsClosed
        (cutoffOneSlabMask
          (assembleReflectedSlabLabelling 0 source
            zeroEdgeLabelling zeroEdgeLabelling)) = false) :
    centralHalfAmplitude w 1 0 source zeroEdgeLabelling ≈ 0 := by
  let physical := assembleReflectedSlabLabelling 0 source
    zeroEdgeLabelling zeroEdgeLabelling
  have hphysical :
      physical ∈ boundedEdgeLabellings 1 (slabPhysicalFaceEdges 1) := by
    unfold physical
    exact assembleReflectedSlabLabelling_mem_full hsource
      (zeroEdgeLabelling_mem_centralBoundaryChannels 1 0)
      (zeroEdgeLabelling_mem_centralHalfStates 1 0)
  have hlabel : ∀ id, physical id ≤ 1 :=
    boundedCutoffOneSlabLabelling_le_one hphysical
  obtain ⟨block, hblock, hodd⟩ :=
    cutoffOneSlabMask_not_closed_has_odd_degree physical hlabel hclosed
  let link := correctedSlabLinkAt 1 block
  have hlinkLower : link ∈ centralLowerLinks 0 := by
    exact correctedSlabLinkAt_mem_lower_of_assembled_odd
      source block hblock hlabel hodd
  have hlinkZero : slabExplicitLinkMultiplicity 1 1 physical link = 0 := by
    exact correctedSlabLinkAt_multiplicity_zero_of_odd
      physical block hblock hlabel hodd
  have hproduct :
      slabLinkMultiplicityProductOn 1 1 physical
        (centralLowerLinks 0) = 0 := by
    unfold slabLinkMultiplicityProductOn
    exact natListProduct_eq_zero_of_member
      (slabExplicitLinkMultiplicity 1 1 physical)
      (centralLowerLinks 0) hlinkLower hlinkZero
  unfold centralHalfAmplitude centralLowerFactor
  change
    slabFaceFactorOn w 1 physical (centralLowerFaceIds 0) *
      Q'.ofNat
        (slabLinkMultiplicityProductOn 1 1 physical
          (centralLowerLinks 0)) ≈ 0
  rw [hproduct]
  exact Q'.eqv_trans _
    (slabFaceFactorOn w 1 physical (centralLowerFaceIds 0) * 0) _
    (Q'.mul_eqv_congr_left _ _ _ Q'.ofNat_zero_eqv)
    (Q'.mul_zero_eqv _)

/-- Complete pointwise support theorem for the genuine vacuum column: every
retained source other than vacuum and the central lower cube has zero half
amplitude. -/
theorem centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_zero_of_ne
    (w : Q') (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates 1 0)
    (hneVacuum : source ≠ zeroEdgeLabelling)
    (hneCube : source ≠
      YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeState) :
    centralHalfAmplitude w 1 0 source zeroEdgeLabelling ≈ 0 := by
  cases hclosed :
      slabSurfaceIsClosed
        (cutoffOneSlabMask
          (assembleReflectedSlabLabelling 0 source
            zeroEdgeLabelling zeroEdgeLabelling)) with
  | false =>
      exact centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_zero_of_not_closed
        w source hsource hclosed
  | true =>
      rcases source_eq_vacuum_or_cube_of_assembled_closed
        source hsource hclosed with hvacuum | hcube
      · exact False.elim (hneVacuum hvacuum)
      · exact False.elim (hneCube hcube)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation.cutoffOneBlockIncidentFaceIdsCheck_true
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation.cutoffOneLinkSpinSum_eq_selectedDegree
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation.centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_zero_of_not_closed
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation.centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_zero_of_ne
