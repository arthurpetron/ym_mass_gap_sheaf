/-
# The original full response slab inside the current union diagonal

At diagonal index s+1, base=1 and time lag/chart radius=3, the selected
chain has extent 6*s+20, width 2*s+5 and time window [2*s+6,4*s+14].
Translate the OLD full slab of extent 2*s+3 by one spatial unit and
2*s+7 temporal units. Its lag-three probes align with the current ones.

Every translated source factor occurs once in the current selected action.
Every omitted factor is at L-infinity distance at least s+1 from the
translated lower probe, including temporal faces at the strict endpoint.
The filtered action is only the translated old action, not the entire
current action. These are inputs to their still-needed analytic comparison.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
import YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor

namespace YMGap.Continuum.BF4SpatialUnionResponseGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding (Placement)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedChain (TranslatedWindow)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent chartIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry (responseExtent sliceFace)
open YMGap.Continuum.Z4CanonicalPolymerUniverse (perm_of_nodup_mem_iff)
open YMGap.Continuum.SepLatticeZ4Linf

def sourceExtent (s : Nat) : Nat := responseExtent s
def targetExtent (s : Nat) : Nat := chartExtent 1 (s+1) 3 (s+1)

theorem sourceExtent_eq (s : Nat) : sourceExtent s = 2*s+3 := by
  unfold sourceExtent responseExtent centralExtent
  omega

theorem targetExtent_eq (s : Nat) : targetExtent s = 6*s+20 := by
  unfold targetExtent chartExtent paddedWidth adjacentEvenExtent centralExtent
  omega

def responsePlacement (s : Nat) : Placement where
  source := sourceExtent s
  target := targetExtent s
  space := 1
  time := 2*s+7
  space_room := by rw [sourceExtent_eq, targetExtent_eq]; omega
  time_room := by rw [sourceExtent_eq, targetExtent_eq]; omega

def ambientIds (s : Nat) : List Nat := chartIds 1 (s+1) 3 (s+1)

def translatedIds (s : Nat) : List Nat :=
  (slabPhysicalFaceEdges (sourceExtent s)).map (responsePlacement s).faceId

def keep (s id : Nat) : Bool := decide (id ∈ translatedIds s)

def root (s : Nat) : Z4Plaq := shiftFace 1 (2*s+7) (sliceFace s 0)

theorem root_eq (s : Nat) : root s = ((s+2,s+2,s+2,3*s+7), .p01) := by
  have hspace : 1+s+1 = s+2 := by omega
  have htime : s+(2*s+7) = 3*s+7 := by omega
  simp only [root, sliceFace, shiftFace, shiftVertex, Nat.add_zero, hspace, htime]

theorem ambientIds_eq (s : Nat) :
    ambientIds s = chainIds (targetExtent s) (2*s+5) (2*s+6) (2*s+8) := by
  unfold ambientIds chartIds
  change chainIds (targetExtent s) (paddedWidth 1 (s+1))
    (paddedWidth 1 (s+1)+1) ((s+1)+(2*3+(s+1))) = _
  simp only [paddedWidth]
  congr 1 <;> omega

theorem ambientIds_physical (s : Nat) {id : Nat} (hi : id ∈ ambientIds s) :
    id ∈ slabPhysicalFaceEdges (targetExtent s) := chainIds_physical hi

theorem ambientIds_nodup (s : Nat) : (ambientIds s).Nodup := chainIds_nodup _ _ _ _

private theorem full_window {extent : Nat} {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent) :
    p.1.1 < extent+1 ∧ p.1.2.1 < extent+1 ∧ p.1.2.2.1 < extent+1 ∧
      0 ≤ p.1.2.2.2 ∧
      (((dirsOf p.2).2 ≠ Dir4.x3 ∧ p.1.2.2.2 ≤ 0+extent) ∨
       ((dirsOf p.2).2 = Dir4.x3 ∧ p.1.2.2.2 < 0+extent)) := by
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := p
  obtain ⟨hb, ht⟩ := (mem_boundaryCompleteSlabPlaquettes extent _).mp hp
  rw [mem_boxPlaquettes] at hb
  change a < extent+1 ∧ b < extent+1 ∧ c < extent+1 ∧ d < extent+1 at hb
  refine ⟨hb.1, hb.2.1, hb.2.2.1, Nat.zero_le _, ?_⟩
  cases plane <;> simp_all [dirsOf, plaquetteTimeAdmissible]

/-- A complete original slab is the full-width, full-time selected chain. -/
theorem full_chain_perm (extent : Nat) :
    (chainIds extent (extent+1) 0 extent).Perm (slabPhysicalFaceEdges extent) := by
  apply perm_of_nodup_mem_iff _ _ (chainIds_nodup _ _ _ _) (CayleyParentInj.range_nodup _)
  intro id
  constructor
  · exact chainIds_physical
  · intro hi
    exact (chainIds_mem_iff _ _ _ _ _).mpr ⟨hi, full_window (slabPlaquetteAt_mem hi)⟩

private theorem translated_chain_perm (s : Nat) :
    (BF4ExactSlabFixedSpatialTranslatedChain.translatedIds (sourceExtent s)
      (targetExtent s) 1 (2*s+7) (sourceExtent s+1) 0 (sourceExtent s)).Perm
      (translatedIds s) :=
  (full_chain_perm (sourceExtent s)).map (responsePlacement s).faceId

theorem translatedIds_nodup (s : Nat) : (translatedIds s).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn _ _ (CayleyParentInj.range_nodup _)
    (fun _ hi _ hj he => (responsePlacement s).faceId_injective hi hj he)

theorem translatedIds_physical (s : Nat) {id : Nat} (hi : id ∈ translatedIds s) :
    id ∈ slabPhysicalFaceEdges (targetExtent s) := by
  obtain ⟨i, hsource, rfl⟩ := List.mem_map.mp hi
  exact (responsePlacement s).faceId_physical hsource

/-- Both endpoint conventions are preserved, including the last spatial slice. -/
theorem translatedIds_mem_iff (s id : Nat) :
    id ∈ translatedIds s ↔ id ∈ slabPhysicalFaceEdges (targetExtent s) ∧
      TranslatedWindow 1 (2*s+7) (sourceExtent s+1) 0 (sourceExtent s)
        (slabPlaquetteAt (targetExtent s) id) :=
  (translated_chain_perm s).mem_iff.symm.trans
    (BF4ExactSlabFixedSpatialTranslatedChain.translatedIds_mem_iff
      (responsePlacement s).space_room (responsePlacement s).time_room
      (Nat.le_refl _) (by change 0+sourceExtent s ≤ sourceExtent s; omega) id)

theorem translatedIds_subset (s : Nat) {id : Nat} (hi : id ∈ translatedIds s) :
    id ∈ ambientIds s := by
  obtain ⟨hphys, hbox⟩ := (translatedIds_mem_iff s id).mp hi
  obtain ⟨_, ha, _, hb, _, hc, ht, hlast⟩ := hbox
  rw [sourceExtent_eq] at ha hb hc hlast
  rw [ambientIds_eq]
  apply (chainIds_mem_iff _ _ _ _ _).mpr
  refine ⟨hphys, by omega, by omega, by omega, by omega, ?_⟩
  rcases hlast with hsp | htemp
  · exact Or.inl ⟨hsp.1, by omega⟩
  · exact Or.inr ⟨htemp.1, by omega⟩

theorem filter_perm (s : Nat) :
    ((ambientIds s).filter (keep s)).Perm (translatedIds s) := by
  apply perm_of_nodup_mem_iff _ _ (List.filter_sublist.nodup (ambientIds_nodup s))
    (translatedIds_nodup s)
  intro id
  simp only [List.mem_filter, keep, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨translatedIds_subset s h, h⟩⟩

private theorem near_root_window (s : Nat) (p : Z4Plaq)
    (hd : linfDist (root s) p < s+1) :
    TranslatedWindow 1 (2*s+7) (sourceExtent s+1) 0 (sourceExtent s) p := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  have h0 := Nat.lt_of_le_of_lt (le_linfDist_comp (root s) ((a,b,c,d),plane) .x0) hd
  have h1 := Nat.lt_of_le_of_lt (le_linfDist_comp (root s) ((a,b,c,d),plane) .x1) hd
  have h2 := Nat.lt_of_le_of_lt (le_linfDist_comp (root s) ((a,b,c,d),plane) .x2) hd
  have h3 := Nat.lt_of_le_of_lt (le_linfDist_comp (root s) ((a,b,c,d),plane) .x3) hd
  rw [root_eq] at h0 h1 h2 h3
  simp only [cPlaq, vComp, natDist] at h0 h1 h2 h3
  unfold TranslatedWindow
  rw [sourceExtent_eq]
  change 1 ≤ a ∧ a < (2*s+3)+1+1 ∧ 1 ≤ b ∧ b < (2*s+3)+1+1 ∧
    1 ≤ c ∧ c < (2*s+3)+1+1 ∧ 0+(2*s+7) ≤ d ∧
    (((dirsOf plane).2 ≠ Dir4.x3 ∧ d ≤ 0+(2*s+3)+(2*s+7)) ∨
     ((dirsOf plane).2 = Dir4.x3 ∧ d < 0+(2*s+3)+(2*s+7)))
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  by_cases ht : (dirsOf plane).2 = Dir4.x3
  · exact Or.inr ⟨ht, by omega⟩
  · exact Or.inl ⟨ht, by omega⟩

/-- No omitted original factor is close, irrespective of face orientation. -/
theorem omitted_separation (s : Nat) {id : Nat} (hi : id ∈ ambientIds s)
    (ho : keep s id = false) :
    s+1 ≤ linfDist (root s) (slabPlaquetteAt (targetExtent s) id) := by
  by_cases hd : s+1 ≤ linfDist (root s) (slabPlaquetteAt (targetExtent s) id)
  · exact hd
  · have hm := (translatedIds_mem_iff s id).mpr
      ⟨ambientIds_physical s hi, near_root_window s _ (Nat.lt_of_not_ge hd)⟩
    have hn : id ∉ translatedIds s := by simpa only [keep, decide_eq_false_iff_not] using ho
    exact False.elim (hn hm)

/-- Direct input to the existing signed active-core tail estimate. -/
theorem active_core_floor (s : Nat) {links : List Z4Link}
    (probe : BF4ExactSlabProbeCarrierAnimal.ProbeCarrier links)
    (hroot : probe.animal.root = root s) {anchor : List Nat}
    (ha : anchor ∈ BF4ExactSlabProbeRootedBoundaryExpansion.activeAnchors
      (targetExtent s) links (keep s) (ambientIds s)) :
    s+2 ≤ probe.animal.support.length+anchor.length := by
  have h := BF4ExactSlabCoreDistanceFloor.active_core_linf_floor probe
    (ambientIds_nodup s) (fun _ hi => ambientIds_physical s hi) ha (by
      intro id hi ho
      rw [hroot]
      exact omitted_separation s hi ho)
  exact h

end YMGap.Continuum.BF4SpatialUnionResponseGeometry

#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.sourceExtent
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.targetExtent
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.sourceExtent_eq
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.targetExtent_eq
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.responsePlacement
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.ambientIds
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.translatedIds
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.keep
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.root
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.root_eq
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.ambientIds_eq
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.ambientIds_physical
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.ambientIds_nodup
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.full_chain_perm
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.translatedIds_nodup
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.translatedIds_physical
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.translatedIds_mem_iff
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.translatedIds_subset
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.filter_perm
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.omitted_separation
#print axioms YMGap.Continuum.BF4SpatialUnionResponseGeometry.active_core_floor
