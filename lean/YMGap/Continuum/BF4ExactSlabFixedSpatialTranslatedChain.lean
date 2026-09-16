/-
# Literal spatially and temporally translated selected chains

The original chain IDs are mapped by the existing ambient face-ID placement.
Physicality and duplicate-freeness require only room for that placement.
When the source chain is contained, exact membership is the translated
spatial BASE box and time window: spatial faces include the last slice,
while temporal faces have a strict upper time bound. The clipped source
chain is still handled honestly without the containment hypotheses.

These statements identify selected face lists, not Haar functionals,
partitions, states, completed norms, or spatial limiting theories.
-/

import YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedChain

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry

/-- Preserve the literal source-chain order under the existing face-ID map. -/
def translatedIds (source target space time width start steps : Nat) : List Nat :=
  (chainIds source width start steps).map (shiftFaceId source target space time)

/-- Half-open spatial base intervals, with the terminal spatial slice retained. -/
def TranslatedWindow (space time width start steps : Nat) (p : Z4Plaq) : Prop :=
  space ≤ p.1.1 ∧ p.1.1 < width+space ∧
  space ≤ p.1.2.1 ∧ p.1.2.1 < width+space ∧
  space ≤ p.1.2.2.1 ∧ p.1.2.2.1 < width+space ∧
  start+time ≤ p.1.2.2.2 ∧
  (((dirsOf p.2).2 ≠ Dir4.x3 ∧ p.1.2.2.2 ≤ start+steps+time) ∨
   ((dirsOf p.2).2 = Dir4.x3 ∧ p.1.2.2.2 < start+steps+time))

theorem translatedIds_physical {source target space time width start steps id : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (hi : id ∈ translatedIds source target space time width start steps) :
    id ∈ slabPhysicalFaceEdges target := by
  obtain ⟨i, hsource, rfl⟩ := List.mem_map.mp hi
  exact shiftFaceId_physical hr ht (chainIds_physical hsource)

theorem translatedIds_nodup {source target space time : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (width start steps : Nat) :
    (translatedIds source target space time width start steps).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn _ _ (chainIds_nodup source width start steps)
    (fun _ hi _ hj he => shiftFaceId_injective hr ht
      (chainIds_physical hi) (chainIds_physical hj) he)

/-- Every numerical target ID names exactly its translated source face. -/
theorem translatedIds_faces_pin {source target space time : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (width start steps : Nat) :
    (translatedIds source target space time width start steps).map (slabPlaquetteAt target) =
      (chainIds source width start steps).map
        (fun id => shiftFace space time (slabPlaquetteAt source id)) := by
  unfold translatedIds
  rw [List.map_map]
  apply List.map_congr_left
  intro id hi
  exact shiftFaceId_pin hr ht (chainIds_physical hi)

private theorem window_of_shift (space time width start steps : Nat) (p : Z4Plaq)
    (hp : p ∈ chainFaces width start steps) :
    TranslatedWindow space time width start steps (shiftFace space time p) := by
  have h := (chainFaces_mem_iff width start steps p).mp hp
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  change a < width ∧ b < width ∧ c < width ∧ start ≤ d ∧
    (((dirsOf plane).2 ≠ Dir4.x3 ∧ d ≤ start+steps) ∨
     ((dirsOf plane).2 = Dir4.x3 ∧ d < start+steps)) at h
  obtain ⟨ha, hb, hc, hl, hlast⟩ := h
  change space ≤ a+space ∧ a+space < width+space ∧
    space ≤ b+space ∧ b+space < width+space ∧
    space ≤ c+space ∧ c+space < width+space ∧
    start+time ≤ d+time ∧
    (((dirsOf plane).2 ≠ Dir4.x3 ∧ d+time ≤ start+steps+time) ∨
     ((dirsOf plane).2 = Dir4.x3 ∧ d+time < start+steps+time))
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  rcases hlast with hs | ht
  · exact Or.inl ⟨hs.1, by omega⟩
  · exact Or.inr ⟨ht.1, by omega⟩

/-- Forward base-window bounds remain true even for a clipped source chain. -/
theorem translatedIds_window {source target space time width start steps id : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (hi : id ∈ translatedIds source target space time width start steps) :
    TranslatedWindow space time width start steps (slabPlaquetteAt target id) := by
  obtain ⟨i, hsource, rfl⟩ := List.mem_map.mp hi
  rw [shiftFaceId_pin hr ht (chainIds_physical hsource)]
  exact window_of_shift space time width start steps _
    ((chainFaces_mem_iff width start steps _).mpr
      ((chainIds_mem_iff source width start steps i).mp hsource).2)

/-- Exact raw-face membership under source-chain containment. The inverse
is the coordinatewise subtraction of the displayed placement, not a choice. -/
theorem translatedIds_faces_mem_iff {source target space time width start steps : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (hw : width ≤ source+1) (hs : start+steps ≤ source) (p : Z4Plaq) :
    p ∈ (translatedIds source target space time width start steps).map (slabPlaquetteAt target) ↔
      TranslatedWindow space time width start steps p := by
  constructor
  · intro hp
    obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hp
    exact translatedIds_window hr ht hi
  · intro hp
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
    change space ≤ a ∧ a < width+space ∧ space ≤ b ∧ b < width+space ∧
      space ≤ c ∧ c < width+space ∧ start+time ≤ d ∧
      (((dirsOf plane).2 ≠ Dir4.x3 ∧ d ≤ start+steps+time) ∨
       ((dirsOf plane).2 = Dir4.x3 ∧ d < start+steps+time)) at hp
    obtain ⟨hal, hau, hbl, hbu, hcl, hcu, hdl, hlast⟩ := hp
    let q : Z4Plaq := ((a-space, b-space, c-space, d-time), plane)
    have hq : q ∈ (chainIds source width start steps).map (slabPlaquetteAt source) := by
      apply (chainIds_faces_mem_iff source width start steps hw hs q).mpr
      change a-space < width ∧ b-space < width ∧ c-space < width ∧
        start ≤ d-time ∧
        (((dirsOf plane).2 ≠ Dir4.x3 ∧ d-time ≤ start+steps) ∨
         ((dirsOf plane).2 = Dir4.x3 ∧ d-time < start+steps))
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      rcases hlast with hsp | htemp
      · exact Or.inl ⟨hsp.1, by omega⟩
      · exact Or.inr ⟨htemp.1, by omega⟩
    have hshift : shiftFace space time q = ((a, b, c, d), plane) := by
      have hd : time ≤ d := by omega
      simp only [q, shiftFace, shiftVertex, Nat.sub_add_cancel hal,
        Nat.sub_add_cancel hbl, Nat.sub_add_cancel hcl, Nat.sub_add_cancel hd]
    obtain ⟨id, hi, he⟩ := List.mem_map.mp hq
    rw [translatedIds_faces_pin hr ht width start steps]
    exact List.mem_map.mpr ⟨id, hi, (congrArg (shiftFace space time) he).trans hshift⟩

/-- Target numerical membership is precisely physicality plus the stated
translated base box/window. Physicality excludes out-of-range default IDs. -/
theorem translatedIds_mem_iff {source target space time width start steps : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (hw : width ≤ source+1) (hs : start+steps ≤ source) (id : Nat) :
    id ∈ translatedIds source target space time width start steps ↔
      id ∈ slabPhysicalFaceEdges target ∧
        TranslatedWindow space time width start steps (slabPlaquetteAt target id) := by
  constructor
  · intro hi
    exact ⟨translatedIds_physical hr ht hi, translatedIds_window hr ht hi⟩
  · intro h
    have hm := (translatedIds_faces_mem_iff hr ht hw hs (slabPlaquetteAt target id)).mpr h.2
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    have hji : j = id := slabPlaquetteAt_injective_on_physical
      (translatedIds_physical hr ht hj) h.1 he
    exact hji ▸ hj

/-- Forward containment in a larger zero-based spatial chain. This needs no
unclipped-source hypothesis; all retained target faces remain physical. -/
theorem translatedIds_subset_chain {source target space time width start steps largerWidth : Nat}
    (hr : source+space ≤ target) (ht : source+time ≤ target)
    (hwide : width+space ≤ largerWidth) {id : Nat}
    (hi : id ∈ translatedIds source target space time width start steps) :
    id ∈ chainIds target largerWidth (start+time) steps := by
  have h := translatedIds_window hr ht hi
  obtain ⟨_, ha, _, hb, _, hc, hl, hlast⟩ := h
  apply (chainIds_mem_iff target largerWidth (start+time) steps id).mpr
  refine ⟨translatedIds_physical hr ht hi, by omega, by omega, by omega, hl, ?_⟩
  rcases hlast with hs | htemp
  · exact Or.inl ⟨hs.1, by omega⟩
  · exact Or.inr ⟨htemp.1, by omega⟩

#print axioms translatedIds
#print axioms translatedIds_physical
#print axioms translatedIds_nodup
#print axioms translatedIds_faces_pin
#print axioms translatedIds_window
#print axioms translatedIds_faces_mem_iff
#print axioms translatedIds_mem_iff
#print axioms translatedIds_subset_chain

end YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedChain
