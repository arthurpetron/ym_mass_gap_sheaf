/-
# Three marked supports give one actual plaquette animal

The inserted plaquette is an ordinary additional face, not an artificial
connecting corridor. The three existing separator tests put both probes
and that face in the same component. The old common-root paths then put
every retained anchor face in that component. Existing two-probe geometry
supplies the actual animal, with at most the two carrier sizes plus the
anchor size plus ONE face.

Freshness is used only to keep this added face enumeration duplicate-free.
No heat-weight estimate, spatial decay, or coupling assertion is made.
-/

import YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
import YMGap.Continuum.BF4ExactSlabTwoProbeAnimal
import YMGap.Continuum.BF4ExactSlabRootedSelectionStability

namespace YMGap.Continuum.BF4ExactSlabThreeMarkGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedSelectionStability
open YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier coreFaces)
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound (sharedLink)
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteRootedAnimalTourCode

private theorem left_mem {ids cut : List Nat} {j : Nat} :
    j ∈ cutLeft ids cut ↔ j ∈ ids ∧ j ∈ cut := by
  simp only [cutLeft, List.mem_filter, decide_eq_true_eq]

private theorem right_mem {ids cut : List Nat} {j : Nat} :
    j ∈ cutRight ids cut ↔ j ∈ ids ∧ j ∉ cut := by
  simp only [cutRight, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]

private theorem no_separator {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (hk : keep extent left right ids = true) (S : Separator extent left right ids) : False := by
  apply keep_no_cut hk (cutLeft ids S.cut) (filter_selected _ _)
  intro link hl hr
  apply S.disjoint link
  · rcases List.mem_append.mp hl with hl | hl
    · exact List.mem_append.mpr (Or.inl hl)
    · exact List.mem_append.mpr (Or.inr (faceLinks_mono (fun j hj =>
        left_mem.mpr ⟨(left_mem.mp hj).1, (left_mem.mp (left_mem.mp hj).2).2⟩) link hl))
  · rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append.mpr (Or.inl hr)
    · exact List.mem_append.mpr (Or.inr (faceLinks_mono (fun j hj =>
        right_mem.mpr ⟨(right_mem.mp hj).1,
          fun hc => (right_mem.mp hj).2 (left_mem.mpr ⟨(right_mem.mp hj).1, hc⟩)⟩) link hr))

private theorem keep_of_no_separator {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (h : Separator extent left right ids → False) : keep extent left right ids = true := by
  cases he : findSeparator extent left right ids with
  | none => simp only [keep, he, Option.isNone]
  | some S => exact False.elim (h S)

private def swapSeparator {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (S : Separator extent left right ids) : Separator extent right left ids where
  cut := cutRight ids S.cut
  disjoint := by
    intro link hl hr
    apply S.disjoint link
    · rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append.mpr (Or.inl hr)
      · exact List.mem_append.mpr (Or.inr (faceLinks_mono (fun j hj => by
          have h := right_mem.mp hj
          by_cases hc : j ∈ S.cut
          · exact left_mem.mpr ⟨h.1, hc⟩
          · exact False.elim (h.2 (right_mem.mpr ⟨h.1, hc⟩))) link hr))
    · rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (Or.inl hl)
      · exact List.mem_append.mpr (Or.inr (faceLinks_mono (fun j hj => (left_mem.mp hj).2) link hl))

private def removeRightFace {extent id : Nat} {left right : List Z4Link} {ids : List Nat}
    (S : Separator extent left right (id::ids)) (hi : id ∉ S.cut) :
    Separator extent left (right++edgesOf (slabPlaquetteAt extent id)) ids where
  cut := S.cut
  disjoint := by
    intro link hl hr
    apply S.disjoint link
    · rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (Or.inl hl)
      · exact List.mem_append.mpr (Or.inr (faceLinks_mono
          (cutLeft_mono (fun _ h => List.mem_cons_of_mem id h) S.cut) link hl))
    · rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append.mpr (Or.inl hr)
        · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
            ⟨id, right_mem.mpr ⟨List.mem_cons_self, hi⟩, hr⟩))
      · exact List.mem_append.mpr (Or.inr (faceLinks_mono
          (cutRight_mono (fun _ h => List.mem_cons_of_mem id h) S.cut) link hr))

/-- Once the inserted face is an actual vertex, the first two mark tests
exclude every separating cut between the two original probes. -/
theorem keep_inserted (extent : Nat) (left right : List Z4Link) (ids : List Nat) (id : Nat)
    (hk : responseKeep extent id left right ids = true) :
    keep extent left right (id::ids) = true := by
  have hp := (Bool.and_eq_true _ _).mp hk
  have hq := (Bool.and_eq_true _ _).mp hp.2
  apply keep_of_no_separator
  intro S
  by_cases hi : id ∈ S.cut
  · have hn : id ∉ (swapSeparator S).cut := fun h => (right_mem.mp h).2 hi
    exact no_separator hq.1 (removeRightFace (swapSeparator S) hn)
  · exact no_separator hp.1 (removeRightFace S hi)

private theorem spectator_of_not_core {extent : Nat} {links : List Z4Link} {ids : List Nat}
    {id : Nat} (hi : id ∈ ids) (hc : id ∉ core extent links ids) :
    id ∈ spectators extent links ids :=
  spectators_mem_iff.mpr ⟨hi, fun h => hc (core_mem_iff.mpr ⟨hi, h⟩)⟩

private theorem inserted_mem_core (extent : Nat) (links : List Z4Link) (ids : List Nat) (id : Nat)
    (hk : keep extent links (edgesOf (slabPlaquetteAt extent id)) ids = true) :
    id ∈ core extent links (id::ids) := by
  by_cases hc : id ∈ core extent links (id::ids)
  · exact hc
  · have hi := spectator_of_not_core List.mem_cons_self hc
    have hd := split_disjoint extent links (id::ids)
    apply False.elim
    apply no_separator hk
    refine ⟨core extent links (id::ids), ?_⟩
    intro link hl hr
    apply hd link
    · rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (Or.inl hl)
      · exact List.mem_append.mpr (Or.inr (faceLinks_mono (fun _ h => (left_mem.mp h).2) link hl))
    · rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_flatMap.mpr ⟨id, hi, hr⟩
      · exact faceLinks_mono (fun j hj => spectator_of_not_core
          (List.mem_cons_of_mem id (right_mem.mp hj).1) (right_mem.mp hj).2) link hr

private theorem adjacent_of_shared {extent : Nat} {links : List Z4Link} {a b : Option Nat}
    (link : Z4Link) (ha : link ∈ nodeLinks extent links a) (hb : link ∈ nodeLinks extent links b) :
    adjacent extent links a b = true := by
  have hn : disjointTest (nodeLinks extent links a) (nodeLinks extent links b) ≠ true :=
    fun h => (disjointTest_iff _ _).mp h link ha hb
  cases he : disjointTest (nodeLinks extent links a) (nodeLinks extent links b) with
  | false => simp only [adjacent, he, Bool.not_false]
  | true => exact False.elim (hn he)

private theorem enlarged_root_step {extent id : Nat} {links : List Z4Link} {ids : List Nat}
    (hi : some id ∈ component extent links (id::ids)) {a b : Option Nat}
    (ha : a ∈ component extent links (id::ids)) (hb : b ∈ vertices ids)
    (he : adjacent extent (links++edgesOf (slabPlaquetteAt extent id)) a b = true) :
    b ∈ component extent links (id::ids) := by
  have hroot : none ∈ vertices (id::ids) := List.mem_cons_self
  have close (source target : Option Nat) := rootComponent_closed_under_edge
    (source := source) (target := target) (adjacent extent links) (adjacent_sym extent links) hroot
  cases b with
  | none => exact root_mem_rootComponent _ hroot
  | some j =>
    have hj : some j ∈ vertices (id::ids) :=
      vertices_mono (fun _ h => List.mem_cons_of_mem id h) _ hb
    cases a with
    | none =>
      have hn : disjointTest (links++edgesOf (slabPlaquetteAt extent id)) (faceLinks extent [j]) = false := by
        simpa only [adjacent, nodeLinks, Bool.not_eq_true'] using he
      obtain ⟨link, hl, hr⟩ := sharedLink _ _ hn
      rcases List.mem_append.mp hl with hl | hl
      · exact close none (some j) ha hj (adjacent_of_shared link hl hr)
      · have hid : link ∈ nodeLinks extent links (some id) := by
          simpa only [nodeLinks, faceLinks, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hl
        exact close (some id) (some j) hi hj (adjacent_of_shared link hid hr)
    | some k => exact close (some k) (some j) ha hj he

private theorem enlarged_root_path {extent id : Nat} {links : List Z4Link} {ids : List Nat}
    (hi : some id ∈ component extent links (id::ids)) : {a b : Option Nat} →
    ChainIn (adjacent extent (links++edgesOf (slabPlaquetteAt extent id))) (vertices ids) a b →
    a ∈ component extent links (id::ids) → b ∈ component extent links (id::ids)
  | _, _, .refl _, ha => ha
  | _, _, .step he hb rest, ha => enlarged_root_path hi rest (enlarged_root_step hi ha hb he)

/-- The insertion test forces the inserted face into the ordinary root
component. Every old rooted path then uses that actual face in its place. -/
theorem fixed_inserted (extent : Nat) (left right : List Z4Link) (ids : List Nat) (id : Nat)
    (hk : responseKeep extent id left right ids = true)
    (hf : core extent ((left++right)++edgesOf (slabPlaquetteAt extent id)) ids = ids) :
    core extent (left++right) (id::ids) = id::ids := by
  have ht := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hk).2
  have hi := (core_mem_iff.mp (inserted_mem_core extent (left++right) ids id ht.2)).2
  apply List.filter_eq_self.mpr
  intro j hj
  apply decide_eq_true
  rcases List.mem_cons.mp hj with he | hj
  · exact he.symm ▸ hi
  · have path : ChainIn (adjacent extent ((left++right)++edgesOf (slabPlaquetteAt extent id)))
        (vertices ids) none (some j) := by
      simpa only [hf] using (core_path extent ((left++right)++edgesOf (slabPlaquetteAt extent id)) ids j (hf.symm ▸ hj))
    exact enlarged_root_path hi path
      (root_mem_rootComponent _ (show none ∈ vertices (id::ids) from List.mem_cons_self))

section Animal

variable {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
  (extent : Nat) (ids : List Nat) (id : Nat) (hn : ids.Nodup)
  (hphys : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
  (hid : id ∈ slabPhysicalFaceEdges extent) (hfresh : id ∉ ids)
  (hk : responseKeep extent id left right ids = true)
  (hf : core extent ((left++right)++edgesOf (slabPlaquetteAt extent id)) ids = ids)

/-- The actual two probe carriers, anchor faces, and one fresh inserted
plaquette, with all connecting paths constructed by the existing compiler. -/
def responseAnimal : RootedConnectedAnimal z4Chain :=
  BF4ExactSlabTwoProbeAnimal.augmentedAnimal P Q extent (id::ids)
    (List.nodup_cons.mpr ⟨hfresh, hn⟩)
    (fun j hj => (List.mem_cons.mp hj).elim (fun he => he.symm ▸ hid) (hphys j))
    (keep_inserted extent left right ids id hk) (fixed_inserted extent left right ids id hk hf)

theorem responseAnimal_size_le :
    (responseAnimal P Q extent ids id hn hphys hid hfresh hk hf).support.length ≤
      P.animal.support.length+Q.animal.support.length+ids.length+1 := by
  have h := BF4ExactSlabTwoProbeAnimal.augmented_size_le P Q extent (id::ids)
  simpa only [List.length_cons, Nat.add_assoc] using h

theorem responseAnimal_inserted_mem : slabPlaquetteAt extent id ∈
    (responseAnimal P Q extent ids id hn hphys hid hfresh hk hf).support :=
  (BF4ExactSlabTwoProbeAnimal.augmented_mem P Q extent (id::ids) _).mpr
    (Or.inr (List.mem_map.mpr ⟨id, List.mem_cons_self, rfl⟩))

end Animal
end YMGap.Continuum.BF4ExactSlabThreeMarkGeometry

#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkGeometry.keep_inserted
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkGeometry.fixed_inserted
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkGeometry.responseAnimal
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkGeometry.responseAnimal_size_le
#print axioms YMGap.Continuum.BF4ExactSlabThreeMarkGeometry.responseAnimal_inserted_mem
