/-
# Two different plaquettes share at most one boundary link

Two distinct boundary links determine a coordinate unit plaquette. Thus
the boundary overlap of distinct plaquettes has size at most one. Their
boundary symmetric difference cannot have four links: it is empty for
equal plaquettes and has at least six links otherwise. These are literal
finite lattice statements, with no gauge, weight or temporal assumption.
-/

import YMGap.Continuum.Z4UnitCubeIncidenceParity
import YMGap.Continuum.Z4CanonicalPolymerUniverse

namespace YMGap.Continuum.Z4PlaquetteBoundaryRigidity

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4UnitCubeIncidenceParity

theorem two_boundary_links_determine_face (left right : Z4Plaq) (a b : Z4Link)
    (ha : a ∈ edgesOf left) (hb : b ∈ edgesOf left) (hne : a ≠ b)
    (hra : a ∈ edgesOf right) (hrb : b ∈ edgesOf right) : left=right := by
  rcases left with ⟨⟨x,y,z,t⟩,p⟩
  rcases right with ⟨⟨u,v,w,s⟩,q⟩
  cases p
  all_goals
    simp only [edgesOf, dirsOf, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl
    all_goals rcases hb with rfl | rfl | rfl | rfl
    all_goals try exact False.elim (hne rfl)
    all_goals clear hne
    all_goals cases q
    all_goals
      simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq, reduceCtorEq, and_true, and_false, false_or] at hra hrb ⊢
      repeat' constructor
      all_goals omega

theorem boundary_subset_eq (left right : Z4Plaq)
    (hs : ∀ link, link ∈ edgesOf left → link ∈ edgesOf right) : left=right :=
  two_boundary_links_determine_face left right (left.1,(dirsOf left.2).1) (left.1,(dirsOf left.2).2)
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun h => dirsOf_ne left.2 (congrArg Prod.snd h))
    (hs _ List.mem_cons_self) (hs _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem distinct_boundary_overlap_le_one (left right : Z4Plaq) (hne : left ≠ right) :
    ((edgesOf left).filter (fun link => decide (link ∈ edgesOf right))).length ≤ 1 := by
  let overlap := (edgesOf left).filter (fun link => decide (link ∈ edgesOf right))
  have hn : overlap.Nodup := (edgesOf_nodup left).filter _
  have hm (link : Z4Link) (hl : link ∈ overlap) : link ∈ edgesOf left ∧ link ∈ edgesOf right :=
    ⟨(List.mem_filter.mp hl).1,of_decide_eq_true (List.mem_filter.mp hl).2⟩
  change overlap.length ≤ 1
  cases he : overlap with
  | nil => exact Nat.zero_le _
  | cons a rest =>
    cases rest with
    | nil => exact Nat.le_refl _
    | cons b rest =>
      have ha := hm a (he ▸ List.mem_cons_self)
      have hb := hm b (he ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      rw [he] at hn
      have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl h))
      exact False.elim (hne (two_boundary_links_determine_face left right a b ha.1 hb.1 hab ha.2 hb.2))

def symmetricBoundary (left right : Z4Plaq) : List Z4Link :=
  (edgesOf left).filter (fun link => decide (link ∉ edgesOf right)) ++
    (edgesOf right).filter (fun link => decide (link ∉ edgesOf left))

theorem symmetricBoundary_nodup (left right : Z4Plaq) : (symmetricBoundary left right).Nodup := by
  refine List.nodup_append.mpr ⟨(edgesOf_nodup left).filter _,(edgesOf_nodup right).filter _,?_⟩
  intro a ha b hb he
  have hn := of_decide_eq_true (List.mem_filter.mp ha).2
  exact hn (he ▸ (List.mem_filter.mp hb).1)

theorem overlap_length_comm (left right : Z4Plaq) :
    ((edgesOf left).filter (fun link => decide (link ∈ edgesOf right))).length =
      ((edgesOf right).filter (fun link => decide (link ∈ edgesOf left))).length := by
  apply List.Perm.length_eq
  apply Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _
    ((edgesOf_nodup left).filter _) ((edgesOf_nodup right).filter _)
  intro link
  simp only [List.mem_filter, decide_eq_true_eq]
  exact and_comm

private theorem boundary_filter_lengths (left right : Z4Plaq) :
    ((edgesOf left).filter (fun link => decide (link ∈ edgesOf right))).length+
      ((edgesOf left).filter (fun link => decide (link ∉ edgesOf right))).length=4 := by
  have h := (List.filter_append_perm (fun link => decide (link ∈ edgesOf right)) (edgesOf left)).length_eq
  have hf : (edgesOf left).filter (fun link => !(decide (link ∈ edgesOf right))) =
      (edgesOf left).filter (fun link => decide (link ∉ edgesOf right)) := by
    apply List.filter_congr
    intro link _
    by_cases hm : link ∈ edgesOf right <;>
      simp only [hm, decide_true, decide_false, not_true_eq_false, not_false_eq_true,
        Bool.not_true, Bool.not_false]
  simpa only [List.length_append, hf] using h

theorem symmetricBoundary_length (left right : Z4Plaq) :
    (symmetricBoundary left right).length+
      2*((edgesOf left).filter (fun link => decide (link ∈ edgesOf right))).length=8 := by
  have hl := boundary_filter_lengths left right
  have hr := boundary_filter_lengths right left
  rw [← overlap_length_comm left right] at hr
  simp only [symmetricBoundary, List.length_append]
  omega

theorem distinct_symmetricBoundary_six (left right : Z4Plaq) (hne : left ≠ right) :
    6 ≤ (symmetricBoundary left right).length := by
  have hc := distinct_boundary_overlap_le_one left right hne
  have hl := symmetricBoundary_length left right
  omega

theorem symmetricBoundary_self (face : Z4Plaq) : symmetricBoundary face face=[] := by
  have hz : (edgesOf face).filter (fun link => decide (link ∉ edgesOf face))=[] := by
    cases he : (edgesOf face).filter (fun link => decide (link ∉ edgesOf face)) with
    | nil => rfl
    | cons link rest =>
      have hm := List.mem_filter.mp (show link ∈ (edgesOf face).filter
        (fun link => decide (link ∉ edgesOf face)) from he ▸ List.mem_cons_self)
      exact False.elim ((of_decide_eq_true hm.2) hm.1)
  rw [symmetricBoundary,hz]
  rfl

theorem symmetricBoundary_ne_four (left right : Z4Plaq) : (symmetricBoundary left right).length ≠ 4 := by
  by_cases he : left=right
  · subst right
    rw [symmetricBoundary_self]
    decide
  · have h := distinct_symmetricBoundary_six left right he
    omega

end YMGap.Continuum.Z4PlaquetteBoundaryRigidity

#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.two_boundary_links_determine_face
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.boundary_subset_eq
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.distinct_boundary_overlap_le_one
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.symmetricBoundary
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.symmetricBoundary_nodup
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.overlap_length_comm
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.symmetricBoundary_length
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.distinct_symmetricBoundary_six
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.symmetricBoundary_self
#print axioms YMGap.Continuum.Z4PlaquetteBoundaryRigidity.symmetricBoundary_ne_four
