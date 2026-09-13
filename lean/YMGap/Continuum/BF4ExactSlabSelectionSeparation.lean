/-
# Computed separating cuts of selected ORIGINAL plaquette links

A separator returns an actual cut of the face list and proves disjointness
of the two probe-plus-face link regions. The finite search enumerates all
positional cuts. No connected-component oracle, choice, or physics premise
is used. The exhaustive search is a certificate construction, not an
efficient numerical cluster enumeration.
-/

import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabSelectionSeparation

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.FinitePolynomialSubsetExpansion

def cutLeft (ids cut : List Nat) : List Nat := ids.filter (fun id => decide (id ∈ cut))
def cutRight (ids cut : List Nat) : List Nat := ids.filter (fun id => !(decide (id ∈ cut)))

theorem cut_partition (ids cut : List Nat) : (cutLeft ids cut ++ cutRight ids cut).Perm ids :=
  List.filter_append_perm _ _

theorem faceLinks_mono {extent : Nat} {xs ys : List Nat} (h : ∀ id, id ∈ xs → id ∈ ys) :
    ∀ link, link ∈ faceLinks extent xs → link ∈ faceLinks extent ys := by
  intro link hl
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hl
  exact List.mem_flatMap.mpr ⟨id, h id hi, he⟩

theorem cutLeft_mono {xs ys : List Nat} (h : ∀ id, id ∈ xs → id ∈ ys) (cut : List Nat) :
    ∀ id, id ∈ cutLeft xs cut → id ∈ cutLeft ys cut := by
  intro id hi
  exact List.mem_filter.mpr ⟨h id (List.mem_filter.mp hi).1, (List.mem_filter.mp hi).2⟩

theorem cutRight_mono {xs ys : List Nat} (h : ∀ id, id ∈ xs → id ∈ ys) (cut : List Nat) :
    ∀ id, id ∈ cutRight xs cut → id ∈ cutRight ys cut := by
  intro id hi
  exact List.mem_filter.mpr ⟨h id (List.mem_filter.mp hi).1, (List.mem_filter.mp hi).2⟩

structure Separator (extent : Nat) (left right : List Z4Link) (ids : List Nat) : Type where
  cut : List Nat
  disjoint : LinksDisjoint (left ++ faceLinks extent (cutLeft ids cut))
    (right ++ faceLinks extent (cutRight ids cut))

def Separator.restrict {extent : Nat} {left right : List Z4Link} {xs ys : List Nat}
    (S : Separator extent left right ys) (h : ∀ id, id ∈ xs → id ∈ ys) : Separator extent left right xs where
  cut := S.cut
  disjoint := by
    intro link hl hr
    apply S.disjoint link
    · rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (Or.inl hl)
      · exact List.mem_append.mpr (Or.inr (faceLinks_mono (cutLeft_mono h S.cut) link hl))
    · rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append.mpr (Or.inl hr)
      · exact List.mem_append.mpr (Or.inr (faceLinks_mono (cutRight_mono h S.cut) link hr))

def disjointTest (left right : List Z4Link) : Bool :=
  left.all (fun link => !(decide (link ∈ right)))

theorem disjointTest_iff (left right : List Z4Link) :
    disjointTest left right = true ↔ LinksDisjoint left right := by
  constructor
  · intro h link hl hr
    have hn := List.all_eq_true.mp h link hl
    simp only [decide_eq_true hr, Bool.not_true] at hn
    cases hn
  · intro h
    apply List.all_eq_true.mpr
    intro link hl
    have hn : link ∉ right := h link hl
    simp only [decide_eq_false hn, Bool.not_false]

def search (extent : Nat) (left right : List Z4Link) (ids : List Nat) :
    List (List Nat) → Option (Separator extent left right ids)
  | [] => none
  | cut :: rest =>
      if h : disjointTest (left ++ faceLinks extent (cutLeft ids cut))
          (right ++ faceLinks extent (cutRight ids cut)) = true then
        some ⟨cut, (disjointTest_iff _ _).mp h⟩
      else search extent left right ids rest

/-- Every explicitly enumerated separating cut is found by the finite search. -/
theorem search_none {extent : Nat} {left right : List Z4Link} {ids : List Nat} :
    ∀ candidates : List (List Nat), search extent left right ids candidates = none →
    ∀ cut, cut ∈ candidates →
      ¬LinksDisjoint (left ++ faceLinks extent (cutLeft ids cut))
        (right ++ faceLinks extent (cutRight ids cut))
  | [], _, _, hc => False.elim (List.not_mem_nil hc)
  | cut :: rest, hn, other, ho => by
      simp only [search] at hn
      split at hn
      · cases hn
      · rename_i hcut
        rcases List.mem_cons.mp ho with he | ht
        · subst other
          exact fun hd => hcut ((disjointTest_iff _ _).mpr hd)
        · exact search_none rest hn other ht

def findSeparator (extent : Nat) (left right : List Z4Link) (ids : List Nat) :
    Option (Separator extent left right ids) := search extent left right ids (selections ids)

def keep (extent : Nat) (left right : List Z4Link) (ids : List Nat) : Bool :=
  (findSeparator extent left right ids).isNone

theorem keep_no_cut {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (hk : keep extent left right ids = true) (cut : List Nat) (hc : cut ∈ selections ids) :
    ¬LinksDisjoint (left ++ faceLinks extent (cutLeft ids cut))
      (right ++ faceLinks extent (cutRight ids cut)) := by
  have hn : findSeparator extent left right ids = none := by
    cases he : findSeparator extent left right ids with
    | none => rfl
    | some S => simp only [keep, he, Option.isNone] at hk; cases hk
  exact search_none _ hn cut hc

end YMGap.Continuum.BF4ExactSlabSelectionSeparation

#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.cutLeft
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.cutRight
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.cut_partition
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.faceLinks_mono
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.cutLeft_mono
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.cutRight_mono
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.Separator
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.Separator.restrict
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.disjointTest
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.disjointTest_iff
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.search
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.search_none
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.findSeparator
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.keep
#print axioms YMGap.Continuum.BF4ExactSlabSelectionSeparation.keep_no_cut
