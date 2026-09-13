/-
# A retained ORIGINAL coefficient has an actual two-probe connecting path

The old rooted graph joins both probes at one virtual vertex. Here they
are distinct vertices. If the right probe is outside the left component,
that computed component gives an explicit separating cut of the SAME face
list. The existing retained-coefficient test excludes that cut. Hence the
two probes have a constructed Type-valued path, with no assumed bridge.

Every face in the old common-root core is then in this genuine component.
This is literal link geometry, with no group/coupling input and no decay
claim. Replacing the two probe vertices by their own connected carriers
and counting the resulting animals is the next quantitative step.
-/

import YMGap.Continuum.BF4ExactSlabRootedSelection
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound

namespace YMGap.Continuum.BF4ExactSlabTwoProbeGraph

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound (sharedLink)
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent

inductive Node where
  | left
  | right
  | face (id : Nat)
  deriving DecidableEq

def nodeLinks (extent : Nat) (left right : List Z4Link) : Node → List Z4Link
  | .left => left
  | .right => right
  | .face id => faceLinks extent [id]

def adjacent (extent : Nat) (left right : List Z4Link) (a b : Node) : Bool :=
  !(disjointTest (nodeLinks extent left right a) (nodeLinks extent left right b))

theorem adjacent_sym (extent : Nat) (left right : List Z4Link) : SymmetricAdj (adjacent extent left right) := by
  intro a b
  apply congrArg Bool.not
  apply Bool.eq_iff_iff.mpr
  rw [disjointTest_iff, disjointTest_iff]
  exact ⟨fun h link hr hl => h link hl hr, fun h link hl hr => h link hr hl⟩

def vertices (ids : List Nat) : List Node := .left :: .right :: ids.map Node.face

theorem face_mem_vertices (ids : List Nat) (id : Nat) : Node.face id ∈ vertices ids ↔ id ∈ ids := by
  constructor
  · intro h
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
    obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    exact Node.face.inj he ▸ hj
  · intro h
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨id, h, rfl⟩))

def component (extent : Nat) (left right : List Z4Link) (ids : List Nat) : List Node :=
  rootComponent (adjacent extent left right) (vertices ids) .left

theorem left_mem_component (extent : Nat) (left right : List Z4Link) (ids : List Nat) :
    Node.left ∈ component extent left right ids :=
  root_mem_rootComponent _ (show Node.left ∈ vertices ids from List.mem_cons_self)

def componentCut (extent : Nat) (left right : List Z4Link) (ids : List Nat) : List Nat :=
  ids.filter (fun id => decide (Node.face id ∈ component extent left right ids))

theorem cutLeft_inside {extent : Nat} {left right : List Z4Link} {ids : List Nat} {id : Nat}
    (hi : id ∈ cutLeft ids (componentCut extent left right ids)) :
    Node.face id ∈ component extent left right ids :=
  of_decide_eq_true (List.mem_filter.mp (of_decide_eq_true (List.mem_filter.mp hi).2)).2

theorem cutRight_outside {extent : Nat} {left right : List Z4Link} {ids : List Nat} {id : Nat}
    (hi : id ∈ cutRight ids (componentCut extent left right ids)) :
    Node.face id ∉ component extent left right ids := by
  intro hc
  have hm : id ∈ componentCut extent left right ids := List.mem_filter.mpr
    ⟨(List.mem_filter.mp hi).1, decide_eq_true hc⟩
  have hn := (List.mem_filter.mp hi).2
  simp only [decide_eq_true hm, Bool.not_true] at hn
  cases hn

/-- This finite cut is data; it uses the actual original separator type. -/
def separatorOfRightOutside (extent : Nat) (left right : List Z4Link) (ids : List Nat)
    (hr : Node.right ∉ component extent left right ids) : Separator extent left right ids where
  cut := componentCut extent left right ids
  disjoint := by
    have sep (a b : Node) (ha : a ∈ component extent left right ids)
        (hb : b ∈ vertices ids) (hout : b ∉ component extent left right ids) :
        LinksDisjoint (nodeLinks extent left right a) (nodeLinks extent left right b) := by
      have h := rootComponent_adj_false_of_not_mem (adjacent extent left right) (adjacent_sym extent left right)
        (show Node.left ∈ vertices ids from List.mem_cons_self) ha hb hout
      apply (disjointTest_iff _ _).mp
      simpa only [adjacent, Bool.not_eq_false'] using h
    intro link hl hright
    have inNode : ∃ a, a ∈ component extent left right ids ∧ link ∈ nodeLinks extent left right a := by
      rcases List.mem_append.mp hl with hl | hl
      · exact ⟨.left, left_mem_component _ _ _ _, hl⟩
      · obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hl
        exact ⟨.face id, cutLeft_inside hi, List.mem_flatMap.mpr ⟨id, List.mem_cons_self, he⟩⟩
    obtain ⟨a, ha, hlink⟩ := inNode
    rcases List.mem_append.mp hright with hright | hright
    · exact sep a .right ha (List.mem_cons_of_mem _ List.mem_cons_self) hr link hlink hright
    · obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hright
      exact sep a (.face id) ha ((face_mem_vertices ids id).mpr (List.mem_filter.mp hi).1)
        (cutRight_outside hi) link hlink (List.mem_flatMap.mpr ⟨id, List.mem_cons_self, he⟩)

theorem right_mem_of_keep {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (hk : keep extent left right ids = true) : Node.right ∈ component extent left right ids := by
  by_cases hr : Node.right ∈ component extent left right ids
  · exact hr
  · exact False.elim (keep_no_cut hk (componentCut extent left right ids) (filter_selected _ _)
      (separatorOfRightOutside extent left right ids hr).disjoint)

/-- A Type-valued chain between DISTINCT probe vertices, not mere reachability. -/
def probePath (extent : Nat) (left right : List Z4Link) (ids : List Nat)
    (hk : keep extent left right ids = true) : ChainIn (adjacent extent left right) (vertices ids) .left .right :=
  ChainIn.mono (fun _ hp => rootComponent_subset _ (show Node.left ∈ vertices ids from List.mem_cons_self) hp)
    (rootComponent_connected _ (adjacent_sym extent left right)
      (show Node.left ∈ vertices ids from List.mem_cons_self) .left .right
      (left_mem_component _ _ _ _) (right_mem_of_keep hk))

theorem adjacent_of_shared {extent : Nat} {left right : List Z4Link} {a b : Node}
    (link : Z4Link) (ha : link ∈ nodeLinks extent left right a) (hb : link ∈ nodeLinks extent left right b) :
    adjacent extent left right a b = true := by
  have hn : disjointTest (nodeLinks extent left right a) (nodeLinks extent left right b) ≠ true :=
    fun h => (disjointTest_iff _ _).mp h link ha hb
  cases he : disjointTest (nodeLinks extent left right a) (nodeLinks extent left right b) with
  | false => simp only [adjacent, he, Bool.not_false]
  | true => exact False.elim (hn he)

private def mergedIn (extent : Nat) (left right : List Z4Link) (ids : List Nat) : Option Nat → Prop
  | none => True
  | some id => Node.face id ∈ component extent left right ids

private theorem merged_edge {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (hr : Node.right ∈ component extent left right ids) {a b : Option Nat}
    (ha : mergedIn extent left right ids a) (hb : b ∈ BF4ExactSlabRootedSelection.vertices ids)
    (he : BF4ExactSlabRootedSelection.adjacent extent (left++right) a b = true) :
    mergedIn extent left right ids b := by
  cases b with
  | none => trivial
  | some id =>
      have hi : id ∈ ids := by
        simpa only [BF4ExactSlabRootedSelection.vertices, List.mem_cons, List.mem_map,
          Option.some.injEq, Option.some_ne_none, false_or, exists_eq_right] using hb
      have close (source target : Node) := rootComponent_closed_under_edge
        (source := source) (target := target) (adjacent extent left right) (adjacent_sym extent left right)
        (show Node.left ∈ vertices ids from List.mem_cons_self)
      cases a with
      | none =>
          have hd : disjointTest (left++right) (faceLinks extent [id]) = false := by
            simpa only [BF4ExactSlabRootedSelection.adjacent, BF4ExactSlabRootedSelection.nodeLinks,
              Bool.not_eq_true'] using he
          obtain ⟨link, hl, hf⟩ := sharedLink _ _ hd
          rcases List.mem_append.mp hl with hl | hl
          · exact close .left (.face id) (left_mem_component _ _ _ _) ((face_mem_vertices ids id).mpr hi)
              (adjacent_of_shared (a := .left) (b := .face id) link hl hf)
          · exact close .right (.face id) hr ((face_mem_vertices ids id).mpr hi)
              (adjacent_of_shared (a := .right) (b := .face id) link hl hf)
      | some j => exact close (.face j) (.face id) ha ((face_mem_vertices ids id).mpr hi) he

private theorem merged_path {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (hr : Node.right ∈ component extent left right ids) : {a b : Option Nat} →
    ChainIn (BF4ExactSlabRootedSelection.adjacent extent (left++right))
      (BF4ExactSlabRootedSelection.vertices ids) a b →
    mergedIn extent left right ids a → mergedIn extent left right ids b
  | _, _, .refl _, ha => ha
  | _, _, .step he hb rest, ha => merged_path hr rest (merged_edge hr ha hb he)

theorem core_face_mem {extent : Nat} {left right : List Z4Link} {ids : List Nat}
    (hk : keep extent left right ids = true) (id : Nat)
    (hi : id ∈ BF4ExactSlabRootedSelection.core extent (left++right) ids) :
    Node.face id ∈ component extent left right ids := by
  have hroot : none ∈ BF4ExactSlabRootedSelection.vertices ids := List.mem_cons_self
  have path := rootComponent_connected (BF4ExactSlabRootedSelection.adjacent extent (left++right))
    (BF4ExactSlabRootedSelection.adjacent_sym extent (left++right)) hroot none (some id)
    (root_mem_rootComponent _ hroot) (BF4ExactSlabRootedSelection.core_mem_iff.mp hi).2
  exact merged_path (right_mem_of_keep hk)
    (ChainIn.mono (fun _ hp => rootComponent_subset _ hroot hp) path) True.intro

def coreFacePath (extent : Nat) (left right : List Z4Link) (ids : List Nat)
    (hk : keep extent left right ids = true) (id : Nat)
    (hi : id ∈ BF4ExactSlabRootedSelection.core extent (left++right) ids) :
    ChainIn (adjacent extent left right) (vertices ids) .left (.face id) :=
  ChainIn.mono (fun _ hp => rootComponent_subset _ (show Node.left ∈ vertices ids from List.mem_cons_self) hp)
    (rootComponent_connected _ (adjacent_sym extent left right)
      (show Node.left ∈ vertices ids from List.mem_cons_self) .left (.face id)
      (left_mem_component _ _ _ _) (core_face_mem hk id hi))

end YMGap.Continuum.BF4ExactSlabTwoProbeGraph

#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.nodeLinks
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.adjacent
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.adjacent_sym
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.vertices
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.face_mem_vertices
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.component
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.left_mem_component
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.componentCut
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.cutLeft_inside
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.cutRight_outside
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.separatorOfRightOutside
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.right_mem_of_keep
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.probePath
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.adjacent_of_shared
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.core_face_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeGraph.coreFacePath
