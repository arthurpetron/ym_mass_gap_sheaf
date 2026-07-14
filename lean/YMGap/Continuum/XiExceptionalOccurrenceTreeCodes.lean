/-
# Finite occurrence codes for rooted conflict trees

The one-use tree carrier is now erased to a proof-free finite syntax.  At a
fixed ambient occurrence count `N` and height fuel, every stored index is
drawn from `occurrenceIndices N`.  The enumeration deliberately includes
invalid parent choices; a later weight function can assign those choices
zero without any classical filtering.

Every valid bounded `OTree` has a constructively computed code in this finite
enumeration at its exact constructor height.
-/

import YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier

namespace YMGap.Continuum.XiExceptionalOccurrenceTreeCodes

open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier

/-! ## Proof-free finite syntax -/

inductive OccTreeCode (N : Nat) : Type
  | single (root : Nat)
  | prepend (root : Nat) (tree : OccTreeCode N)
  | attach (tree : OccTreeCode N) (parent child : Nat)
deriving DecidableEq

def OccTreeCode.height {N : Nat} : OccTreeCode N -> Nat
  | .single _ => 1
  | .prepend _ tree => tree.height + 1
  | .attach tree _ _ => tree.height + 1

def OccTreeCode.vertices {N : Nat} : OccTreeCode N -> List Nat
  | .single root => [root]
  | .prepend root tree => root :: tree.vertices
  | .attach tree _ child => child :: tree.vertices

/-- Every stored index, including an attachment parent, is in range. -/
def OccTreeCode.IndicesBound {N : Nat} : OccTreeCode N -> Prop
  | .single root => root < N
  | .prepend root tree => root < N ∧ tree.IndicesBound
  | .attach tree parent child =>
      tree.IndicesBound ∧ parent < N ∧ child < N

/-! ## Finite enumeration by constructor height -/

def singleTreeCodes (N : Nat) : List (OccTreeCode N) :=
  (occurrenceIndices N).map OccTreeCode.single

def prependTreeCodes (N : Nat) (trees : List (OccTreeCode N)) :
    List (OccTreeCode N) :=
  (occurrenceIndices N).flatMap (fun root =>
    trees.map (OccTreeCode.prepend root))

def attachTreeCodes (N : Nat) (trees : List (OccTreeCode N)) :
    List (OccTreeCode N) :=
  trees.flatMap (fun tree =>
    (occurrenceIndices N).flatMap (fun parent =>
      (occurrenceIndices N).map (OccTreeCode.attach tree parent)))

/-- All bounded raw tree codes of constructor height at most `fuel`, with a
fresh copy of the singleton layer at every positive fuel. -/
def occurrenceTreeCodes (N : Nat) : Nat -> List (OccTreeCode N)
  | 0 => []
  | fuel + 1 =>
      singleTreeCodes N ++
        prependTreeCodes N (occurrenceTreeCodes N fuel) ++
          attachTreeCodes N (occurrenceTreeCodes N fuel)

theorem single_mem_singleTreeCodes {N root : Nat} (hroot : root < N) :
    OccTreeCode.single root ∈ singleTreeCodes N := by
  unfold singleTreeCodes
  exact List.mem_map.mpr
    ⟨root, occurrenceIndices_complete hroot, rfl⟩

theorem prepend_mem_prependTreeCodes {N root : Nat}
    (tree : OccTreeCode N) (hroot : root < N)
    (htree : tree ∈ occurrenceTreeCodes N fuel) :
    OccTreeCode.prepend root tree ∈
      prependTreeCodes N (occurrenceTreeCodes N fuel) := by
  unfold prependTreeCodes
  apply List.mem_flatMap.mpr
  exact ⟨root, occurrenceIndices_complete hroot,
    List.mem_map.mpr ⟨tree, htree, rfl⟩⟩

theorem attach_mem_attachTreeCodes {N parent child : Nat}
    (tree : OccTreeCode N)
    (htree : tree ∈ occurrenceTreeCodes N fuel)
    (hparent : parent < N) (hchild : child < N) :
    OccTreeCode.attach tree parent child ∈
      attachTreeCodes N (occurrenceTreeCodes N fuel) := by
  unfold attachTreeCodes
  apply List.mem_flatMap.mpr
  refine ⟨tree, htree, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨parent, occurrenceIndices_complete hparent,
    List.mem_map.mpr
      ⟨child, occurrenceIndices_complete hchild, rfl⟩⟩

/-- Finite completeness at the code's exact height. -/
theorem OccTreeCode.mem_occurrenceTreeCodes_of_bound {N : Nat} :
    forall code : OccTreeCode N, code.IndicesBound ->
      code ∈ occurrenceTreeCodes N code.height
  | .single root, hbound => by
      unfold OccTreeCode.height occurrenceTreeCodes
      exact List.mem_append_left _
        (List.mem_append_left _ (single_mem_singleTreeCodes hbound))
  | .prepend root tree, hbound => by
      unfold OccTreeCode.height occurrenceTreeCodes
      exact List.mem_append_left _ (List.mem_append_right _
        (prepend_mem_prependTreeCodes tree hbound.1
          (OccTreeCode.mem_occurrenceTreeCodes_of_bound tree hbound.2)))
  | .attach tree parent child, hbound => by
      unfold OccTreeCode.height occurrenceTreeCodes
      exact List.mem_append_right _ (attach_mem_attachTreeCodes tree
          (OccTreeCode.mem_occurrenceTreeCodes_of_bound tree hbound.1)
          hbound.2.1 hbound.2.2)

/-! ## Erasing certified trees -/

def OTree.toCode {N root : Nat} {edge : Nat -> Nat -> Bool} :
    OTree edge root -> OccTreeCode N
  | .single root => .single root
  | .prepend _ tree => .prepend root (OTree.toCode tree)
  | .attach tree parent child _ =>
      .attach (OTree.toCode tree) parent child

theorem OTree.toCode_vertices {N root : Nat}
    {edge : Nat -> Nat -> Bool} :
    forall tree : OTree edge root,
      (OTree.toCode (N := N) tree).vertices = tree.vertices
  | .single _ => rfl
  | .prepend _ tree => by
      simp only [OTree.toCode, OccTreeCode.vertices, OTree.vertices]
      rw [OTree.toCode_vertices tree]
  | .attach tree _ _ _ => by
      simp only [OTree.toCode, OccTreeCode.vertices, OTree.vertices]
      rw [OTree.toCode_vertices tree]

theorem OTree.toCode_height {N root : Nat}
    {edge : Nat -> Nat -> Bool} :
    forall tree : OTree edge root,
      (OTree.toCode (N := N) tree).height = tree.vertices.length
  | .single _ => rfl
  | .prepend _ tree => by
      simp only [OTree.toCode, OccTreeCode.height, OTree.vertices,
        List.length_cons]
      rw [OTree.toCode_height tree]
  | .attach tree _ _ _ => by
      simp only [OTree.toCode, OccTreeCode.height, OTree.vertices,
        List.length_cons]
      rw [OTree.toCode_height tree]

theorem OTree.toCode_indicesBound {N root : Nat}
    {edge : Nat -> Nat -> Bool} :
    forall (tree : OTree edge root), tree.Valid ->
      (forall k, k ∈ tree.vertices -> k < N) ->
      (OTree.toCode (N := N) tree).IndicesBound
  | .single root, _, hbound =>
      hbound root List.mem_cons_self
  | @OTree.prepend _ _ root next hedge tree, hvalid, hbound => by
      constructor
      · exact hbound root List.mem_cons_self
      · apply OTree.toCode_indicesBound tree hvalid
        intro k hk
        exact hbound k (List.mem_cons_of_mem root hk)
  | @OTree.attach _ _ root tree parent child hedge, hvalid, hbound => by
      refine ⟨?_, ?_, ?_⟩
      · apply OTree.toCode_indicesBound tree hvalid.1
        intro k hk
        exact hbound k (List.mem_cons_of_mem child hk)
      · exact hbound parent
          (List.mem_cons_of_mem child hvalid.2)
      · exact hbound child List.mem_cons_self

/-- Every valid occurrence tree whose vertices lie in the ambient list has a
code in the explicit finite enumeration. -/
theorem OTree.toCode_mem_occurrenceTreeCodes {N root : Nat}
    {edge : Nat -> Nat -> Bool} (tree : OTree edge root)
    (hvalid : tree.Valid)
    (hbound : forall k, k ∈ tree.vertices -> k < N) :
    OTree.toCode (N := N) tree ∈
      occurrenceTreeCodes N tree.vertices.length := by
  rw [← OTree.toCode_height (N := N) tree]
  exact OccTreeCode.mem_occurrenceTreeCodes_of_bound _
    (OTree.toCode_indicesBound tree hvalid hbound)

#print axioms OccTreeCode.mem_occurrenceTreeCodes_of_bound
#print axioms OTree.toCode_vertices
#print axioms OTree.toCode_height
#print axioms OTree.toCode_indicesBound
#print axioms OTree.toCode_mem_occurrenceTreeCodes

end YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
