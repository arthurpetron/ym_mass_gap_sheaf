/-
# Occurrence-tree carrier for cross-conflict branches

Linear endpoint-preserving ears repeat their articulation and overspend walk
fuel.  A rooted occurrence tree records the same connected object without a
return traversal.  Attaching `u` to an old pivot and `v` to `u` then costs
exactly two vertices and multiplies the activity by exactly the two new
activities.

This is carrier infrastructure, not yet a domination theorem: the existing
`connectingChainMajorant` enumerates linear walks.  A later module must either
enumerate these trees directly or dominate their finite sum by an accepted
majorant.
-/

import YMGap.Continuum.XiExceptionalCrossConflictEar

namespace YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalPathExtraction

local infix:50 " ≈ " => Q'.eqv

/-! ## Rooted occurrence trees -/

inductive OTree {a : Type} (edge : a -> a -> Bool) : a -> Type
  | single (root : a) : OTree edge root
  | prepend {root next : a} (hedge : edge root next = true)
      (tree : OTree edge next) : OTree edge root
  | attach {root : a} (tree : OTree edge root) (parent child : a)
      (hedge : edge parent child = true) :
      OTree edge root

def OTree.vertices {a : Type} {edge : a -> a -> Bool} {root : a} :
    OTree edge root -> List a
  | .single root => [root]
  | .prepend _ tree => root :: tree.vertices
  | .attach tree _ child _ => child :: tree.vertices

/-- Validity records that every attached child is joined to a vertex already
present in the tree. -/
def OTree.Valid {a : Type} {edge : a -> a -> Bool} {root : a} :
    OTree edge root -> Prop
  | .single _ => True
  | .prepend _ tree => tree.Valid
  | .attach tree parent _ _ => tree.Valid ∧ parent ∈ tree.vertices

theorem OTree.root_mem {a : Type} {edge : a -> a -> Bool} {root : a} :
    forall tree : OTree edge root, root ∈ tree.vertices
  | .single _ => List.mem_cons_self
  | .prepend _ _ => List.mem_cons_self
  | .attach tree _ child _ =>
      List.mem_cons_of_mem child (OTree.root_mem tree)

/-! ## A canonical tree behind every walk -/

def OTree.ofWalk {a : Type} {edge : a -> a -> Bool} :
    {x y : a} -> CWalk edge x y -> OTree edge x
  | _, _, .single x => .single x
  | _, _, .cons hedge rest => .prepend hedge (OTree.ofWalk rest)

theorem OTree.ofWalk_vertices {a : Type} {edge : a -> a -> Bool} :
    forall {x y : a} (walk : CWalk edge x y),
      (OTree.ofWalk walk).vertices = walk.vertices
  | _, _, .single _ => rfl
  | _, _, .cons _ rest => by
      simp only [OTree.ofWalk, OTree.vertices, CWalk.vertices]
      rw [OTree.ofWalk_vertices rest]

theorem OTree.ofWalk_nodup {a : Type} {edge : a -> a -> Bool}
    {x y : a} (walk : CWalk edge x y) (hnodup : walk.vertices.Nodup) :
    (OTree.ofWalk walk).vertices.Nodup := by
  rw [OTree.ofWalk_vertices]
  exact hnodup

theorem OTree.ofWalk_valid {a : Type} {edge : a -> a -> Bool} :
    forall {x y : a} (walk : CWalk edge x y),
      (OTree.ofWalk walk).Valid
  | _, _, .single _ => trivial
  | _, _, .cons _ rest => OTree.ofWalk_valid rest

/-! ## Two one-use attachments -/

def OTree.attachTwo {a : Type} {edge : a -> a -> Bool} {root : a}
    (tree : OTree edge root) (pivot u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true) :
    OTree edge root :=
  let withU := OTree.attach tree pivot u hpu
  OTree.attach withU u v huv

theorem OTree.attachTwo_vertices {a : Type} {edge : a -> a -> Bool}
    {root : a} (tree : OTree edge root) (pivot u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true) :
    (tree.attachTwo pivot u v hpu huv).vertices =
      v :: u :: tree.vertices := rfl

theorem OTree.attachTwo_vertices_length {a : Type}
    {edge : a -> a -> Bool} {root : a}
    (tree : OTree edge root) (pivot u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true) :
    (tree.attachTwo pivot u v hpu huv).vertices.length =
      tree.vertices.length + 2 := by
  rw [OTree.attachTwo_vertices]
  simp only [List.length_cons]

theorem OTree.attachTwo_valid {a : Type} {edge : a -> a -> Bool}
    {root : a} (tree : OTree edge root) (pivot u v : a)
    (hpivot : pivot ∈ tree.vertices)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (hvalid : tree.Valid) :
    (tree.attachTwo pivot u v hpu huv).Valid := by
  exact ⟨⟨hvalid, hpivot⟩, List.mem_cons_self⟩

theorem OTree.attachTwo_nodup {a : Type} {edge : a -> a -> Bool}
    {root : a} (tree : OTree edge root) (pivot u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (htree : tree.vertices.Nodup)
    (hu : u ∉ tree.vertices) (hvTree : v ∉ tree.vertices) (hvu : v ≠ u) :
    (tree.attachTwo pivot u v hpu huv).vertices.Nodup := by
  rw [OTree.attachTwo_vertices]
  apply List.nodup_cons.mpr
  constructor
  · intro hv
    rcases List.mem_cons.mp hv with hvu' | hvTail
    · exact hvu hvu'
    · exact hvTree hvTail
  · exact List.nodup_cons.mpr ⟨hu, htree⟩

theorem OTree.attachTwo_vertices_bound
    {edge : Nat -> Nat -> Bool} {root : Nat}
    (tree : OTree edge root) (pivot u v : Nat)
    (hpu : edge pivot u = true) (huv : edge u v = true)
    (N : Nat) (hbase : forall k, k ∈ tree.vertices -> k < N)
    (huN : u < N) (hvN : v < N) :
    forall k, k ∈ (tree.attachTwo pivot u v hpu huv).vertices ->
      k < N := by
  intro k hk
  rw [OTree.attachTwo_vertices] at hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact hvN
  · rcases List.mem_cons.mp hk with rfl | hk
    · exact huN
    · exact hbase k hk

/-! ## Activity without traversal multiplicity -/

def OTree.activity {a : Type} {edge : a -> a -> Bool}
    (weight : a -> Q') : {root : a} -> OTree edge root -> Q'
  | _, .single root => weight root
  | root, .prepend _ tree => weight root * tree.activity weight
  | _, .attach tree _ child _ => tree.activity weight * weight child

theorem OTree.ofWalk_activity_eqv {L : Lattice}
    [DecidableEq L.Plaquette]
    (w : Q') (label : L.Plaquette -> Rep) :
    forall {X Y : Polymer L}
      (walk : CWalk (fun A B : Polymer L => !(compatibleB A B)) X Y),
      (OTree.ofWalk walk).activity
          (fun A => YMGap.Continuum.PolymerModel.activity w A label) ≈
        walk.activityWeight w label
  | _, _, .single _ => Q'.eqv_refl _
  | _, _, .cons _ rest => by
      simp only [OTree.ofWalk, OTree.activity, CWalk.activityWeight]
      exact Q'.mul_eqv_congr_left _ _ _
        (OTree.ofWalk_activity_eqv w label rest)

theorem OTree.attachTwo_activity_eqv {a : Type}
    {edge : a -> a -> Bool} {root : a}
    (weight : a -> Q') (tree : OTree edge root) (pivot u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true) :
    (tree.attachTwo pivot u v hpu huv).activity weight ≈
      (tree.activity weight * weight u) * weight v := by
  exact Q'.eqv_refl _

/-- Unlike the linear cross ear, the tree attachment has exact `+2` fuel and
no repeated pivot or left-endpoint activity. -/
theorem OTree.attachTwo_exact_profile {a : Type}
    {edge : a -> a -> Bool} {root : a}
    (weight : a -> Q') (tree : OTree edge root) (pivot u v : a)
    (hpu : edge pivot u = true) (huv : edge u v = true) :
    (tree.attachTwo pivot u v hpu huv).vertices.length =
        tree.vertices.length + 2 ∧
      (tree.attachTwo pivot u v hpu huv).activity weight ≈
        (tree.activity weight * weight u) * weight v :=
  ⟨OTree.attachTwo_vertices_length tree pivot u v hpu huv,
    OTree.attachTwo_activity_eqv weight tree pivot u v hpu huv⟩

#print axioms OTree.root_mem
#print axioms OTree.ofWalk_vertices
#print axioms OTree.ofWalk_nodup
#print axioms OTree.ofWalk_valid
#print axioms OTree.attachTwo_vertices_length
#print axioms OTree.attachTwo_valid
#print axioms OTree.attachTwo_nodup
#print axioms OTree.attachTwo_vertices_bound
#print axioms OTree.ofWalk_activity_eqv
#print axioms OTree.attachTwo_activity_eqv
#print axioms OTree.attachTwo_exact_profile

end YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
