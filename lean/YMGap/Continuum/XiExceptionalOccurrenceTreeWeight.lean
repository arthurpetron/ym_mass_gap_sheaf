/-
# Zero-gated weights for finite occurrence-tree codes

Raw finite tree codes are assigned zero unless all stored occurrences are in
range, every edge is an actual distinct incompatibility, every attachment
parent is already present, the vertex list is duplicate-free, all vertices
are `q`-admissible, the root carries `b1`, and some vertex carries `b2`.

A certified bounded `OTree` erases through all gates and its code activity is
exactly the one-use tree activity.
-/

import YMGap.Continuum.XiExceptionalOccurrenceTreeCodes

namespace YMGap.Continuum.XiExceptionalOccurrenceTreeWeight

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes

local infix:50 " ≈ " => Q'.eqv

/-! ## Boolean validity gates -/

def natMemB (x : Nat) : List Nat -> Bool
  | [] => false
  | y :: ys => decide (x = y) || natMemB x ys

theorem natMemB_true_of_mem (x : Nat) : forall xs : List Nat,
    x ∈ xs -> natMemB x xs = true
  | [], hx => by cases hx
  | y :: ys, hx => by
      rcases List.mem_cons.mp hx with hxy | htail
      · subst y
        simp [natMemB]
      · cases h : decide (x = y) with
        | true => simp [natMemB, h]
        | false =>
            simp only [natMemB, h, Bool.false_or]
            exact natMemB_true_of_mem x ys htail

def treeCodeRoot {N : Nat} : OccTreeCode N -> Nat
  | .single root => root
  | .prepend root _ => root
  | .attach tree _ _ => treeCodeRoot tree

def treeCodeLocalValidB {L : Lattice} [DecidableEq L.Plaquette]
    (Gamma : List (Polymer L)) : OccTreeCode Gamma.length -> Bool
  | .single root => decide (root < Gamma.length)
  | .prepend root tree =>
      decide (root < Gamma.length) && treeCodeLocalValidB Gamma tree &&
        incAtDistinct Gamma root (treeCodeRoot tree)
  | .attach tree parent child =>
      treeCodeLocalValidB Gamma tree && natMemB parent tree.vertices &&
        decide (child < Gamma.length) &&
          incAtDistinct Gamma parent child

def treeCodeAdmissibleB {L : Lattice} [DecidableEq L.Plaquette]
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (code : OccTreeCode Gamma.length) : Bool :=
  treeCodeLocalValidB Gamma code && decide code.vertices.Nodup &&
    b1 (polyAt Gamma (treeCodeRoot code)) &&
      code.vertices.any (fun i => b2 (polyAt Gamma i)) &&
        code.vertices.all (fun i => qP (polyAt Gamma i))

theorem OTree.toCode_root {L : Lattice} [DecidableEq L.Plaquette]
    (Gamma : List (Polymer L)) :
    forall {root : Nat} (tree : OTree (incAtDistinct Gamma) root),
      treeCodeRoot (OTree.toCode (N := Gamma.length) tree) = root
  | _, .single _ => rfl
  | _, .prepend _ _ => rfl
  | _, .attach tree _ _ _ => OTree.toCode_root Gamma tree

theorem OTree.toCode_localValidB {L : Lattice}
    [DecidableEq L.Plaquette] (Gamma : List (Polymer L)) :
    forall {root : Nat} (tree : OTree (incAtDistinct Gamma) root),
      tree.Valid ->
      (forall k, k ∈ tree.vertices -> k < Gamma.length) ->
      treeCodeLocalValidB Gamma
        (OTree.toCode (N := Gamma.length) tree) = true
  | _, .single root, _, hbound => by
      unfold OTree.toCode treeCodeLocalValidB
      exact decide_eq_true (hbound root List.mem_cons_self)
  | _, @OTree.prepend _ _ root next hedge tree, hvalid, hbound => by
      have hroot : root < Gamma.length :=
        hbound root List.mem_cons_self
      have htail : forall k, k ∈ tree.vertices -> k < Gamma.length := by
        intro k hk
        exact hbound k (List.mem_cons_of_mem root hk)
      have ih := OTree.toCode_localValidB Gamma tree hvalid htail
      unfold OTree.toCode treeCodeLocalValidB
      rw [decide_eq_true hroot, ih, OTree.toCode_root Gamma tree, hedge]
      rfl
  | _, @OTree.attach _ _ root tree parent child hedge,
      hvalid, hbound => by
      have htail : forall k, k ∈ tree.vertices -> k < Gamma.length := by
        intro k hk
        exact hbound k (List.mem_cons_of_mem child hk)
      have hchild : child < Gamma.length :=
        hbound child List.mem_cons_self
      have ih := OTree.toCode_localValidB Gamma tree hvalid.1 htail
      have hparentCode :
          natMemB parent
            (OTree.toCode (N := Gamma.length) tree).vertices = true := by
        apply natMemB_true_of_mem
        rw [OTree.toCode_vertices]
        exact hvalid.2
      unfold OTree.toCode treeCodeLocalValidB
      rw [ih, hparentCode, decide_eq_true hchild, hedge]
      rfl

private theorem list_any_true_of_mem_true (p : a -> Bool) :
    forall (xs : List a) (x : a), x ∈ xs -> p x = true -> xs.any p = true
  | [], _, hx, _ => by cases hx
  | y :: ys, x, hx, hpx => by
      rcases List.mem_cons.mp hx with hxy | htail
      · subst y
        simp [hpx]
      · cases hp : p y with
        | true => simp [List.any_cons, hp]
        | false =>
            simp only [List.any_cons, hp, Bool.false_or]
            exact list_any_true_of_mem_true p ys x htail hpx

theorem OTree.toCode_admissibleB {L : Lattice}
    [DecidableEq L.Plaquette]
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    {root : Nat} (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : forall k, k ∈ tree.vertices -> k < Gamma.length)
    (hnodup : tree.vertices.Nodup)
    (hq : forall k, k ∈ tree.vertices -> qP (polyAt Gamma k) = true)
    (hb1 : b1 (polyAt Gamma root) = true)
    (b2Index : Nat) (hb2Mem : b2Index ∈ tree.vertices)
    (hb2 : b2 (polyAt Gamma b2Index) = true) :
    treeCodeAdmissibleB Gamma qP b1 b2
      (OTree.toCode (N := Gamma.length) tree) = true := by
  have hlocal := OTree.toCode_localValidB Gamma tree hvalid hbound
  have hcodeVertices := OTree.toCode_vertices
    (N := Gamma.length) tree
  have hcodeNodup :
      (OTree.toCode (N := Gamma.length) tree).vertices.Nodup := by
    rw [hcodeVertices]
    exact hnodup
  have hb1Code :
      b1 (polyAt Gamma
        (treeCodeRoot (OTree.toCode (N := Gamma.length) tree))) = true := by
    rw [OTree.toCode_root Gamma tree]
    exact hb1
  have hb2Code :
      (OTree.toCode (N := Gamma.length) tree).vertices.any
        (fun i => b2 (polyAt Gamma i)) = true := by
    apply list_any_true_of_mem_true _ _ b2Index
    · rw [hcodeVertices]
      exact hb2Mem
    · exact hb2
  have hqCode :
      (OTree.toCode (N := Gamma.length) tree).vertices.all
        (fun i => qP (polyAt Gamma i)) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    apply hq i
    rw [← hcodeVertices]
    exact hi
  unfold treeCodeAdmissibleB
  rw [hlocal, decide_eq_true hcodeNodup, hb1Code, hb2Code, hqCode]
  rfl

/-! ## Exact one-use activity -/

def treeCodeActivity {L : Lattice} [DecidableEq L.Plaquette]
    (w : Q') (Gamma : List (Polymer L)) (label : L.Plaquette -> Rep) :
    OccTreeCode Gamma.length -> Q'
  | .single root => activity w (polyAt Gamma root) label
  | .prepend root tree =>
      activity w (polyAt Gamma root) label *
        treeCodeActivity w Gamma label tree
  | .attach tree _ child =>
      treeCodeActivity w Gamma label tree *
        activity w (polyAt Gamma child) label

def occurrenceTreeCodeWeight {L : Lattice} [DecidableEq L.Plaquette]
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L -> Bool) (label : L.Plaquette -> Rep)
    (code : OccTreeCode Gamma.length) : Q' :=
  if treeCodeAdmissibleB Gamma qP b1 b2 code then
    treeCodeActivity w Gamma label code
  else 0

theorem OTree.toCode_activity_eqv {L : Lattice}
    [DecidableEq L.Plaquette]
    (w : Q') (Gamma : List (Polymer L)) (label : L.Plaquette -> Rep) :
    forall {root : Nat} (tree : OTree (incAtDistinct Gamma) root),
      treeCodeActivity w Gamma label
          (OTree.toCode (N := Gamma.length) tree) ≈
        tree.activity (fun i => activity w (polyAt Gamma i) label)
  | _, .single _ => Q'.eqv_refl _
  | _, .prepend _ tree => by
      simp only [OTree.toCode, treeCodeActivity, OTree.activity]
      exact Q'.mul_eqv_congr_left _ _ _
        (OTree.toCode_activity_eqv w Gamma label tree)
  | _, .attach tree _ _ _ => by
      simp only [OTree.toCode, treeCodeActivity, OTree.activity]
      exact Q'.mul_eqv_congr_right _ _ _
        (OTree.toCode_activity_eqv w Gamma label tree)

theorem occurrenceTreeCodeWeight_toCode_eqv {L : Lattice}
    [DecidableEq L.Plaquette]
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L -> Bool) (label : L.Plaquette -> Rep)
    {root : Nat} (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : forall k, k ∈ tree.vertices -> k < Gamma.length)
    (hnodup : tree.vertices.Nodup)
    (hq : forall k, k ∈ tree.vertices -> qP (polyAt Gamma k) = true)
    (hb1 : b1 (polyAt Gamma root) = true)
    (b2Index : Nat) (hb2Mem : b2Index ∈ tree.vertices)
    (hb2 : b2 (polyAt Gamma b2Index) = true) :
    occurrenceTreeCodeWeight w Gamma qP b1 b2 label
        (OTree.toCode (N := Gamma.length) tree) ≈
      tree.activity (fun i => activity w (polyAt Gamma i) label) := by
  unfold occurrenceTreeCodeWeight
  rw [OTree.toCode_admissibleB Gamma qP b1 b2 tree hvalid hbound
    hnodup hq hb1 b2Index hb2Mem hb2]
  exact OTree.toCode_activity_eqv w Gamma label tree

#print axioms natMemB_true_of_mem
#print axioms OTree.toCode_root
#print axioms OTree.toCode_localValidB
#print axioms OTree.toCode_admissibleB
#print axioms OTree.toCode_activity_eqv
#print axioms occurrenceTreeCodeWeight_toCode_eqv

end YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
