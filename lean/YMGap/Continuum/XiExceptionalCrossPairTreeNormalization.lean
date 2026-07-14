/-
# Terminating cross-pair normalization into an occurrence tree

Whenever the two pending occurrence masks fail the finite cross-side
compatibility check, this module constructively selects the first bad left
occurrence and then its first conflicting right occurrence.  A certified
state attaches that pair to a fresh occurrence tree and clears both bits.
The exact potential law is `-2` pending bits and `+2` tree vertices.

This is the recursive combinatorial core of the exceptional allocator.  The
source adapter and its terminal carrier gates are kept in a successor module.
-/

import YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
import YMGap.Continuum.XiExceptionalFirstConflictPotential
import YMGap.Continuum.XiExceptionalFirstConflictActivity

namespace YMGap.Continuum.XiExceptionalCrossPairTreeNormalization

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiExceptionalMergedIncompatibleSplit
open YMGap.Continuum.XiExceptionalConflictRelevantLeft
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalFirstConflictActivity
open YMGap.Continuum.XiExceptionalCrossConflictEar
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalParallelSourceSide

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## A data-valued selector for a failed cross check -/

private theorem occurrenceIndices_sound : forall {n i : Nat},
    i ∈ occurrenceIndices n -> i < n
  | 0, _, hi => by cases hi
  | n + 1, 0, _ => by omega
  | n + 1, i + 1, hi => by
      have ht : i ∈ occurrenceIndices n := by
        rcases List.mem_cons.mp hi with hzero | htail
        · cases hzero
        · obtain ⟨j, hj, hji⟩ := List.mem_map.mp htail
          injection hji with h
          subst j
          exact hj
      have := occurrenceIndices_sound ht
      omega

private theorem all_not_not_eq (f : a -> Bool) : forall xs : List a,
    xs.all (fun x => !(!(f x))) = xs.all f
  | [] => rfl
  | x :: xs => by
      simp only [List.all_cons]
      rw [all_not_not_eq f xs]
      cases f x <;> rfl

def firstCrossBadLeft (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) : Nat :=
  firstTrueOn 0 (fun i =>
    !((!left.at i) ||
      (occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j))))
    (occurrenceIndices Gamma.length)

theorem firstCrossBadLeft_spec (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length)
    (hcross : crossResidualCompatibleB Gamma left right = false) :
    let i := firstCrossBadLeft Gamma left right
    i < Gamma.length ∧ left.at i = true ∧
      (crossBadLeftBits Gamma left right).at i = true := by
  have hfirst := firstTrueOn_mem_and_true 0 (fun i =>
      !((!left.at i) ||
        (occurrenceIndices Gamma.length).all (fun j =>
          (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j))))
    (occurrenceIndices Gamma.length) (by
      rw [all_not_not_eq]
      unfold crossResidualCompatibleB at hcross
      exact hcross)
  let i := firstCrossBadLeft Gamma left right
  have hiMem : i ∈ occurrenceIndices Gamma.length := by
    exact hfirst.1
  have hi : i < Gamma.length := occurrenceIndices_sound hiMem
  have hiBad :
      Bool.not ((!left.at i) ||
        (occurrenceIndices Gamma.length).all (fun j =>
          (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j))) =
        true := by
    exact hfirst.2
  have hleft : left.at i = true := by
    cases hl : left.at i with
    | true => rfl
    | false =>
        simp only [hl, Bool.not_false, Bool.true_or,
          Bool.not_true] at hiBad
        cases hiBad
  have hinner :
      (occurrenceIndices Gamma.length).all (fun j =>
        (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)) =
        false := by
    cases h : (occurrenceIndices Gamma.length).all (fun j =>
      (!right.at j) || compatibleB (polyAt Gamma i) (polyAt Gamma j)) with
    | false => rfl
    | true =>
        simp only [hleft, Bool.not_true, h, Bool.false_or] at hiBad
        cases hiBad
  have hbad : (crossBadLeftBits Gamma left right).at i = true := by
    rw [crossBadLeftBits_at Gamma left right i hi]
    rw [hleft, hinner]
    rfl
  exact ⟨hi, hleft, hbad⟩

structure CrossPairSelection (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length) : Type where
  leftIndex : Nat
  rightIndex : Nat
  left_lt : leftIndex < Gamma.length
  right_lt : rightIndex < Gamma.length
  left_mem : left.at leftIndex = true
  right_mem : right.at rightIndex = true
  cross_conflict :
    compatibleB (polyAt Gamma leftIndex) (polyAt Gamma rightIndex) = false

def selectCrossPair (Gamma : List (Polymer L))
    (left right : OccBitVec Gamma.length)
    (hcross : crossResidualCompatibleB Gamma left right = false) :
    CrossPairSelection Gamma left right := by
  let i := firstCrossBadLeft Gamma left right
  have hi := firstCrossBadLeft_spec Gamma left right hcross
  let j := firstRightConflictIndex Gamma right i
  have hj := firstRightConflictIndex_spec Gamma left right i hi.1 hi.2.2
  exact
    { leftIndex := i
      rightIndex := j
      left_lt := hi.1
      right_lt := hj.1
      left_mem := hi.2.1
      right_mem := hj.2.1
      cross_conflict := hj.2.2 }

/-! ## Clearing lemmas -/

theorem clearResidualAt_submask : forall {n : Nat}
    (bits : OccBitVec n) (selected k : Nat),
    (clearResidualAt bits selected).at k = true -> bits.at k = true
  | 0, .nil, _, _, h => by cases h
  | _ + 1, .cons head tail, 0, 0, h => by cases h
  | _ + 1, .cons head tail, 0, k + 1, h => h
  | _ + 1, .cons head tail, selected + 1, 0, h => h
  | _ + 1, .cons head tail, selected + 1, k + 1, h =>
      clearResidualAt_submask tail selected k h

theorem clearResidualAt_true_ne_selected {n : Nat}
    (bits : OccBitVec n) (selected k : Nat)
    (htrue : (clearResidualAt bits selected).at k = true)
    (hselected : selected < n) : k ≠ selected := by
  intro hEq
  subst k
  rw [clearResidualAt_at_self_false bits selected hselected] at htrue
  cases htrue

theorem clearResidualAt_disjoint {n : Nat}
    (left right : OccBitVec n) (i j : Nat)
    (hdisjoint : DisjointBits left right) :
    DisjointBits (clearResidualAt left i) (clearResidualAt right j) := by
  intro k hkLeft
  have hkOriginal := clearResidualAt_submask left i k hkLeft
  have hkRightFalse := hdisjoint k hkOriginal
  cases hkNew : (clearResidualAt right j).at k with
  | false => rfl
  | true =>
      have := clearResidualAt_submask right j k hkNew
      rw [hkRightFalse] at this
      cases this

private theorem pathSafe_cons_of_tail_false
    (Gamma : List (Polymer L)) (head : Nat) (tail : List Nat) (i : Nat)
    (hfalse : pathSafe Gamma tail i = false) :
    pathSafe Gamma (head :: tail) i = false := by
  unfold pathSafe at hfalse ⊢
  simp only [List.all_cons, hfalse, Bool.and_false]

/-! ## Certified states and one exact step -/

structure CrossTreeState (Gamma : List (Polymer L)) (root : Nat) : Type where
  tree : OTree (incAtDistinct Gamma) root
  left : OccBitVec Gamma.length
  right : OccBitVec Gamma.length
  valid : tree.Valid
  nodup : tree.vertices.Nodup
  vertices_bound : forall k, k ∈ tree.vertices -> k < Gamma.length
  left_compatible : familyCompatibleB (selectByBits Gamma left) = true
  right_compatible : familyCompatibleB (selectByBits Gamma right) = true
  disjoint : DisjointBits left right
  left_unsafe : forall i, i < Gamma.length -> left.at i = true ->
    pathSafe Gamma tree.vertices i = false
  left_fresh : forall i, i < Gamma.length -> left.at i = true ->
    i ∉ tree.vertices
  right_fresh : forall i, i < Gamma.length -> right.at i = true ->
    i ∉ tree.vertices

def CrossTreeState.crossCheckB {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) : Bool :=
  crossResidualCompatibleB Gamma state.left state.right

def CrossTreeState.potential {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) : Nat :=
  residualPotential state.left + residualPotential state.right

def CrossTreeState.selection {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root)
    (hcross : state.crossCheckB = false) :
    CrossPairSelection Gamma state.left state.right :=
  selectCrossPair Gamma state.left state.right hcross

def CrossTreeState.step {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root)
    (hcross : state.crossCheckB = false) : CrossTreeState Gamma root := by
  let pair := state.selection hcross
  let u := pair.leftIndex
  let v := pair.rightIndex
  have huUnsafe := state.left_unsafe u pair.left_lt pair.left_mem
  let pivot := firstConflictIndex Gamma state.tree.vertices u
  have hpivot := firstConflictIndex_mem_and_conflict
    Gamma state.tree.vertices u huUnsafe
  have hpu := incAtDistinct_of_symConflict_true Gamma pivot u hpivot.2
  have hpairNe : pair.leftIndex ≠ pair.rightIndex := by
    intro hEq
    have hfalse := state.disjoint pair.leftIndex pair.left_mem
    have htrue : state.right.at pair.leftIndex = true := by
      rw [hEq]
      exact pair.right_mem
    rw [htrue] at hfalse
    cases hfalse
  have huvNe : u ≠ v := by simpa [u, v] using hpairNe
  have huv := incAtDistinct_of_distinct_incompatible Gamma u v huvNe
    pair.cross_conflict
  let nextTree := state.tree.attachTwo pivot u v hpu huv
  refine
    { tree := nextTree
      left := clearResidualAt state.left u
      right := clearResidualAt state.right v
      valid := OTree.attachTwo_valid state.tree pivot u v hpivot.1 hpu huv
        state.valid
      nodup := OTree.attachTwo_nodup state.tree pivot u v hpu huv
        state.nodup
        (state.left_fresh u pair.left_lt pair.left_mem)
        (state.right_fresh v pair.right_lt pair.right_mem)
        (Ne.symm huvNe)
      vertices_bound := OTree.attachTwo_vertices_bound state.tree pivot u v
        hpu huv Gamma.length state.vertices_bound pair.left_lt pair.right_lt
      left_compatible := selectByBits_compatible_of_submask Gamma _ state.left
        (clearResidualAt_submask state.left u) state.left_compatible
      right_compatible := selectByBits_compatible_of_submask Gamma _ state.right
        (clearResidualAt_submask state.right v) state.right_compatible
      disjoint := clearResidualAt_disjoint state.left state.right u v
        state.disjoint
      left_unsafe := ?_
      left_fresh := ?_
      right_fresh := ?_ }
  · intro k hk hkLeft
    have hkOld := clearResidualAt_submask state.left u k hkLeft
    have hOldUnsafe := state.left_unsafe k hk hkOld
    change pathSafe Gamma (v :: u :: state.tree.vertices) k = false
    exact pathSafe_cons_of_tail_false Gamma v (u :: state.tree.vertices) k
      (pathSafe_cons_of_tail_false Gamma u state.tree.vertices k hOldUnsafe)
  · intro k hk hkLeft
    have hkOld := clearResidualAt_submask state.left u k hkLeft
    have hku := clearResidualAt_true_ne_selected state.left u k hkLeft
      pair.left_lt
    have hkv : k ≠ v := by
      intro hkvEq
      subst k
      have hfalse := state.disjoint v hkOld
      rw [pair.right_mem] at hfalse
      cases hfalse
    change k ∉ v :: u :: state.tree.vertices
    intro hmem
    rcases List.mem_cons.mp hmem with hEqV | hmem
    · exact hkv hEqV
    · rcases List.mem_cons.mp hmem with hEqU | hmem
      · exact hku hEqU
      · exact state.left_fresh k hk hkOld hmem
  · intro k hk hkRight
    have hkOld := clearResidualAt_submask state.right v k hkRight
    have hkv := clearResidualAt_true_ne_selected state.right v k hkRight
      pair.right_lt
    have hku : k ≠ u := by
      intro hkuEq
      subst k
      have hfalse := state.disjoint u pair.left_mem
      rw [hkOld] at hfalse
      cases hfalse
    change k ∉ v :: u :: state.tree.vertices
    intro hmem
    rcases List.mem_cons.mp hmem with hEqV | hmem
    · exact hkv hEqV
    · rcases List.mem_cons.mp hmem with hEqU | hmem
      · exact hku hEqU
      · exact state.right_fresh k hk hkOld hmem

theorem CrossTreeState.step_potential_add_two
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root)
    (hcross : state.crossCheckB = false) :
    (state.step hcross).potential + 2 = state.potential := by
  let pair := state.selection hcross
  have hleft := residualPotential_clearResidualAt_add_one state.left
    pair.leftIndex pair.left_mem
  have hright := residualPotential_clearResidualAt_add_one state.right
    pair.rightIndex pair.right_mem
  change residualPotential (clearResidualAt state.left pair.leftIndex) +
      residualPotential (clearResidualAt state.right pair.rightIndex) + 2 =
    residualPotential state.left + residualPotential state.right
  omega

theorem CrossTreeState.step_potential_lt
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root)
    (hcross : state.crossCheckB = false) :
    (state.step hcross).potential < state.potential := by
  have h := state.step_potential_add_two hcross
  omega

theorem CrossTreeState.step_vertices_length
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root)
    (hcross : state.crossCheckB = false) :
    (state.step hcross).tree.vertices.length =
      state.tree.vertices.length + 2 := by
  let pair := state.selection hcross
  let pivot := firstConflictIndex Gamma state.tree.vertices pair.leftIndex
  exact OTree.attachTwo_vertices_length state.tree pivot pair.leftIndex
    pair.rightIndex _ _

/-! Every occurrence property carried by the initial tree and pending masks
survives normalization. -/

structure CrossTreeState.AllGood {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) (good : Nat -> Prop) : Prop where
  tree : forall i, i ∈ state.tree.vertices -> good i
  left : forall i, i < Gamma.length -> state.left.at i = true -> good i
  right : forall i, i < Gamma.length -> state.right.at i = true -> good i

theorem CrossTreeState.AllGood.step
    {Gamma : List (Polymer L)} {root : Nat}
    {state : CrossTreeState Gamma root} {good : Nat -> Prop}
    (hgood : state.AllGood good)
    (hcross : state.crossCheckB = false) :
    (state.step hcross).AllGood good := by
  let pair := state.selection hcross
  refine
    { tree := ?_
      left := ?_
      right := ?_ }
  · intro i hi
    change i ∈ pair.rightIndex :: pair.leftIndex :: state.tree.vertices at hi
    rcases List.mem_cons.mp hi with hright | hi
    · rw [hright]
      exact hgood.right pair.rightIndex pair.right_lt pair.right_mem
    · rcases List.mem_cons.mp hi with hleft | hi
      · rw [hleft]
        exact hgood.left pair.leftIndex pair.left_lt pair.left_mem
      · exact hgood.tree i hi
  · intro i hi hmem
    exact hgood.left i hi (clearResidualAt_submask state.left
      pair.leftIndex i hmem)
  · intro i hi hmem
    exact hgood.right i hi (clearResidualAt_submask state.right
      pair.rightIndex i hmem)

/-! ## Exact activity conservation -/

def CrossTreeState.totalActivity (w : Q')
    (label : L.Plaquette -> Rep)
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) : Q' :=
  (state.tree.activity (fun i => activity w (polyAt Gamma i) label) *
    residualActivity w label Gamma state.left) *
      residualActivity w label Gamma state.right

theorem CrossTreeState.step_totalActivity_eqv
    (w : Q') (label : L.Plaquette -> Rep)
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root)
    (hcross : state.crossCheckB = false) :
    (state.step hcross).totalActivity w label ≈
      state.totalActivity w label := by
  let pair := state.selection hcross
  have hleft := residualActivity_clearResidualAt_eqv w label Gamma
    state.left pair.leftIndex pair.left_mem
  have hright := residualActivity_clearResidualAt_eqv w label Gamma
    state.right pair.rightIndex pair.right_mem
  have huUnsafe := state.left_unsafe pair.leftIndex pair.left_lt pair.left_mem
  have hpivot := firstConflictIndex_mem_and_conflict Gamma state.tree.vertices
    pair.leftIndex huUnsafe
  have hpu := incAtDistinct_of_symConflict_true Gamma
    (firstConflictIndex Gamma state.tree.vertices pair.leftIndex)
    pair.leftIndex hpivot.2
  have hne : pair.leftIndex ≠ pair.rightIndex := by
    intro hEq
    have hfalse := state.disjoint pair.leftIndex pair.left_mem
    have htrue : state.right.at pair.leftIndex = true := by
      rw [hEq]
      exact pair.right_mem
    rw [htrue] at hfalse
    cases hfalse
  have huv := incAtDistinct_of_distinct_incompatible Gamma
    pair.leftIndex pair.rightIndex hne pair.cross_conflict
  have htree := OTree.attachTwo_activity_eqv
    (fun i => activity w (polyAt Gamma i) label) state.tree
    (firstConflictIndex Gamma state.tree.vertices pair.leftIndex)
    pair.leftIndex pair.rightIndex hpu huv
  unfold CrossTreeState.totalActivity
  change (((state.tree.attachTwo
      (firstConflictIndex Gamma state.tree.vertices pair.leftIndex)
      pair.leftIndex pair.rightIndex hpu huv).activity
        (fun i => activity w (polyAt Gamma i) label) *
      residualActivity w label Gamma
        (clearResidualAt state.left pair.leftIndex)) *
    residualActivity w label Gamma
      (clearResidualAt state.right pair.rightIndex)) ≈ _
  let mid : Q' :=
    (((state.tree.activity (fun i => activity w (polyAt Gamma i) label) *
        activity w (polyAt Gamma pair.leftIndex) label) *
          activity w (polyAt Gamma pair.rightIndex) label) *
      residualActivity w label Gamma
        (clearResidualAt state.left pair.leftIndex)) *
    residualActivity w label Gamma
      (clearResidualAt state.right pair.rightIndex)
  refine Q'.eqv_trans _ mid _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ htree)
  · let regrouped : Q' :=
      (state.tree.activity (fun i => activity w (polyAt Gamma i) label) *
        (activity w (polyAt Gamma pair.leftIndex) label *
          residualActivity w label Gamma
            (clearResidualAt state.left pair.leftIndex))) *
        (activity w (polyAt Gamma pair.rightIndex) label *
          residualActivity w label Gamma
            (clearResidualAt state.right pair.rightIndex))
    refine Q'.eqv_trans _ regrouped _ ?_ ?_
    · unfold mid regrouped
      ring_qeqv
    · refine Q'.eqv_trans _
        ((state.tree.activity (fun i => activity w (polyAt Gamma i) label) *
          residualActivity w label Gamma state.left) *
            (activity w (polyAt Gamma pair.rightIndex) label *
              residualActivity w label Gamma
                (clearResidualAt state.right pair.rightIndex))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hleft))
      · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hright)

def CrossTreeState.exhaust {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) : CrossTreeState Gamma root :=
  if hcross : state.crossCheckB = false then
    CrossTreeState.exhaust (state.step hcross)
  else state
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem CrossTreeState.exhaust_crossCheckB_true
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) :
    state.exhaust.crossCheckB = true := by
  rw [CrossTreeState.exhaust]
  split
  next hcross =>
    exact CrossTreeState.exhaust_crossCheckB_true (state.step hcross)
  next hnot =>
    cases h : state.crossCheckB
    · exact False.elim (hnot h)
    · rfl
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem CrossTreeState.AllGood.exhaust
    {Gamma : List (Polymer L)} {root : Nat}
    {state : CrossTreeState Gamma root} {good : Nat -> Prop}
    (hgood : state.AllGood good) : state.exhaust.AllGood good := by
  rw [CrossTreeState.exhaust]
  split
  next hcross =>
    exact (hgood.step hcross).exhaust
  next _ => exact hgood
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem CrossTreeState.exhaust_totalActivity_eqv
    (w : Q') (label : L.Plaquette -> Rep)
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) :
    state.exhaust.totalActivity w label ≈ state.totalActivity w label := by
  rw [CrossTreeState.exhaust]
  split
  next hcross =>
    exact Q'.eqv_trans _ _ _
      (CrossTreeState.exhaust_totalActivity_eqv w label (state.step hcross))
      (state.step_totalActivity_eqv w label hcross)
  next _ => exact Q'.eqv_refl _
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem CrossTreeState.exhaust_external_compatible
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) :
    familyCompatibleB (selectByBits Gamma
      (unionBits state.exhaust.left state.exhaust.right)) = true :=
  unionBits_compatible_of_cross Gamma state.exhaust.left state.exhaust.right
    state.exhaust.left_compatible state.exhaust.right_compatible
    state.exhaust_crossCheckB_true

#print axioms firstCrossBadLeft_spec
#print axioms selectCrossPair
#print axioms clearResidualAt_submask
#print axioms clearResidualAt_true_ne_selected
#print axioms clearResidualAt_disjoint
#print axioms CrossTreeState.step
#print axioms CrossTreeState.step_potential_add_two
#print axioms CrossTreeState.step_potential_lt
#print axioms CrossTreeState.step_vertices_length
#print axioms CrossTreeState.AllGood.step
#print axioms CrossTreeState.step_totalActivity_eqv
#print axioms CrossTreeState.exhaust
#print axioms CrossTreeState.exhaust_crossCheckB_true
#print axioms CrossTreeState.AllGood.exhaust
#print axioms CrossTreeState.exhaust_totalActivity_eqv
#print axioms CrossTreeState.exhaust_external_compatible

end YMGap.Continuum.XiExceptionalCrossPairTreeNormalization
