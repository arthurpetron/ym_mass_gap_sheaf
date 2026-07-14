/-
# Terminal background normalization for occurrence trees

Cross-pair normalization can add right-side vertices which conflict with a
previously path-safe background.  This second terminating phase absorbs each
such background occurrence once, as a child of its first conflicting tree
vertex.  At termination the remaining background is compatible with every
tree vertex, while an already-compatible external mask is unchanged.
-/

import YMGap.Continuum.XiExceptionalCrossPairTreeNormalization

namespace YMGap.Continuum.XiExceptionalTreeBackgroundNormalization

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalEntryFirstConflictSplice
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalFirstConflictActivity
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalCrossPairTreeNormalization
open YMGap.Continuum.XiExceptionalParallelSourceSide

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

structure TreeBackgroundState (Gamma : List (Polymer L))
    (root : Nat) : Type where
  tree : OTree (incAtDistinct Gamma) root
  background : OccBitVec Gamma.length
  external : OccBitVec Gamma.length
  valid : tree.Valid
  nodup : tree.vertices.Nodup
  vertices_bound : forall i, i ∈ tree.vertices -> i < Gamma.length
  background_compatible :
    familyCompatibleB (selectByBits Gamma background) = true
  external_compatible :
    familyCompatibleB (selectByBits Gamma external) = true
  background_fresh : forall i, i < Gamma.length ->
    background.at i = true -> i ∉ tree.vertices

def TreeBackgroundState.checkB {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) : Bool :=
  (occurrenceIndices Gamma.length).all (fun i =>
    Bool.not (state.background.at i) ||
      pathSafe Gamma state.tree.vertices i)

def TreeBackgroundState.selected {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) : Nat :=
  firstUnsafeOccurrence Gamma state.tree.vertices state.background

theorem TreeBackgroundState.selected_spec
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root)
    (hcheck : state.checkB = false) :
    state.selected < Gamma.length ∧
      state.background.at state.selected = true ∧
      pathSafe Gamma state.tree.vertices state.selected = false := by
  exact firstUnsafeOccurrence_spec Gamma state.tree.vertices
    state.background hcheck

def TreeBackgroundState.step {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root)
    (hcheck : state.checkB = false) : TreeBackgroundState Gamma root := by
  let u := state.selected
  have hu := state.selected_spec hcheck
  let pivot := firstConflictIndex Gamma state.tree.vertices u
  have hpivot := firstConflictIndex_mem_and_conflict Gamma
    state.tree.vertices u hu.2.2
  have hpu := incAtDistinct_of_symConflict_true Gamma pivot u hpivot.2
  refine
    { tree := OTree.attach state.tree pivot u hpu
      background := clearResidualAt state.background u
      external := state.external
      valid := ⟨state.valid, hpivot.1⟩
      nodup := ?_
      vertices_bound := ?_
      background_compatible := selectByBits_compatible_of_submask Gamma _
        state.background (clearResidualAt_submask state.background u)
        state.background_compatible
      external_compatible := state.external_compatible
      background_fresh := ?_ }
  · change (u :: state.tree.vertices).Nodup
    exact List.nodup_cons.mpr
      ⟨state.background_fresh u hu.1 hu.2.1, state.nodup⟩
  · intro i hi
    change i ∈ u :: state.tree.vertices at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hu.1
    · exact state.vertices_bound i hi
  · intro i hi hbackground
    have hiOld := clearResidualAt_submask state.background u i hbackground
    have hiNe := clearResidualAt_true_ne_selected state.background u i
      hbackground hu.1
    change i ∉ u :: state.tree.vertices
    intro hmem
    rcases List.mem_cons.mp hmem with hiEq | hmem
    · exact hiNe hiEq
    · exact state.background_fresh i hi hiOld hmem

def TreeBackgroundState.potential {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) : Nat :=
  residualPotential state.background

theorem TreeBackgroundState.step_potential_add_one
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root)
    (hcheck : state.checkB = false) :
    (state.step hcheck).potential + 1 = state.potential := by
  let hu := state.selected_spec hcheck
  exact residualPotential_clearResidualAt_add_one state.background
    state.selected hu.2.1

theorem TreeBackgroundState.step_potential_lt
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root)
    (hcheck : state.checkB = false) :
    (state.step hcheck).potential < state.potential := by
  have h := state.step_potential_add_one hcheck
  omega

theorem TreeBackgroundState.step_vertices_length
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root)
    (hcheck : state.checkB = false) :
    (state.step hcheck).tree.vertices.length =
      state.tree.vertices.length + 1 := by
  rfl

structure TreeBackgroundState.AllGood
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) (good : Nat -> Prop) : Prop where
  tree : forall i, i ∈ state.tree.vertices -> good i
  background : forall i, i < Gamma.length ->
    state.background.at i = true -> good i
  external : forall i, i < Gamma.length ->
    state.external.at i = true -> good i

theorem TreeBackgroundState.AllGood.step
    {Gamma : List (Polymer L)} {root : Nat}
    {state : TreeBackgroundState Gamma root} {good : Nat -> Prop}
    (hgood : state.AllGood good) (hcheck : state.checkB = false) :
    (state.step hcheck).AllGood good := by
  let hu := state.selected_spec hcheck
  refine
    { tree := ?_
      background := ?_
      external := hgood.external }
  · intro i hi
    change i ∈ state.selected :: state.tree.vertices at hi
    rcases List.mem_cons.mp hi with hiEq | hi
    · rw [hiEq]
      exact hgood.background state.selected hu.1 hu.2.1
    · exact hgood.tree i hi
  · intro i hi hmem
    exact hgood.background i hi
      (clearResidualAt_submask state.background state.selected i hmem)

def TreeBackgroundState.totalActivity (w : Q')
    (label : L.Plaquette -> Rep)
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) : Q' :=
  (state.tree.activity (fun i => activity w (polyAt Gamma i) label) *
    residualActivity w label Gamma state.background) *
      residualActivity w label Gamma state.external

theorem TreeBackgroundState.step_totalActivity_eqv
    (w : Q') (label : L.Plaquette -> Rep)
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root)
    (hcheck : state.checkB = false) :
    (state.step hcheck).totalActivity w label ≈
      state.totalActivity w label := by
  let hu := state.selected_spec hcheck
  have hbackground := residualActivity_clearResidualAt_eqv w label Gamma
    state.background state.selected hu.2.1
  unfold TreeBackgroundState.totalActivity
  change (((state.tree.activity
      (fun i => activity w (polyAt Gamma i) label) *
        activity w (polyAt Gamma state.selected) label) *
      residualActivity w label Gamma
        (clearResidualAt state.background state.selected)) *
    residualActivity w label Gamma state.external) ≈ _
  refine Q'.eqv_trans _
    ((state.tree.activity (fun i => activity w (polyAt Gamma i) label) *
      (activity w (polyAt Gamma state.selected) label *
        residualActivity w label Gamma
          (clearResidualAt state.background state.selected))) *
      residualActivity w label Gamma state.external) _ ?_ ?_
  · ring_qeqv
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hbackground))

def TreeBackgroundState.exhaust {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    TreeBackgroundState Gamma root :=
  if hcheck : state.checkB = false then
    TreeBackgroundState.exhaust (state.step hcheck)
  else state
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem TreeBackgroundState.exhaust_checkB_true
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    state.exhaust.checkB = true := by
  rw [TreeBackgroundState.exhaust]
  split
  next hcheck =>
    exact TreeBackgroundState.exhaust_checkB_true (state.step hcheck)
  next hnot =>
    cases h : state.checkB
    · exact False.elim (hnot h)
    · rfl
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem TreeBackgroundState.AllGood.exhaust
    {Gamma : List (Polymer L)} {root : Nat}
    {state : TreeBackgroundState Gamma root} {good : Nat -> Prop}
    (hgood : state.AllGood good) : state.exhaust.AllGood good := by
  rw [TreeBackgroundState.exhaust]
  split
  next hcheck => exact (hgood.step hcheck).exhaust
  next _ => exact hgood
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem TreeBackgroundState.exhaust_totalActivity_eqv
    (w : Q') (label : L.Plaquette -> Rep)
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    state.exhaust.totalActivity w label ≈ state.totalActivity w label := by
  rw [TreeBackgroundState.exhaust]
  split
  next hcheck =>
    exact Q'.eqv_trans _ _ _
      (TreeBackgroundState.exhaust_totalActivity_eqv w label
        (state.step hcheck))
      (state.step_totalActivity_eqv w label hcheck)
  next _ => exact Q'.eqv_refl _
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem TreeBackgroundState.exhaust_background_tree_compatible
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    forall j, j ∈ state.exhaust.tree.vertices -> forall T,
      T ∈ selectByBits Gamma state.exhaust.background ->
        compatibleB (polyAt Gamma j) T = true := by
  intro j hj T hT
  have hTmask : T ∈ maskFamily Gamma
      (bitMask state.exhaust.background) := by
    rw [maskFamily_toMask_eq_selectByBits]
    exact hT
  obtain ⟨i, hi, hbackground, hiT⟩ :=
    mem_maskFamily_occurrence Gamma (bitMask state.exhaust.background) hTmask
  change state.exhaust.background.at i = true at hbackground
  have hiAll := List.all_eq_true.mp state.exhaust_checkB_true i
    (occurrenceIndices_complete hi)
  have hiSafe : pathSafe Gamma state.exhaust.tree.vertices i = true := by
    simpa only [hbackground, Bool.not_true, Bool.false_or] using hiAll
  have hji : j ≠ i := by
    intro hEq
    subst j
    exact state.exhaust.background_fresh i hi hbackground hj
  unfold pathSafe at hiSafe
  have hnotConflict := List.all_eq_true.mp hiSafe j hj
  have hconflict :
      symConflict (incAtDistinct Gamma) j i = false :=
    eq_false_of_not_true hnotConflict
  rw [← hiT]
  exact compatibleB_of_incAtDistinct_symConflict_false Gamma hji hconflict

#print axioms TreeBackgroundState.selected_spec
#print axioms TreeBackgroundState.step
#print axioms TreeBackgroundState.step_potential_add_one
#print axioms TreeBackgroundState.step_potential_lt
#print axioms TreeBackgroundState.step_vertices_length
#print axioms TreeBackgroundState.AllGood.step
#print axioms TreeBackgroundState.step_totalActivity_eqv
#print axioms TreeBackgroundState.exhaust
#print axioms TreeBackgroundState.exhaust_checkB_true
#print axioms TreeBackgroundState.AllGood.exhaust
#print axioms TreeBackgroundState.exhaust_totalActivity_eqv
#print axioms TreeBackgroundState.exhaust_background_tree_compatible

end YMGap.Continuum.XiExceptionalTreeBackgroundNormalization
