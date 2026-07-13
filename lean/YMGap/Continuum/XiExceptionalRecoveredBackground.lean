/-
# Recovered-cut exterior compatibility for exceptional Xi paths

The frozen exceptional carrier checkpoint requires a background family which
is compatible with every recovered path vertex.  This file proves the graph
mechanism that supplies it.  Under internal compatibility of the two input
masks, every occupied occurrence outside the forward disagreement component
is compatible with every occurrence inside that component.  Otherwise a
same-side conflict contradicts internal compatibility, or an opposite-side
conflict is a disagreement edge and closure pulls the exterior occurrence
into the component.

This is the pointwise cut theorem.  The next step lifts it through
`maskFamily` and accounts for the activities discarded with the non-path
part of a branched component.
-/

import YMGap.Continuum.XiExceptionalMaskCarrier

namespace YMGap.Continuum.XiExceptionalRecoveredBackground

open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi

/-! ## 1. Every reached occurrence is an exclusive occupation -/

theorem disagreementBits_source_different
    (li ri lj rj conflict : Bool)
    (h : disagreementBits li ri lj rj conflict = true) :
    differentBits li ri = true := by
  cases li <;> cases ri <;> cases lj <;> cases rj <;> cases conflict <;>
    simp_all [disagreementBits, differentBits, leftOnly, rightOnly]

theorem disagreementEdge_source_different
    (N : Nat) (inc : Nat → Nat → Bool) (left right : Nat → Bool)
    {i j : Nat} (h : disagreementEdge N inc left right i j = true) :
    differentBits (left i) (right i) = true := by
  exact disagreementBits_source_different _ _ _ _ _
    ((Bool.and_eq_true _ _).mp h).2

theorem walk_vertices_different_of_seed
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool) :
    ∀ {i seed : Nat}
      (p : CWalk (disagreementEdge N inc left right) i seed),
      forwardSeed N left right bad seed = true →
      ∀ k, k ∈ p.vertices → differentBits (left k) (right k) = true
  | _, _, .single _, hseed, k, hk => by
      rw [List.mem_singleton.mp hk]
      have hs := forwardSeed_parts N left right bad hseed
      simp [differentBits, hs.2.1, hs.2.2.1]
  | _, _, .cons h rest, hseed, k, hk => by
      rcases List.mem_cons.mp hk with hhead | htail
      · rw [hhead]
        exact disagreementEdge_source_different N inc left right h
      · exact walk_vertices_different_of_seed N inc left right bad rest
          hseed k htail

theorem component_different_of_reach
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    {i : Nat} (hreach : forwardComponent N inc left right bad i = true) :
    differentBits (left i) (right i) = true := by
  let ep := reverseOccurrencePathOfReach N inc left right bad i hreach
  exact walk_vertices_different_of_seed N inc left right bad ep.walk
    ep.seed_true i (CWalk.start_mem_vertices ep.walk)

theorem component_index_lt_of_reach
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    {i : Nat} (hreach : forwardComponent N inc left right bad i = true) :
    i < N := by
  let ep := reverseOccurrencePathOfReach N inc left right bad i hreach
  have hseedN := (forwardSeed_parts N left right bad ep.seed_true).1
  exact walk_vertices_lt_of_seed N inc left right ep.walk hseedN i
    (CWalk.start_mem_vertices ep.walk)

/-! ## 2. The closed component is compatible with its occupied exterior -/

/-- Scalar case split behind the exterior theorem.  An exclusive first cell
and an occupied second cell, with same-side conflicts forbidden, form a
disagreement edge whenever `conflict=true`. -/
theorem disagreementBits_of_exclusive_occupied_conflict
    (li ri lj rj conflict : Bool)
    (hi : differentBits li ri = true)
    (hjOcc : lj || rj = true)
    (hleft : li = true → lj = true → conflict = false)
    (hright : ri = true → rj = true → conflict = false)
    (hc : conflict = true) :
    disagreementBits li ri lj rj conflict = true := by
  cases li <;> cases ri <;> cases lj <;> cases rj <;> cases conflict <;>
    simp_all [disagreementBits, differentBits, leftOnly, rightOnly]

/-- **Exterior compatibility of a recovered component.** -/
theorem component_compatible_with_occupied_exterior
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    {i j : Nat}
    (hi : forwardComponent N inc left right bad i = true)
    (hj : forwardComponent N inc left right bad j = false)
    (hjN : j < N) (hjOcc : left j || right j = true) :
    symConflict inc i j = false := by
  cases hc : symConflict inc i j with
  | false => rfl
  | true =>
      have hiN := component_index_lt_of_reach N inc left right bad hi
      have hdifferent := component_different_of_reach N inc left right bad hi
      have hbits : disagreementBits (left i) (right i)
          (left j) (right j) (symConflict inc i j) = true :=
        disagreementBits_of_exclusive_occupied_conflict _ _ _ _ _
          hdifferent hjOcc (hleft i j) (hright i j) hc
      have hedge : disagreementEdge N inc left right i j = true := by
        unfold disagreementEdge
        rw [decide_eq_true hiN, decide_eq_true hjN]
        exact hbits
      have hjReach := component_closed_right N inc left right bad hi hedge
      rw [hj] at hjReach
      exact absurd hjReach (by decide)

/-! ## 3. Outside masks and pointwise path-background compatibility -/

def outsideMask (cut mask : Nat → Bool) (i : Nat) : Bool :=
  mask i && !(cut i)

theorem outsideMask_parts (cut mask : Nat → Bool) {i : Nat}
    (h : outsideMask cut mask i = true) :
    mask i = true ∧ cut i = false := by
  have hp := (Bool.and_eq_true _ _).mp h
  exact ⟨hp.1, eq_false_of_not_true hp.2⟩

theorem component_compatible_with_outside_left
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    {i j : Nat}
    (hi : forwardComponent N inc left right bad i = true)
    (hjN : j < N)
    (hj : outsideMask (forwardComponent N inc left right bad) left j = true) :
    symConflict inc i j = false := by
  have hp := outsideMask_parts _ _ hj
  apply component_compatible_with_occupied_exterior N inc left right bad
    hleft hright hi hp.2 hjN
  simp [hp.1]

theorem component_compatible_with_outside_right
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    (hleft : ∀ i j, left i = true → left j = true →
      symConflict inc i j = false)
    (hright : ∀ i j, right i = true → right j = true →
      symConflict inc i j = false)
    {i j : Nat}
    (hi : forwardComponent N inc left right bad i = true)
    (hjN : j < N)
    (hj : outsideMask (forwardComponent N inc left right bad) right j = true) :
    symConflict inc i j = false := by
  have hp := outsideMask_parts _ _ hj
  apply component_compatible_with_occupied_exterior N inc left right bad
    hleft hright hi hp.2 hjN
  cases hl : left j <;> simp [hl, hp.1]

/-- Every vertex of a disagreement walk starting in the component remains in
that component. -/
theorem walk_vertices_in_component
    (N : Nat) (inc : Nat → Nat → Bool) (left right bad : Nat → Bool)
    {i seed : Nat}
    (p : CWalk (disagreementEdge N inc left right) i seed)
    (hi : forwardComponent N inc left right bad i = true) :
    ∀ k, k ∈ p.vertices →
      forwardComponent N inc left right bad k = true :=
  CWalk.all_vertices_of_start
    (fun k => forwardComponent N inc left right bad k = true)
    (fun _ _ hedge hreach =>
      component_closed_right N inc left right bad hreach hedge)
    p hi

/-! ## 4. Diagonal normalization fence and corrected occurrence conflict -/

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-- Correct occurrence conflict: two *distinct* ambient occurrences carry
incompatible polymers.  The diagonal is deliberately false because a family
does not compare an occurrence with itself. -/
def incAtDistinct (Γ : List (Polymer L)) (i j : Nat) : Bool :=
  decide (i ≠ j) && !(compatibleB (polyAt Γ i) (polyAt Γ j))

theorem disagreementEdge_incAtDistinct
    (Γ : List (Polymer L)) (left right : Nat → Bool)
    {i j : Nat}
    (h : disagreementEdge Γ.length (incAtDistinct Γ) left right i j = true) :
    (!(compatibleB (polyAt Γ i) (polyAt Γ j))) = true := by
  have hbits := ((Bool.and_eq_true _ _).mp h).2
  have hconflict := ((Bool.and_eq_true _ _).mp hbits).2
  unfold symConflict at hconflict
  rcases (Bool.or_eq_true _ _).mp hconflict with hij | hji
  · exact ((Bool.and_eq_true _ _).mp hij).2
  · have hji' := ((Bool.and_eq_true _ _).mp hji).2
    rw [compatibleB_symm (polyAt Γ j) (polyAt Γ i)] at hji'
    exact hji'

theorem incAtDistinct_diag_false (Γ : List (Polymer L)) (i : Nat) :
    incAtDistinct Γ i i = false := by
  simp [incAtDistinct]

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def tp : TL.Plaquette := (0, 0)
private def tΓ : List (Polymer TL) := [[tp]]
private def tleft (i : Nat) : Bool := decide (i = 0)

/-- **Normalization fence.**  The uncorrected `incAt` makes the same-side
guard used by reverse recovery impossible even for one occupied one-plaquette
polymer: occurrence `0` conflicts with itself.  Therefore the diagonal-free
`incAtDistinct` normalization above is required for a non-vacuous mask
specialization. -/
theorem incAt_sameSide_guard_uninhabited_on_singleton :
    ¬ (∀ i j, tleft i = true → tleft j = true →
      symConflict (incAt tΓ) i j = false) := by
  intro h
  have h00 := h 0 0 (by rfl) (by rfl)
  unfold symConflict incAt polyAt tΓ tp compatibleB at h00
  exact absurd h00 (by decide)

#print axioms disagreementBits_source_different
#print axioms disagreementEdge_source_different
#print axioms walk_vertices_different_of_seed
#print axioms component_different_of_reach
#print axioms component_index_lt_of_reach
#print axioms disagreementBits_of_exclusive_occupied_conflict
#print axioms component_compatible_with_occupied_exterior
#print axioms outsideMask_parts
#print axioms component_compatible_with_outside_left
#print axioms component_compatible_with_outside_right
#print axioms walk_vertices_in_component
#print axioms disagreementEdge_incAtDistinct
#print axioms incAtDistinct_diag_false
#print axioms incAt_sameSide_guard_uninhabited_on_singleton

end YMGap.Continuum.XiExceptionalRecoveredBackground
