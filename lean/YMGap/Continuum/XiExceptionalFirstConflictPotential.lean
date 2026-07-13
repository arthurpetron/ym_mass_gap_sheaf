/-
# Exact termination potential for repeated first-conflict splicing

A first-conflict detour is only an iterable construction once its consumed
residual occurrence is removed from the pending work.  This file packages a
walk together with its occurrence residual, performs that Boolean-selected
step entirely in `Type`, and proves an exact potential law: every step adds
two walk vertices and removes exactly one true residual bit.  The latter is a
strict natural-number decrease and therefore supplies recursion fuel without
choice or a `Prop`-valued witness.
-/

import YMGap.Continuum.XiExceptionalEntryFirstConflictSplice

namespace YMGap.Continuum.XiExceptionalFirstConflictPotential

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFirstConflictSplice
open YMGap.Continuum.XiExceptionalEntryFirstConflictSplice

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Residual clearing and its exact cardinality law -/

def clearResidualAt : {n : Nat} → OccBitVec n → Nat → OccBitVec n
  | 0, .nil, _ => .nil
  | _ + 1, .cons _ tail, 0 => .cons false tail
  | _ + 1, .cons head tail, i + 1 =>
      .cons head (clearResidualAt tail i)

def residualPotential : {n : Nat} → OccBitVec n → Nat
  | 0, .nil => 0
  | _ + 1, .cons head tail =>
      (if head then 1 else 0) + residualPotential tail

theorem clearResidualAt_at_self_false :
    ∀ {n : Nat} (bits : OccBitVec n) (i : Nat), i < n →
      (clearResidualAt bits i).at i = false
  | 0, .nil, _, hi => by omega
  | _ + 1, .cons _ _, 0, _ => rfl
  | _ + 1, .cons _ tail, i + 1, hi =>
      clearResidualAt_at_self_false tail i (by omega)

theorem residualPotential_le_length :
    ∀ {n : Nat} (bits : OccBitVec n), residualPotential bits ≤ n
  | 0, .nil => Nat.zero_le 0
  | n + 1, .cons head tail => by
      have ih := residualPotential_le_length tail
      cases head <;>
        simp only [residualPotential, Bool.false_eq_true, ↓reduceIte,
          Nat.zero_add] <;>
        omega

theorem residualPotential_clearResidualAt_add_one :
    ∀ {n : Nat} (bits : OccBitVec n) (i : Nat), bits.at i = true →
      residualPotential (clearResidualAt bits i) + 1 =
        residualPotential bits
  | 0, .nil, _, h => by cases h
  | _ + 1, .cons head tail, 0, h => by
      change head = true at h
      subst head
      simp only [clearResidualAt, residualPotential, ↓reduceIte,
        Bool.false_eq_true, Nat.zero_add]
      omega
  | _ + 1, .cons head tail, i + 1, h => by
      have ih := residualPotential_clearResidualAt_add_one tail i h
      cases head <;>
        simp only [clearResidualAt, residualPotential, Bool.false_eq_true,
          ↓reduceIte, Nat.zero_add] <;>
        omega

theorem residualPotential_clearResidualAt_lt
    {n : Nat} (bits : OccBitVec n) (i : Nat)
    (hi : bits.at i = true) :
    residualPotential (clearResidualAt bits i) < residualPotential bits := by
  have h := residualPotential_clearResidualAt_add_one bits i hi
  omega

/-! ## A data-valued splice state -/

structure SpliceState (Gamma : List (Polymer L)) (start finish : Nat) : Type where
  walk : CWalk (incAtDistinct Gamma) start finish
  residual : OccBitVec Gamma.length

def SpliceState.unsafeCheckB {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) : Bool :=
  (occurrenceIndices Gamma.length).all (fun i =>
    Bool.not (state.residual.at i) ||
      pathSafe Gamma state.walk.vertices i)

def SpliceState.selectedUnsafe {Gamma : List (Polymer L)}
    {start finish : Nat} (state : SpliceState Gamma start finish) : Nat :=
  firstUnsafeOccurrence Gamma state.walk.vertices state.residual

theorem SpliceState.selectedUnsafe_spec
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    state.selectedUnsafe < Gamma.length ∧
      state.residual.at state.selectedUnsafe = true ∧
      pathSafe Gamma state.walk.vertices state.selectedUnsafe = false := by
  exact firstUnsafeOccurrence_spec Gamma state.walk.vertices state.residual
    hunsafe

def SpliceState.step {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    SpliceState Gamma start finish :=
  let u := state.selectedUnsafe
  let hu := state.selectedUnsafe_spec hunsafe
  { walk :=
      YMGap.Continuum.XiExceptionalFirstConflictSplice.CWalk.firstConflictEndpointDetour
        Gamma state.walk u hu.2.2
    residual := clearResidualAt state.residual u }

def SpliceState.potential {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) : Nat :=
  residualPotential state.residual

/-! ## Exact one-step laws -/

theorem SpliceState.step_potential_add_one
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    (state.step hunsafe).potential + 1 = state.potential := by
  let hu := state.selectedUnsafe_spec hunsafe
  exact residualPotential_clearResidualAt_add_one state.residual
    state.selectedUnsafe hu.2.1

theorem SpliceState.step_potential_lt
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    (state.step hunsafe).potential < state.potential := by
  have h := state.step_potential_add_one hunsafe
  omega

theorem SpliceState.potential_le_ambient_length
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    state.potential ≤ Gamma.length :=
  residualPotential_le_length state.residual

theorem SpliceState.step_selected_cleared
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    (state.step hunsafe).residual.at state.selectedUnsafe = false := by
  let hu := state.selectedUnsafe_spec hunsafe
  exact clearResidualAt_at_self_false state.residual state.selectedUnsafe hu.1

theorem SpliceState.step_walk_length
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    (state.step hunsafe).walk.vertices.length =
      state.walk.vertices.length + 2 := by
  let hu := state.selectedUnsafe_spec hunsafe
  exact
    YMGap.Continuum.XiExceptionalFirstConflictSplice.CWalk.firstConflictEndpointDetour_length
      Gamma state.walk state.selectedUnsafe hu.2.2

theorem SpliceState.step_size_potential_conserved
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    (state.step hunsafe).walk.vertices.length +
        2 * (state.step hunsafe).potential =
      state.walk.vertices.length + 2 * state.potential := by
  have hlength := state.step_walk_length hunsafe
  have hpotential := state.step_potential_add_one hunsafe
  omega

#print axioms residualPotential_clearResidualAt_add_one
#print axioms residualPotential_clearResidualAt_lt
#print axioms residualPotential_le_length
#print axioms SpliceState.selectedUnsafe_spec
#print axioms SpliceState.step
#print axioms SpliceState.step_potential_add_one
#print axioms SpliceState.step_potential_lt
#print axioms SpliceState.potential_le_ambient_length
#print axioms SpliceState.step_selected_cleared
#print axioms SpliceState.step_walk_length
#print axioms SpliceState.step_size_potential_conserved

end YMGap.Continuum.XiExceptionalFirstConflictPotential
