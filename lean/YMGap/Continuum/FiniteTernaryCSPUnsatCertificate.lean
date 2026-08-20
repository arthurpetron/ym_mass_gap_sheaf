/-
# Kernel-checked finite ternary CSP refutations

This module supplies a small computer-science proof contract for finite
constraint searches.  A constraint has a finite coordinate scope and an
executable predicate on ternary local words.  An external program may emit a
backtracking refutation tree whose leaves name a locally conflicting
constraint.  Lean rechecks every leaf against all local words and verifies
all three children of every split.

The soundness theorem says that an accepted tree rules out every globally
ternary assignment satisfying all constraints.  The producer, its search
heuristics, and its parallel execution are not trusted.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.FiniteTernaryCSPUnsatCertificate

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Continuum.CayleyPruferInjection

/-- One local constraint on a finite list of ternary coordinates. -/
structure TernaryConstraint where
  scope : List Nat
  accepts : List Nat → Bool

/-- A partial assignment is a list of coordinate/label bindings.  Repeated
coordinates are harmless: a global extension must satisfy every binding. -/
abbrev PartialAssignment := List (Nat × Nat)

/-- Lookup a coordinate in a local scope/word pair. -/
def localWordLookup (coordinate : Nat) : List Nat → List Nat → Option Nat
  | [], _ => none
  | _, [] => none
  | scopeHead :: scopeTail, wordHead :: wordTail =>
      if coordinate = scopeHead then some wordHead
      else localWordLookup coordinate scopeTail wordTail

/-- A local word agrees with every partial binding that lies in its scope. -/
def localWordAgreesPartial
    (scope word : List Nat) (bindings : PartialAssignment) : Bool :=
  bindings.all fun binding =>
    match localWordLookup binding.1 scope word with
    | none => true
    | some label => decide (label = binding.2)

/-- Retain only the path bindings visible to one local constraint.  This is
an executable proof-checker optimization: bindings outside the scope made
`localWordAgreesPartial` return `true` unconditionally, so discarding them
before enumerating local words preserves the conflict semantics while making
replay cost depend on local arity rather than full search depth. -/
def bindingsOnScope
    (scope : List Nat) (bindings : PartialAssignment) : PartialAssignment :=
  bindings.filter fun binding => decide (binding.1 ∈ scope)

/-- No accepted ternary word on this scope extends the partial assignment. -/
def constraintConflictB
    (constraint : TernaryConstraint)
    (bindings : PartialAssignment) : Bool :=
  let localBindings := bindingsOnScope constraint.scope bindings
  (allSeqs 3 constraint.scope.length).all fun word =>
    !(constraint.accepts word &&
      localWordAgreesPartial constraint.scope word localBindings)

/-- A finite refutation tree.  Leaves identify a conflicting constraint;
split nodes cover labels zero, one, and two for one coordinate. -/
inductive TernaryUnsatCertificate (constraintCount : Nat) : Type
  | conflict (index : Fin constraintCount)
  | split (coordinate : Nat)
      (zero one two : TernaryUnsatCertificate constraintCount)
  | forceZero (coordinate : Nat)
      (rejectOne rejectTwo : Fin constraintCount)
      (child : TernaryUnsatCertificate constraintCount)
  | forceOne (coordinate : Nat)
      (rejectZero rejectTwo : Fin constraintCount)
      (child : TernaryUnsatCertificate constraintCount)
  | forceTwo (coordinate : Nat)
      (rejectZero rejectOne : Fin constraintCount)
      (child : TernaryUnsatCertificate constraintCount)

namespace TernaryUnsatCertificate

/-- Executable replay of a refutation tree below a partial assignment. -/
def check (constraints : List TernaryConstraint) :
    PartialAssignment →
      TernaryUnsatCertificate constraints.length → Bool
  | bindings, .conflict index =>
      constraintConflictB (constraints.get index) bindings
  | bindings, .split coordinate zero one two =>
      check constraints ((coordinate, 0) :: bindings) zero &&
        check constraints ((coordinate, 1) :: bindings) one &&
        check constraints ((coordinate, 2) :: bindings) two
  | bindings, .forceZero coordinate rejectOne rejectTwo child =>
      constraintConflictB (constraints.get rejectOne)
          ((coordinate, 1) :: bindings) &&
        constraintConflictB (constraints.get rejectTwo)
          ((coordinate, 2) :: bindings) &&
        check constraints ((coordinate, 0) :: bindings) child
  | bindings, .forceOne coordinate rejectZero rejectTwo child =>
      constraintConflictB (constraints.get rejectZero)
          ((coordinate, 0) :: bindings) &&
        constraintConflictB (constraints.get rejectTwo)
          ((coordinate, 2) :: bindings) &&
        check constraints ((coordinate, 1) :: bindings) child
  | bindings, .forceTwo coordinate rejectZero rejectOne child =>
      constraintConflictB (constraints.get rejectZero)
          ((coordinate, 0) :: bindings) &&
        constraintConflictB (constraints.get rejectOne)
          ((coordinate, 1) :: bindings) &&
        check constraints ((coordinate, 2) :: bindings) child

def AssignmentBounded (assignment : Nat → Nat) : Prop :=
  ∀ coordinate, assignment coordinate < 3

def Extends
    (assignment : Nat → Nat) (bindings : PartialAssignment) : Prop :=
  ∀ binding, binding ∈ bindings →
    assignment binding.1 = binding.2

def SatisfiesConstraint
    (assignment : Nat → Nat) (constraint : TernaryConstraint) : Prop :=
  constraint.accepts (constraint.scope.map assignment) = true

def Satisfies
    (constraints : List TernaryConstraint) (assignment : Nat → Nat) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    SatisfiesConstraint assignment constraint

private theorem localWordLookup_map
    (assignment : Nat → Nat) (coordinate : Nat) : ∀ scope,
    localWordLookup coordinate scope (scope.map assignment) =
      if coordinate ∈ scope then some (assignment coordinate) else none
  | [] => by simp [localWordLookup]
  | head :: tail => by
      by_cases heq : coordinate = head
      · subst head
        simp [localWordLookup]
      · simp [localWordLookup, heq,
          localWordLookup_map assignment coordinate tail]

private theorem localWordAgreesPartial_map
    (assignment : Nat → Nat) (bindings : PartialAssignment)
    (hextends : Extends assignment bindings) (scope : List Nat) :
    localWordAgreesPartial scope (scope.map assignment) bindings = true := by
  unfold localWordAgreesPartial
  apply List.all_eq_true.mpr
  intro binding hbinding
  rw [localWordLookup_map]
  by_cases hscope : binding.1 ∈ scope
  · simp only [hscope, if_true]
    have hagree := hextends binding hbinding
    simp [hagree]
  · simp [hscope]

private theorem map_assignment_mem_allSeqs
    (assignment : Nat → Nat) (hbounded : AssignmentBounded assignment)
    (scope : List Nat) :
    scope.map assignment ∈ allSeqs 3 scope.length := by
  apply mem_allSeqs 3 scope.length (scope.map assignment)
  · simp
  · intro label hlabel
    rcases List.mem_map.mp hlabel with ⟨coordinate, _hcoordinate, rfl⟩
    exact hbounded coordinate

private theorem extends_cons_of_value
    (assignment : Nat → Nat) (bindings : PartialAssignment)
    (hextends : Extends assignment bindings)
    (coordinate label : Nat)
    (hvalue : assignment coordinate = label) :
    Extends assignment ((coordinate, label) :: bindings) := by
  intro binding hbinding
  rcases List.mem_cons.mp hbinding with hhead | htail
  · cases hhead
    exact hvalue
  · exact hextends binding htail

private theorem conflict_false_of_solution
    (constraints : List TernaryConstraint)
    (index : Fin constraints.length) (bindings : PartialAssignment)
    (assignment : Nat → Nat)
    (hconflict : constraintConflictB (constraints.get index) bindings = true)
    (hbounded : AssignmentBounded assignment)
    (hsatisfies : Satisfies constraints assignment)
    (hextends : Extends assignment bindings) : False := by
  let constraint := constraints.get index
  let localBindings := bindingsOnScope constraint.scope bindings
  have hconstraintMem : constraint ∈ constraints := by
    exact List.get_mem constraints index
  have haccepts :
      constraint.accepts (constraint.scope.map assignment) = true :=
    hsatisfies constraint hconstraintMem
  have hextendsLocal : Extends assignment localBindings := by
    intro binding hbinding
    apply hextends binding
    exact (List.mem_filter.mp hbinding).1
  have hagrees :
      localWordAgreesPartial constraint.scope
        (constraint.scope.map assignment) localBindings = true :=
    localWordAgreesPartial_map assignment localBindings
      hextendsLocal constraint.scope
  have hword : constraint.scope.map assignment ∈
      allSeqs 3 constraint.scope.length :=
    map_assignment_mem_allSeqs assignment hbounded constraint.scope
  have hrejected :
      !(constraint.accepts (constraint.scope.map assignment) &&
        localWordAgreesPartial constraint.scope
          (constraint.scope.map assignment) localBindings) = true := by
    simpa [constraint, localBindings, constraintConflictB] using
      (List.all_eq_true.mp hconflict
        (constraint.scope.map assignment) hword)
  simp [haccepts, hagrees] at hrejected

/-- Soundness below an arbitrary partial assignment. -/
theorem check_false_of_solution
    (constraints : List TernaryConstraint) :
    ∀ (certificate : TernaryUnsatCertificate constraints.length)
      (bindings : PartialAssignment) (assignment : Nat → Nat),
      check constraints bindings certificate = true →
      AssignmentBounded assignment →
      Satisfies constraints assignment →
      Extends assignment bindings → False
  | .conflict index, bindings, assignment,
      hcheck, hbounded, hsatisfies, hextends => by
      exact conflict_false_of_solution constraints index bindings assignment
        hcheck hbounded hsatisfies hextends
  | .split coordinate zero one two, bindings, assignment,
      hcheck, hbounded, hsatisfies, hextends => by
      simp only [check, Bool.and_eq_true] at hcheck
      have hvalue := hbounded coordinate
      have hcases : assignment coordinate = 0 ∨
          assignment coordinate = 1 ∨ assignment coordinate = 2 := by
        omega
      rcases hcases with hlabel | hlabel | hlabel
      · exact check_false_of_solution constraints zero
          ((coordinate, 0) :: bindings) assignment hcheck.1.1
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 0 hlabel)
      · exact check_false_of_solution constraints one
          ((coordinate, 1) :: bindings) assignment hcheck.1.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 1 hlabel)
      · exact check_false_of_solution constraints two
          ((coordinate, 2) :: bindings) assignment hcheck.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 2 hlabel)
  | .forceZero coordinate rejectOne rejectTwo child,
      bindings, assignment, hcheck, hbounded, hsatisfies, hextends => by
      simp only [check, Bool.and_eq_true] at hcheck
      have hvalue := hbounded coordinate
      have hcases : assignment coordinate = 0 ∨
          assignment coordinate = 1 ∨ assignment coordinate = 2 := by omega
      rcases hcases with hlabel | hlabel | hlabel
      · exact check_false_of_solution constraints child
          ((coordinate, 0) :: bindings) assignment hcheck.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 0 hlabel)
      · exact conflict_false_of_solution constraints rejectOne
          ((coordinate, 1) :: bindings) assignment hcheck.1.1
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 1 hlabel)
      · exact conflict_false_of_solution constraints rejectTwo
          ((coordinate, 2) :: bindings) assignment hcheck.1.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 2 hlabel)
  | .forceOne coordinate rejectZero rejectTwo child,
      bindings, assignment, hcheck, hbounded, hsatisfies, hextends => by
      simp only [check, Bool.and_eq_true] at hcheck
      have hvalue := hbounded coordinate
      have hcases : assignment coordinate = 0 ∨
          assignment coordinate = 1 ∨ assignment coordinate = 2 := by omega
      rcases hcases with hlabel | hlabel | hlabel
      · exact conflict_false_of_solution constraints rejectZero
          ((coordinate, 0) :: bindings) assignment hcheck.1.1
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 0 hlabel)
      · exact check_false_of_solution constraints child
          ((coordinate, 1) :: bindings) assignment hcheck.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 1 hlabel)
      · exact conflict_false_of_solution constraints rejectTwo
          ((coordinate, 2) :: bindings) assignment hcheck.1.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 2 hlabel)
  | .forceTwo coordinate rejectZero rejectOne child,
      bindings, assignment, hcheck, hbounded, hsatisfies, hextends => by
      simp only [check, Bool.and_eq_true] at hcheck
      have hvalue := hbounded coordinate
      have hcases : assignment coordinate = 0 ∨
          assignment coordinate = 1 ∨ assignment coordinate = 2 := by omega
      rcases hcases with hlabel | hlabel | hlabel
      · exact conflict_false_of_solution constraints rejectZero
          ((coordinate, 0) :: bindings) assignment hcheck.1.1
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 0 hlabel)
      · exact conflict_false_of_solution constraints rejectOne
          ((coordinate, 1) :: bindings) assignment hcheck.1.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 1 hlabel)
      · exact check_false_of_solution constraints child
          ((coordinate, 2) :: bindings) assignment hcheck.2
          hbounded hsatisfies
          (extends_cons_of_value assignment bindings hextends
            coordinate 2 hlabel)

/-- An accepted root certificate proves that the finite ternary CSP has no
globally bounded satisfying assignment. -/
theorem no_solution_of_check
    (constraints : List TernaryConstraint)
    (certificate : TernaryUnsatCertificate constraints.length)
    (hcheck : check constraints [] certificate = true) :
    ¬ ∃ assignment : Nat → Nat,
      AssignmentBounded assignment ∧ Satisfies constraints assignment := by
  rintro ⟨assignment, hbounded, hsatisfies⟩
  exact check_false_of_solution constraints certificate [] assignment
    hcheck hbounded hsatisfies (by
      intro binding hbinding
      exact False.elim (List.not_mem_nil hbinding))

end TernaryUnsatCertificate

/-! ## Closed regression certificate -/

def regressionZero : TernaryConstraint where
  scope := [0]
  accepts := fun word => decide (word = [0])

def regressionOne : TernaryConstraint where
  scope := [0]
  accepts := fun word => decide (word = [1])

def regressionConstraints : List TernaryConstraint :=
  [regressionZero, regressionOne]

def regressionCertificate :
    TernaryUnsatCertificate regressionConstraints.length :=
  .split 0 (.conflict ⟨1, by decide⟩)
    (.conflict ⟨0, by decide⟩) (.conflict ⟨0, by decide⟩)

theorem regressionCertificate_checked :
    regressionCertificate.check regressionConstraints [] = true := by
  decide

theorem regressionConstraints_unsatisfiable :
    ¬ ∃ assignment : Nat → Nat,
      TernaryUnsatCertificate.AssignmentBounded assignment ∧
      TernaryUnsatCertificate.Satisfies regressionConstraints assignment := by
  exact TernaryUnsatCertificate.no_solution_of_check
    regressionConstraints regressionCertificate
    regressionCertificate_checked

end YMGap.Continuum.FiniteTernaryCSPUnsatCertificate

#print axioms
  YMGap.Continuum.FiniteTernaryCSPUnsatCertificate.TernaryUnsatCertificate.no_solution_of_check
#print axioms
  YMGap.Continuum.FiniteTernaryCSPUnsatCertificate.regressionConstraints_unsatisfiable
