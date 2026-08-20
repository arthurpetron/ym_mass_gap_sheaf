/-
# Kernel-checked finite variable-elimination certificates

An external exact-arithmetic program may contract a finite factor graph much
more efficiently than flattening its full assignment table.  This module
defines the small proof contract such a program must satisfy.

For `variables` coordinates with labels in `0, ..., domainSize - 1`, a staged
table at index `remaining` is a function of the `remaining` uneliminated
labels.  A certificate proves:

* the top table agrees with the original weight on every complete word; and
* every lower table entry is the exact rational sum obtained by eliminating
  the next label from the preceding table.

The theorem then identifies the exponentially written assignment sum with
the scalar bottom table.  The producer and its elimination order are not
trusted: Lean checks every displayed stage equation.  Compact factor tables,
symmetry signatures, or algebraic formulas may be used to prove those stage
equations without materializing the full Cartesian product.

This is a theorem about finite computation only.  It makes no statistical,
asymptotic, cutoff-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.FiniteVariableEliminationCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Exact sum over all fixed-length words on a finite label domain. -/
def finiteAssignmentSum
    (domainSize variables : Nat) (value : List Nat → Q') : Q' :=
  listQSum value (allSeqs domainSize variables)

/-- Eliminate the next (head) coordinate by exact rational summation. -/
def eliminateHead
    (domainSize : Nat) (value : List Nat → Q')
    (tail : List Nat) : Q' :=
  listQSum (fun label => value (label :: tail)) (List.range domainSize)

/-- One finite-Fubini step: summing all words of length `remaining + 1` is
the same as summing the head-eliminated table over all remaining tails. -/
theorem finiteAssignmentSum_succ_eqv_eliminateHead
    (domainSize remaining : Nat) (value : List Nat → Q') :
    finiteAssignmentSum domainSize (remaining + 1) value ≈
      finiteAssignmentSum domainSize remaining
        (eliminateHead domainSize value) := by
  unfold finiteAssignmentSum eliminateHead
  refine Q'.eqv_trans _
    (listQSum
      (fun label =>
        listQSum (fun tail => value (label :: tail))
          (allSeqs domainSize remaining))
      (List.range domainSize)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun label =>
          listQSum value
            ((allSeqs domainSize remaining).map
              (fun tail => label :: tail)))
        (List.range domainSize)) _ ?_ ?_
    · exact listQSum_flatMap value
        (fun label =>
          (allSeqs domainSize remaining).map
            (fun tail => label :: tail))
        (List.range domainSize)
    · apply listQSum_congr_on
      intro label _label_mem
      exact Q'.eqv_of_eq
        (listQSum_map value (fun tail => label :: tail)
          (allSeqs domainSize remaining))
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun label tail => value (label :: tail))
        (List.range domainSize)
        (allSeqs domainSize remaining))

private theorem mem_allSeqs_succ_parts
    (domainSize remaining label : Nat) (tail : List Nat)
    (hmem : label :: tail ∈ allSeqs domainSize (remaining + 1)) :
    label ∈ List.range domainSize ∧
      tail ∈ allSeqs domainSize remaining := by
  change label :: tail ∈
    (List.range domainSize).flatMap
      (fun head =>
        (allSeqs domainSize remaining).map
          (fun rest => head :: rest)) at hmem
  rcases List.mem_flatMap.mp hmem with ⟨head, hhead, hmapped⟩
  rcases List.mem_map.mp hmapped with ⟨rest, hrest, heq⟩
  cases heq
  exact ⟨hhead, hrest⟩

/-- A replayable dynamic-programming trace for exact finite variable
elimination.  `table remaining` may be defined by a compact factorization or
a generated literal table; only its values on the appropriate finite word
carrier enter the contract. -/
structure ExactVariableEliminationCertificate
    (domainSize variables : Nat) (value : List Nat → Q') : Type where
  table : Nat → List Nat → Q'
  initial :
    ∀ assignment,
      assignment ∈ allSeqs domainSize variables →
        value assignment ≈ table variables assignment
  step :
    ∀ remaining,
      remaining < variables →
        ∀ tail,
          tail ∈ allSeqs domainSize remaining →
            eliminateHead domainSize (table (remaining + 1)) tail ≈
              table remaining tail

namespace ExactVariableEliminationCertificate

private theorem staged_sum_eqv_bottom
    {domainSize variables : Nat} {value : List Nat → Q'}
    (certificate :
      ExactVariableEliminationCertificate domainSize variables value) :
    ∀ remaining,
      remaining ≤ variables →
        finiteAssignmentSum domainSize remaining
            (certificate.table remaining) ≈
          certificate.table 0 []
  | 0, _ => by
      unfold finiteAssignmentSum allSeqs listQSum
      exact Q'.eqv_of_eq (Q'.add_zero' (certificate.table 0 []))
  | remaining + 1, hremaining => by
      refine Q'.eqv_trans _
        (finiteAssignmentSum domainSize remaining
          (eliminateHead domainSize
            (certificate.table (remaining + 1)))) _
        (finiteAssignmentSum_succ_eqv_eliminateHead
          domainSize remaining (certificate.table (remaining + 1))) ?_
      refine Q'.eqv_trans _
        (finiteAssignmentSum domainSize remaining
          (certificate.table remaining)) _ ?_
        (staged_sum_eqv_bottom certificate remaining
          (Nat.le_trans (Nat.le_succ remaining) hremaining))
      unfold finiteAssignmentSum
      apply listQSum_congr_on
      intro tail htail
      exact certificate.step remaining
        (Nat.lt_of_succ_le hremaining) tail htail

/-- Soundness of a complete elimination trace.  The scalar bottom entry is
the exact sum of the original weight over the full Cartesian word carrier. -/
theorem assignmentSum_eqv_bottom
    {domainSize variables : Nat} {value : List Nat → Q'}
    (certificate :
      ExactVariableEliminationCertificate domainSize variables value) :
    finiteAssignmentSum domainSize variables value ≈
      certificate.table 0 [] := by
  refine Q'.eqv_trans _
    (finiteAssignmentSum domainSize variables
      (certificate.table variables)) _ ?_ ?_
  · unfold finiteAssignmentSum
    apply listQSum_congr_on
    intro assignment hassignment
    exact certificate.initial assignment hassignment
  · exact staged_sum_eqv_bottom certificate variables (Nat.le_refl variables)

end ExactVariableEliminationCertificate

/-! ## Branch-and-bound traces for Cartesian maxima -/

/-- Maximum of a rational value over a finite list, seeded at zero. -/
def finiteListMaxZero {Item : Type}
    (value : Item → Q') : List Item → Q'
  | [] => 0
  | item :: items =>
      Q'.max' (value item) (finiteListMaxZero value items)

/-- Maximum over the full fixed-length word carrier. -/
def finiteAssignmentMaxZero
    (domainSize variables : Nat) (value : List Nat → Q') : Q' :=
  finiteListMaxZero value (allSeqs domainSize variables)

private theorem finiteListMaxZero_le_of_on_mem
    {Item : Type} (value : Item → Q') (bound : Q')
    (bound_nonnegative : (0 : Q') ≤ bound) :
    ∀ items : List Item,
      (∀ item, item ∈ items → value item ≤ bound) →
        finiteListMaxZero value items ≤ bound
  | [], _ => bound_nonnegative
  | item :: items, hbound => by
      unfold finiteListMaxZero
      exact (Q'.max'_le_iff' _ _ bound).mpr
        ⟨hbound item List.mem_cons_self,
          finiteListMaxZero_le_of_on_mem value bound bound_nonnegative
            items
            (fun other hother =>
              hbound other (List.mem_cons_of_mem item hother))⟩

/-- A proof-carrying branch-and-bound trace.  `table remaining assignment`
is an upper bound at a node with `remaining` unprocessed labels.  Every child
must be bounded by its parent; hence the scalar root bounds all complete
assignments.  External search may propose the table but cannot certify an
incorrect pruning step. -/
structure VariableEliminationUpperBoundCertificate
    (domainSize variables : Nat) (value : List Nat → Q') : Type where
  table : Nat → List Nat → Q'
  initial_le :
    ∀ assignment,
      assignment ∈ allSeqs domainSize variables →
        value assignment ≤ table variables assignment
  step_le :
    ∀ remaining,
      remaining < variables →
        ∀ label,
          label ∈ List.range domainSize →
            ∀ tail,
              tail ∈ allSeqs domainSize remaining →
                table (remaining + 1) (label :: tail) ≤
                  table remaining tail
  bottom_nonnegative :
    (0 : Q') ≤ table 0 []

namespace VariableEliminationUpperBoundCertificate

private theorem table_le_bottom
    {domainSize variables : Nat} {value : List Nat → Q'}
    (certificate :
      VariableEliminationUpperBoundCertificate
        domainSize variables value) :
    ∀ remaining assignment,
      remaining ≤ variables →
        assignment ∈ allSeqs domainSize remaining →
          certificate.table remaining assignment ≤
            certificate.table 0 []
  | 0, assignment, _hremaining, hassignment => by
      change assignment ∈ [[]] at hassignment
      have hempty : assignment = [] := List.mem_singleton.mp hassignment
      subst assignment
      exact Q'.le_refl' _
  | remaining + 1, assignment, hremaining, hassignment => by
      cases assignment with
      | nil =>
          change [] ∈
            (List.range domainSize).flatMap
              (fun head =>
                (allSeqs domainSize remaining).map
                  (fun rest => head :: rest)) at hassignment
          rcases List.mem_flatMap.mp hassignment with
            ⟨head, _hhead, hmapped⟩
          rcases List.mem_map.mp hmapped with
            ⟨tail, _htail, heq⟩
          cases heq
      | cons label tail =>
          have hparts := mem_allSeqs_succ_parts
            domainSize remaining label tail hassignment
          exact Q'.le_trans' _ _ _
            (certificate.step_le remaining
              (Nat.lt_of_succ_le hremaining)
              label hparts.1 tail hparts.2)
            (table_le_bottom certificate remaining tail
              (Nat.le_trans (Nat.le_succ remaining) hremaining)
              hparts.2)

/-- Every complete assignment is bounded by the scalar root of the checked
branch-and-bound trace. -/
theorem value_le_bottom
    {domainSize variables : Nat} {value : List Nat → Q'}
    (certificate :
      VariableEliminationUpperBoundCertificate
        domainSize variables value)
    (assignment : List Nat)
    (hassignment : assignment ∈ allSeqs domainSize variables) :
    value assignment ≤ certificate.table 0 [] :=
  Q'.le_trans' _ _ _
    (certificate.initial_le assignment hassignment)
    (table_le_bottom certificate variables assignment
      (Nat.le_refl variables) hassignment)

/-- The scalar root bounds the zero-seeded maximum over the full Cartesian
word carrier. -/
theorem assignmentMax_le_bottom
    {domainSize variables : Nat} {value : List Nat → Q'}
    (certificate :
      VariableEliminationUpperBoundCertificate
        domainSize variables value) :
    finiteAssignmentMaxZero domainSize variables value ≤
      certificate.table 0 [] := by
  unfold finiteAssignmentMaxZero
  exact finiteListMaxZero_le_of_on_mem
    value (certificate.table 0 []) certificate.bottom_nonnegative
    (allSeqs domainSize variables)
    (fun assignment hassignment =>
      certificate.value_le_bottom assignment hassignment)

end VariableEliminationUpperBoundCertificate

end YMGap.Continuum.FiniteVariableEliminationCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FiniteVariableEliminationCertificate.finiteAssignmentSum_succ_eqv_eliminateHead
#print axioms YMGap.Continuum.FiniteVariableEliminationCertificate.ExactVariableEliminationCertificate.assignmentSum_eqv_bottom
#print axioms YMGap.Continuum.FiniteVariableEliminationCertificate.VariableEliminationUpperBoundCertificate.value_le_bottom
#print axioms YMGap.Continuum.FiniteVariableEliminationCertificate.VariableEliminationUpperBoundCertificate.assignmentMax_le_bottom
