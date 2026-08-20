/-
# Proof-by-construction ternary scoped-factor elimination

`FiniteScopedFactorTableCertificate` can validate externally proposed sparse
tables.  This module proves a complementary computer-science result: when the
next bucket table is defined by exhaustive ternary evaluation itself, its
correctness is symbolic and need not be rechecked entry by entry.

The result is a verified width-sensitive dynamic program.  External Rust,
C, or Python may predict its final answer, but Lean's kernel evaluates the
same finite recurrence and the theorem below connects that value to the full
Cartesian partition sum.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup

namespace YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.FiniteScopedFactorTernaryRadixLookup
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Every coordinate read by every factor belongs to the live carrier. -/
def FactorsScopedBy
    (coordinates : List Nat) (factors : List ScopedQFactor) : Prop :=
  ∀ factor, factor ∈ factors →
    ∀ id, id ∈ factor.scope → id ∈ coordinates

def factorsScopedByCheck
    (coordinates : List Nat) (factors : List ScopedQFactor) : Bool :=
  factors.all fun factor =>
    factor.scope.all fun id => decide (id ∈ coordinates)

theorem factorsScopedBy_of_check
    {coordinates : List Nat} {factors : List ScopedQFactor}
    (hcheck : factorsScopedByCheck coordinates factors = true) :
    FactorsScopedBy coordinates factors := by
  intro factor hfactor id hid
  exact of_decide_eq_true
    (List.all_eq_true.mp
      (List.all_eq_true.mp hcheck factor hfactor) id hid)

private theorem wordToEdgeLabelling_map_eq_on
    (assignment : Nat → Nat) : ∀ scope : List Nat,
    scope.Nodup → ∀ id, id ∈ scope →
      wordToEdgeLabelling scope (scope.map assignment) id = assignment id
  | [], _, id, hid => False.elim (List.not_mem_nil hid)
  | head :: tail, hnodup, id, hid => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hid with rfl | htail
      · simp [wordToEdgeLabelling, setEdgeLabel]
      · have hne : id ≠ head := by
          intro heq
          subst id
          exact hparts.1 htail
        simp only [List.map_cons, wordToEdgeLabelling]
        rw [show setEdgeLabel
            (wordToEdgeLabelling tail (tail.map assignment))
              head (assignment head) id =
            wordToEdgeLabelling tail (tail.map assignment) id by
              simp [setEdgeLabel, hne]]
        exact wordToEdgeLabelling_map_eq_on assignment tail
          hparts.2 id htail

/-- A ternary table produced by `computedBucketTable` is correct by lookup
semantics, without a Boolean scan of its full table. -/
theorem computedBucketFactor_three_correct
    (coordinate : Nat) (scope : List Nat)
    (bucket : List ScopedQFactor)
    (hnodup : scope.Nodup)
    (hcover : ∀ factor, factor ∈ bucket →
      ∀ id, id ∈ factor.scope → id ≠ coordinate → id ∈ scope)
    (labelling : EdgeLabelling)
    (hbounded : ∀ id, id ∈ scope → labelling id < 3) :
    (computedBucketFactor 2 coordinate scope bucket).value labelling ≈
      eliminatedBucketValue 2 coordinate bucket labelling := by
  have hlookup := scopedTableValue_map_allSeqs_three
    scope labelling
    (fun labels => eliminatedBucketValue 2 coordinate bucket
      (wordToEdgeLabelling scope labels))
    (0 : Q') hbounded
  have hlocal := eliminatedBucketValue_local_eq
    2 coordinate bucket scope hcover
    (wordToEdgeLabelling scope (scope.map labelling))
    labelling
    (fun id hid =>
      wordToEdgeLabelling_map_eq_on labelling scope hnodup id hid)
  unfold computedBucketFactor computedBucketTable
    scopedTableFactor scopedTableValue
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hlookup)
    (Q'.eqv_of_eq hlocal)

def computedTernaryResultScope
    (coordinates : List Nat) (coordinate : Nat)
    (factors : List ScopedQFactor) : List Nat :=
  computedBucketScope coordinates coordinate
    (factorBucket coordinate factors)

def computedTernaryResultFactor
    (coordinates : List Nat) (coordinate : Nat)
    (factors : List ScopedQFactor) : ScopedQFactor :=
  computedBucketFactor 2 coordinate
    (computedTernaryResultScope coordinates coordinate factors)
    (factorBucket coordinate factors)

def computedTernaryAfterFactors
    (coordinates : List Nat) (coordinate : Nat)
    (factors : List ScopedQFactor) : List ScopedQFactor :=
  computedTernaryResultFactor coordinates coordinate factors ::
    factorOutside coordinate factors

private theorem computedTernaryResultScope_nodup
    {coordinates : List Nat} {coordinate : Nat}
    {factors : List ScopedQFactor}
    (hnodup : coordinates.Nodup) :
    (computedTernaryResultScope coordinates coordinate factors).Nodup := by
  unfold computedTernaryResultScope computedBucketScope
  exact List.filter_sublist.nodup hnodup

private theorem computedTernaryResultScope_coordinate_not_mem
    (coordinates : List Nat) (coordinate : Nat)
    (factors : List ScopedQFactor) :
    coordinate ∉ computedTernaryResultScope
      coordinates coordinate factors := by
  intro hmem
  have hparts := List.mem_filter.mp hmem
  have hand := (Bool.and_eq_true _ _).mp hparts.2
  exact (of_decide_eq_true hand.1) rfl

private theorem computedTernaryResultScope_covers
    {coordinates : List Nat} {coordinate : Nat}
    {factors : List ScopedQFactor}
    (hscoped : FactorsScopedBy coordinates factors) :
    ∀ factor, factor ∈ factorBucket coordinate factors →
      ∀ id, id ∈ factor.scope → id ≠ coordinate →
        id ∈ computedTernaryResultScope
          coordinates coordinate factors := by
  intro factor hfactor id hid hne
  have horiginal : factor ∈ factors := (List.mem_filter.mp hfactor).1
  have hcoordinate : id ∈ coordinates :=
    hscoped factor horiginal id hid
  have hany : (factorBucket coordinate factors).any
      (fun item => decide (id ∈ item.scope)) = true :=
    List.any_eq_true.mpr ⟨factor, hfactor, by
      exact decide_eq_true hid⟩
  unfold computedTernaryResultScope computedBucketScope
  apply List.mem_filter.mpr
  exact ⟨hcoordinate, (Bool.and_eq_true _ _).mpr
    ⟨decide_eq_true hne, hany⟩⟩

private theorem computedTernaryResultScope_mem_remaining
    {coordinate : Nat} {remaining : List Nat}
    {factors : List ScopedQFactor} :
    ∀ id, id ∈ computedTernaryResultScope
        (coordinate :: remaining) coordinate factors →
      id ∈ remaining := by
  intro id hid
  have hparts := List.mem_filter.mp hid
  have hand := (Bool.and_eq_true _ _).mp hparts.2
  have hne : id ≠ coordinate := of_decide_eq_true hand.1
  rcases List.mem_cons.mp hparts.1 with heq | hremaining
  · exact False.elim (hne heq)
  · exact hremaining

/-- A computed ternary step inhabits the existing checked-step interface by
theorems, not by exhaustive reduction of `table_checked`. -/
def computedTernaryEliminationStep
    (coordinate : Nat) (remaining : List Nat)
    (factors : List ScopedQFactor)
    (hnodup : (coordinate :: remaining).Nodup)
    (hscoped : FactorsScopedBy (coordinate :: remaining) factors) :
    CheckedScopedEliminationStep 2 coordinate remaining factors where
  bucketResult :=
    { result := computedTernaryResultFactor
        (coordinate :: remaining) coordinate factors
      scope_nodup := computedTernaryResultScope_nodup hnodup
      coordinate_not_scope :=
        computedTernaryResultScope_coordinate_not_mem
          (coordinate :: remaining) coordinate factors
      scope_cover_checked := by
        apply List.all_eq_true.mpr
        intro factor hfactor
        apply List.all_eq_true.mpr
        intro id hid
        apply decide_eq_true
        by_cases heq : id = coordinate
        · exact Or.inl heq
        · exact Or.inr
            (computedTernaryResultScope_covers hscoped
              factor hfactor id hid heq)
      table_checked := by
        unfold boundedLocalEquationCheck
        apply List.all_eq_true.mpr
        intro labelling hlabelling
        apply decide_eq_true
        apply computedBucketFactor_three_correct
        · exact computedTernaryResultScope_nodup hnodup
        · exact computedTernaryResultScope_covers hscoped
        · exact (boundedEdgeLabellings_sound 2
            (computedTernaryResultScope
              (coordinate :: remaining) coordinate factors)
            labelling hlabelling).1 }
  result_scope_remaining_checked := by
    apply List.all_eq_true.mpr
    intro id hid
    exact decide_eq_true
      (computedTernaryResultScope_mem_remaining id hid)

private theorem computedTernaryAfterFactors_eq_step
    (coordinate : Nat) (remaining : List Nat)
    (factors : List ScopedQFactor)
    (hnodup : (coordinate :: remaining).Nodup)
    (hscoped : FactorsScopedBy (coordinate :: remaining) factors) :
    computedTernaryAfterFactors (coordinate :: remaining) coordinate factors =
      (computedTernaryEliminationStep coordinate remaining factors
        hnodup hscoped).afterFactors :=
  rfl

theorem partitionSum_eqv_computedTernaryAfter
    (coordinate : Nat) (remaining : List Nat)
    (factors : List ScopedQFactor)
    (hnodup : (coordinate :: remaining).Nodup)
    (hscoped : FactorsScopedBy (coordinate :: remaining) factors) :
    scopedFactorPartitionSum 2 (coordinate :: remaining) factors ≈
      scopedFactorPartitionSum 2 remaining
        (computedTernaryAfterFactors
          (coordinate :: remaining) coordinate factors) := by
  rw [computedTernaryAfterFactors_eq_step
    coordinate remaining factors hnodup hscoped]
  exact (computedTernaryEliminationStep coordinate remaining factors
    hnodup hscoped).partitionSum_eqv_after

theorem computedTernaryAfterFactors_scoped
    (coordinate : Nat) (remaining : List Nat)
    (factors : List ScopedQFactor)
    (hscoped : FactorsScopedBy (coordinate :: remaining) factors) :
    FactorsScopedBy remaining
      (computedTernaryAfterFactors
        (coordinate :: remaining) coordinate factors) := by
  intro factor hfactor id hid
  rcases List.mem_cons.mp hfactor with hresult | houtside
  · subst factor
    exact computedTernaryResultScope_mem_remaining id hid
  · have hparts := List.mem_filter.mp houtside
    have horiginal := hparts.1
    have hcoordinateNot : coordinate ∉ factor.scope :=
      of_decide_eq_true hparts.2
    have hcurrent := hscoped factor horiginal id hid
    rcases List.mem_cons.mp hcurrent with heq | hremaining
    · subst id
      exact False.elim (hcoordinateNot hid)
    · exact hremaining

/-- Execute exact ternary variable elimination in the listed order. -/
def computedTernaryEliminate :
    List Nat → List ScopedQFactor → List ScopedQFactor
  | [], factors => factors
  | coordinate :: remaining, factors =>
      computedTernaryEliminate remaining
        (computedTernaryAfterFactors
          (coordinate :: remaining) coordinate factors)

/-- Scalar read after all listed coordinates have been eliminated. -/
def computedTernaryBottomValue
    (coordinates : List Nat) (factors : List ScopedQFactor) : Q' :=
  scopedFactorProduct
    (computedTernaryEliminate coordinates factors)
    zeroEdgeLabelling

/-- Soundness of the proof-by-construction dynamic program. -/
theorem scopedFactorPartitionSum_eqv_computedTernaryBottom :
    ∀ (coordinates : List Nat) (factors : List ScopedQFactor),
    coordinates.Nodup → FactorsScopedBy coordinates factors →
      scopedFactorPartitionSum 2 coordinates factors ≈
        computedTernaryBottomValue coordinates factors
  | [], factors, _, _ => by
      unfold scopedFactorPartitionSum boundedEdgeLabellings
        computedTernaryBottomValue computedTernaryEliminate
      exact Q'.eqv_of_eq
        (Q'.add_zero' (scopedFactorProduct factors zeroEdgeLabelling))
  | coordinate :: remaining, factors, hnodup, hscoped => by
      exact Q'.eqv_trans _ _ _
        (partitionSum_eqv_computedTernaryAfter
          coordinate remaining factors hnodup hscoped)
        (scopedFactorPartitionSum_eqv_computedTernaryBottom
          remaining
          (computedTernaryAfterFactors
            (coordinate :: remaining) coordinate factors)
          (List.nodup_cons.mp hnodup).2
          (computedTernaryAfterFactors_scoped
            coordinate remaining factors hscoped))

end YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination

#print axioms
  YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination.computedBucketFactor_three_correct
#print axioms
  YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination.partitionSum_eqv_computedTernaryAfter
#print axioms
  YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination.scopedFactorPartitionSum_eqv_computedTernaryBottom
