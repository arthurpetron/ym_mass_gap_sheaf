/-
# Monotone rank for canonical nonbacktracking link strands

The path argument is independent of strand slots and dependent port
addresses.  Three natural-number positions on a linear path suffice: if both
successive pairs are adjacent and the third position does not return to the
first, then the two steps have one common direction.  The remaining distance
to that end of a bounded path therefore decreases strictly.

The second section proves that the arithmetic coordinate assigned to a
canonical internal identifier is faithful.  These are the two abstract facts
needed to turn the already-proved local strand dynamics into a bounded
terminal extractor.

Constructive contract: natural-number arithmetic and explicit finite-list
membership only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkInternalEdgeEndpoints

namespace YMGap.Continuum.CanonicalLinkStrandMonotonePath

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalEdgeEndpoints
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. The abstract nonbacktracking path theorem -/

/-- Two natural-number positions are adjacent in the linear path. -/
def NatPathAdjacent (left right : Nat) : Prop :=
  left + 1 = right ∨ right + 1 = left

/-- A pair of adjacent, nonbacktracking steps has a single direction. -/
theorem natPathAdjacent_nonbacktracking_direction
    {previous current next : Nat}
    (hprevious : NatPathAdjacent previous current)
    (hnext : NatPathAdjacent current next)
    (hnonbacktracking : next ≠ previous) :
    (previous + 1 = current ∧ current + 1 = next) ∨
      (current + 1 = previous ∧ next + 1 = current) := by
  unfold NatPathAdjacent at hprevious hnext
  rcases hprevious with hprevious | hprevious
  · rcases hnext with hnext | hnext
    · exact Or.inl ⟨hprevious, hnext⟩
    · have hreturn : next = previous :=
        Nat.add_right_cancel (hnext.trans hprevious.symm)
      exact False.elim (hnonbacktracking hreturn)
  · rcases hnext with hnext | hnext
    · have hreturn : next = previous := hnext.symm.trans hprevious
      exact False.elim (hnonbacktracking hreturn)
    · exact Or.inr ⟨hprevious, hnext⟩

/-- Remaining distance to the end selected by the ordered pair
`previous,current`: right distance when the pair increases, left distance
when it decreases. -/
def natPathRank (bound previous current : Nat) : Nat :=
  if previous < current then bound - current else current

/-- A bounded nonbacktracking path step strictly decreases its selected-end
rank.  This is the well-founded measure for terminal extraction. -/
theorem natPathRank_strictly_decreases
    {bound previous current next : Nat}
    (hprevious : NatPathAdjacent previous current)
    (hnext : NatPathAdjacent current next)
    (hnonbacktracking : next ≠ previous)
    (hnextBound : next < bound) :
    natPathRank bound current next <
      natPathRank bound previous current := by
  have hdirection := natPathAdjacent_nonbacktracking_direction
    hprevious hnext hnonbacktracking
  rcases hdirection with hdirection | hdirection
  · have hpreviousLt : previous < current :=
      Nat.lt_of_succ_le (Nat.le_of_eq hdirection.1)
    have hcurrentLt : current < next :=
      Nat.lt_of_succ_le (Nat.le_of_eq hdirection.2)
    have hcurrentLeBound : current ≤ bound :=
      Nat.le_trans (Nat.le_of_lt hcurrentLt) (Nat.le_of_lt hnextBound)
    have hnextLeBound : next ≤ bound := Nat.le_of_lt hnextBound
    have hrankEq : bound - next + 1 = bound - current := by
      have hadded : (bound - next + 1) + current =
          (bound - current) + current := by
        calc
          (bound - next + 1) + current =
              (bound - next) + (current + 1) := by
                simp only [Nat.add_comm, Nat.add_left_comm]
          _ = (bound - next) + next := by rw [hdirection.2]
          _ = bound := Nat.sub_add_cancel hnextLeBound
          _ = (bound - current) + current :=
            (Nat.sub_add_cancel hcurrentLeBound).symm
      exact Nat.add_right_cancel hadded
    simp only [natPathRank, if_pos hpreviousLt, if_pos hcurrentLt]
    exact Nat.lt_of_succ_le (Nat.le_of_eq hrankEq)
  · have hcurrentLtPrevious : current < previous :=
      Nat.lt_of_succ_le (Nat.le_of_eq hdirection.1)
    have hnextLtCurrent : next < current :=
      Nat.lt_of_succ_le (Nat.le_of_eq hdirection.2)
    have hpreviousNotLt : ¬ previous < current :=
      Nat.not_lt_of_ge (Nat.le_of_lt hcurrentLtPrevious)
    have hcurrentNotLt : ¬ current < next :=
      Nat.not_lt_of_ge (Nat.le_of_lt hnextLtCurrent)
    simp only [natPathRank, if_neg hpreviousNotLt,
      if_neg hcurrentNotLt]
    exact hnextLtCurrent

/-- Two distinct positions that both form the endpoints of two consecutive
unit intervals determine the same left endpoint. -/
theorem consecutiveEndpointPair_leftIndex_unique
    {first second left₁ left₂ : Nat}
    (hdistinct : first ≠ second)
    (hfirst₁ : first = left₁ ∨ first = left₁ + 1)
    (hsecond₁ : second = left₁ ∨ second = left₁ + 1)
    (hfirst₂ : first = left₂ ∨ first = left₂ + 1)
    (hsecond₂ : second = left₂ ∨ second = left₂ + 1) :
    left₁ = left₂ := by
  rcases hfirst₁ with hfirst₁ | hfirst₁ <;>
    rcases hsecond₁ with hsecond₁ | hsecond₁ <;>
      rcases hfirst₂ with hfirst₂ | hfirst₂ <;>
        rcases hsecond₂ with hsecond₂ | hsecond₂ <;> omega

/-! ## 2. Faithfulness of the canonical internal-edge coordinate -/

/-- An internal identifier is reconstructed exactly from its left-endpoint
coordinate. -/
theorem canonicalInternalEdge_reconstruct
    {degree edge : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalInternalFusionEdges degree) :
    degree + 1 + canonicalInternalEdgeLeftIndex degree edge = edge := by
  have hfiltered := List.mem_filter.mp hedge
  have hauxiliary : edge ∈ canonicalUsedAuxiliaryCoordinates degree :=
    hfiltered.1
  have hnotTerminator : edge ≠ degree :=
    of_decide_eq_true hfiltered.2
  obtain ⟨offset, hedgeEq, _⟩ :=
    canonicalUsedAuxiliary_coordinate_shape hdegree hauxiliary
  unfold canonicalInternalEdgeLeftIndex
  omega

/-- The canonical internal-edge left-endpoint coordinate is injective. -/
theorem canonicalInternalEdgeLeftIndex_injective
    {degree edge₁ edge₂ : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge₁ : edge₁ ∈ canonicalInternalFusionEdges degree)
    (hedge₂ : edge₂ ∈ canonicalInternalFusionEdges degree)
    (hleft : canonicalInternalEdgeLeftIndex degree edge₁ =
      canonicalInternalEdgeLeftIndex degree edge₂) :
    edge₁ = edge₂ := by
  have hreconstruct₁ := canonicalInternalEdge_reconstruct hdegree hedge₁
  have hreconstruct₂ := canonicalInternalEdge_reconstruct hdegree hedge₂
  omega

#print axioms NatPathAdjacent
#print axioms natPathAdjacent_nonbacktracking_direction
#print axioms natPathRank
#print axioms natPathRank_strictly_decreases
#print axioms consecutiveEndpointPair_leftIndex_unique
#print axioms canonicalInternalEdge_reconstruct
#print axioms canonicalInternalEdgeLeftIndex_injective

end YMGap.Continuum.CanonicalLinkStrandMonotonePath
