/-
# Exact edge-occurrence multiplicities in the canonical link fusion chain

The production resolver replaces the plaquette representations incident on a
lattice link by a canonical left-associated trivalent chain.  To continue an
individual strand through that chain, one needs more than the fact that each
identifier occurs somewhere: physical identifiers must be terminals, genuine
auxiliary identifiers must have two endpoints, and the vacuum terminator must
carry no strand.

This module proves the edge-level version of that statement for the geometric
four-dimensional valence range `degree <= 6`.  It flattens the three edge
positions of every canonical vertex into one occurrence word.  Every physical
identifier below `degree` has count one.  Every genuine internal auxiliary
identifier has count two.  The only used coordinate not belonging to either
class is the terminator `degree`; the production Boolean guard forces its
label to zero.

Constructive contract: exact reduction of the seven possible finite valences,
natural arithmetic, and Boolean-list elimination only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.ResolvedTrivalentNetworkPorts
import YMGap.Continuum.Z4CanonicalLinkUsedCoordinates

namespace YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. The literal occurrence word -/

/-- All three edge positions of all vertices in the canonical link chain. -/
def canonicalLinkEdgeOccurrences (degree : Nat) : List Nat :=
  (canonicalLinkVertices degree).flatMap vertexEdgeIds

@[simp] theorem canonicalLinkEdgeOccurrences_zero :
    canonicalLinkEdgeOccurrences 0 = [] := rfl

@[simp] theorem canonicalLinkEdgeOccurrences_one :
    canonicalLinkEdgeOccurrences 1 = [0, 1, 1] := rfl

@[simp] theorem canonicalLinkEdgeOccurrences_two :
    canonicalLinkEdgeOccurrences 2 = [0, 1, 2] := rfl

@[simp] theorem canonicalLinkEdgeOccurrences_three :
    canonicalLinkEdgeOccurrences 3 = [0, 1, 2] := rfl

@[simp] theorem canonicalLinkEdgeOccurrences_four :
    canonicalLinkEdgeOccurrences 4 = [0, 1, 5, 5, 2, 3] := rfl

@[simp] theorem canonicalLinkEdgeOccurrences_five :
    canonicalLinkEdgeOccurrences 5 = [0, 1, 6, 6, 2, 7, 7, 3, 4] := rfl

@[simp] theorem canonicalLinkEdgeOccurrences_six :
    canonicalLinkEdgeOccurrences 6 =
      [0, 1, 7, 7, 2, 8, 8, 3, 9, 9, 4, 5] := rfl

/-! ## 2. Physical terminals and internal auxiliary edges -/

/-- The used auxiliary coordinates other than the open-link vacuum
terminator. -/
def canonicalInternalFusionEdges (degree : Nat) : List Nat :=
  (canonicalUsedAuxiliaryCoordinates degree).filter
    (fun edge => decide (edge ≠ degree))

/-- Every physical input identifier occurs exactly once in the trivalent
edge word. -/
theorem canonicalLinkEdgeOccurrences_count_physical
    {degree edge : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge < degree) :
    (canonicalLinkEdgeOccurrences degree).count edge = 1 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · have he : edge = 0 := by omega
    subst edge
    decide
  · have he : edge = 0 ∨ edge = 1 := by omega
    rcases he with rfl | rfl <;> decide
  · have he : edge = 0 ∨ edge = 1 ∨ edge = 2 := by omega
    rcases he with rfl | rfl | rfl <;> decide
  · have he : edge = 0 ∨ edge = 1 ∨ edge = 2 ∨ edge = 3 := by
      omega
    rcases he with rfl | rfl | rfl | rfl <;> decide
  · have he :
        edge = 0 ∨ edge = 1 ∨ edge = 2 ∨ edge = 3 ∨ edge = 4 := by
      omega
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
  · have he : edge = 0 ∨ edge = 1 ∨ edge = 2 ∨ edge = 3 ∨
        edge = 4 ∨ edge = 5 := by
      omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every genuine internal fusion identifier occurs exactly twice. -/
theorem canonicalLinkEdgeOccurrences_count_internal
    {degree edge : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalInternalFusionEdges degree) :
    (canonicalLinkEdgeOccurrences degree).count edge = 2 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    subst edge
    decide
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl <;> decide
  · simp [canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl | rfl <;> decide

/-- A used canonical coordinate is physical, the vacuum terminator, or a
genuine internal fusion identifier. -/
theorem canonicalUsedCoordinate_classify
    {degree edge : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalUsedCoordinates degree) :
    edge < degree ∨ edge = degree ∨
      edge ∈ canonicalInternalFusionEdges degree := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [canonicalUsedCoordinates, canonicalInternalFusionEdges,
      canonicalUsedAuxiliaryCoordinates] at hedge ⊢ <;>
    omega

/-! ## 3. The terminator has no positive strand -/

/-- If the terminator is among the coordinates read by the resolver, the
accepted production guard forces its label to zero. -/
theorem canonicalLinkConditionalAllowedB_terminator_zero
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hused : degree ∈ canonicalUsedAuxiliaryCoordinates degree)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    canonicalLinkLabelling degree external auxiliary degree = 0 := by
  have hparts :
      verticesAdmissibleB
          (canonicalLinkVertices degree)
          (canonicalLinkLabelling degree external auxiliary) = true ∧
        (canonicalUsedAuxiliaryCoordinates degree).all
          (canonicalAuxiliaryEdgeAllowedB degree
            (canonicalLinkLabelling degree external auxiliary)) = true := by
    simpa only [canonicalLinkConditionalAllowedB,
      canonicalLinkVertices, canonicalLinkLabelling,
      Bool.and_eq_true] using hallowed
  have hedge := List.all_eq_true.mp hparts.2 degree hused
  unfold canonicalAuxiliaryEdgeAllowedB at hedge
  rw [if_pos rfl] at hedge
  simpa only [decide_eq_true_eq] using hedge

/-- Consequently no typed port can lie on a used terminator edge. -/
theorem no_resolved_port_on_used_terminator
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (hused : degree ∈ canonicalUsedAuxiliaryCoordinates degree)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    occurrence.edgeId ≠ degree := by
  intro hedge
  have hzero := canonicalLinkConditionalAllowedB_terminator_zero
    hused hallowed
  have hslot := occurrence.slot_lt_edgeLabel
  rw [hedge, hzero] at hslot
  omega

#print axioms canonicalLinkEdgeOccurrences
#print axioms canonicalLinkEdgeOccurrences_zero
#print axioms canonicalLinkEdgeOccurrences_one
#print axioms canonicalLinkEdgeOccurrences_two
#print axioms canonicalLinkEdgeOccurrences_three
#print axioms canonicalLinkEdgeOccurrences_four
#print axioms canonicalLinkEdgeOccurrences_five
#print axioms canonicalLinkEdgeOccurrences_six
#print axioms canonicalLinkEdgeOccurrences_count_physical
#print axioms canonicalInternalFusionEdges
#print axioms canonicalLinkEdgeOccurrences_count_internal
#print axioms canonicalUsedCoordinate_classify
#print axioms canonicalLinkConditionalAllowedB_terminator_zero
#print axioms no_resolved_port_on_used_terminator

end YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
