/-
# A concrete boundary shared by a cube labelling and its inward mate

On each of the twelve vertical cube-edge faces, put the absolute difference
of the two incident lower-cube labels. Every lower-link triple is admissible
both before and after the inward mate. Each of the eight nontrivial fixed
links sees three distances between three natural-number labels and is also
admissible. No common-parity assumption is needed for this boundary.

This module supplies the boundary, its cutoff bound and its SU(2) triangle
identities. Production link multiplicities and physical kernel weights are
connected in the next module. No transition floor or gap is asserted here.
-/

import YMGap.Continuum.BF4PhysicalHalfCubeSupport
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateLabels

namespace YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary

set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

def spinDistance (a b : Nat) : Nat := (a - b) + (b - a)

theorem spinDistance_le {K a b : Nat} (ha : a ≤ K) (hb : b ≤ K) :
    spinDistance a b ≤ K := by unfold spinDistance; omega

theorem spinDistance_fusion (a b : Nat) : fusionOK a b (spinDistance a b) = true := by
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_def, Nat.min_def]
  unfold spinDistance
  split <;> refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The same distance channel survives the literal inward mate, even at zero. -/
theorem spinDistance_mate_fusion (a b : Nat) :
    fusionOK (evenInwardMateLabel a) (evenInwardMateLabel b) (spinDistance a b) = true := by
  rw [fusionOK_eq_true_iff]
  unfold spinDistance evenInwardMateLabel
  split <;> split <;> simp only [Nat.max_def, Nat.min_def] <;>
    split <;> refine ⟨?_, ?_, ?_⟩ <;> omega

theorem spinDistance_triangle_fusion (a b c : Nat) :
    fusionOK (spinDistance a b) (spinDistance a c) (spinDistance b c) = true := by
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_def, Nat.min_def]
  unfold spinDistance
  split <;> refine ⟨?_, ?_, ?_⟩ <;> omega

def cubeDifferenceBoundaryIds : List Nat :=
  [2, 4, 5, 11, 13, 20, 23, 29, 40, 41, 49, 59]

def cubeDifferenceBoundary (state : EdgeLabelling) : EdgeLabelling := fun face =>
  match face with
  | 2 => spinDistance (state 0) (state 1)
  | 4 => spinDistance (state 0) (state 3)
  | 5 => spinDistance (state 1) (state 3)
  | 11 => spinDistance (state 1) (state 9)
  | 13 => spinDistance (state 3) (state 9)
  | 20 => spinDistance (state 0) (state 19)
  | 23 => spinDistance (state 3) (state 19)
  | 29 => spinDistance (state 9) (state 19)
  | 40 => spinDistance (state 0) (state 39)
  | 41 => spinDistance (state 1) (state 39)
  | 49 => spinDistance (state 9) (state 39)
  | 59 => spinDistance (state 19) (state 39)
  | _ => 0

theorem cubeDifferenceBoundary_zero_off (state : EdgeLabelling) {face : Nat}
    (hoff : face ∉ cubeDifferenceBoundaryIds) : cubeDifferenceBoundary state face = 0 := by
  unfold cubeDifferenceBoundary
  split
  all_goals first | rfl | exact False.elim (hoff (by decide))

theorem cubeDifferenceBoundary_bounded (K : Nat) (state : EdgeLabelling)
    (hbound : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K) :
    ∀ face, cubeDifferenceBoundary state face ≤ K := by
  intro face
  unfold cubeDifferenceBoundary
  split
  all_goals first
    | exact Nat.zero_le K
    | exact spinDistance_le (hbound _ (by decide)) (hbound _ (by decide))

theorem cubeDifferenceBoundaryIds_subset_fixed {face : Nat}
    (hface : face ∈ cubeDifferenceBoundaryIds) : face ∈ centralFixedFaceIds 0 := by
  simp only [cubeDifferenceBoundaryIds, List.mem_cons, List.not_mem_nil, or_false] at hface
  rcases hface with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem cubeDifferenceBoundary_mem (K : Nat) (state : EdgeLabelling)
    (hbound : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K) :
    cubeDifferenceBoundary state ∈ centralBoundaryChannels K 0 := by
  apply boundedEdgeLabellings_complete
  · intro face _
    exact Nat.lt_succ_of_le (cubeDifferenceBoundary_bounded K state hbound face)
  · intro face hoff
    apply cubeDifferenceBoundary_zero_off
    exact fun h => hoff (cubeDifferenceBoundaryIds_subset_fixed h)

/-- Each row is lower face, lower face, vertical boundary face. -/
def cubeDifferenceEdges : List (Nat × Nat × Nat) :=
  [(0, 1, 2), (0, 3, 4), (0, 19, 20), (0, 39, 40),
   (1, 3, 5), (1, 9, 11), (1, 39, 41), (3, 9, 13),
   (3, 19, 23), (9, 19, 29), (9, 39, 49), (19, 39, 59)]

theorem cubeDifferenceEdge_faces (edge : Nat × Nat × Nat)
    (he : edge ∈ cubeDifferenceEdges) :
    edge.1 ∈ centralLowerCubeFaceIds ∧ edge.2.1 ∈ centralLowerCubeFaceIds ∧
      edge.2.2 ∈ centralFixedFaceIds 0 := by
  simp only [cubeDifferenceEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem cubeDifferenceBoundary_on_edge (state : EdgeLabelling) (edge : Nat × Nat × Nat)
    (he : edge ∈ cubeDifferenceEdges) :
    cubeDifferenceBoundary state edge.2.2 = spinDistance (state edge.1) (state edge.2.1) := by
  simp only [cubeDifferenceEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def cubeDifferenceCorners : List (Nat × Nat × Nat) :=
  [(2, 4, 5), (2, 40, 41), (4, 20, 23), (5, 11, 13),
   (11, 41, 49), (13, 23, 29), (20, 40, 59), (29, 49, 59)]

theorem cubeDifferenceBoundary_corner_fusion (state : EdgeLabelling)
    (corner : Nat × Nat × Nat) (hc : corner ∈ cubeDifferenceCorners) :
    fusionOK (cubeDifferenceBoundary state corner.1)
      (cubeDifferenceBoundary state corner.2.1)
      (cubeDifferenceBoundary state corner.2.2) = true := by
  simp only [cubeDifferenceCorners, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact spinDistance_triangle_fusion _ _ _

end YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary

#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.spinDistance_fusion
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.spinDistance_le
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.spinDistance_mate_fusion
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.spinDistance_triangle_fusion
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.cubeDifferenceBoundary_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.cubeDifferenceBoundary_zero_off
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.cubeDifferenceBoundaryIds_subset_fixed
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.cubeDifferenceBoundary_mem
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.cubeDifferenceEdge_faces
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.cubeDifferenceBoundary_on_edge
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary.cubeDifferenceBoundary_corner_fusion
