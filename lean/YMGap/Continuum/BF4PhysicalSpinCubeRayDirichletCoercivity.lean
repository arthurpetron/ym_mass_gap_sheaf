/-
# Uniform Dirichlet coercivity on the explicit central spin-cube ray

The cutoff-uniform spoke capacity is already a coefficient-independent flow
bound.  This module contracts that bound into the corresponding analytic
statement.  The stationary-product pairwise variance of the growing excited
spin-cube ray is routed through the vacuum star.  Literal weighted edge
occurrences retain repeated spoke use, exact regrouping turns them into one
directed-edge load, and the uniform capacity compares that load pointwise
with the genuine normalized physical kernel.

At the strong-coupling anchor this yields, at every cutoff and with one fixed
positive rational `delta`,

  delta * pairwiseVariance(ray) <= physicalDirichlet(full vacuum sector).

This is a genuine uniform coercivity theorem on the explicit ray subsector.
It does not control pairwise variance involving the remaining physical
vacuum-sector states, and hence proves no full-sector transfer gap,
thermodynamic or continuum limit, continuum QFT, or Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity

namespace YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. The literal stationary pairwise form on the growing ray -/

/-- Stationary-product pairwise variance restricted to the `K` excited
central spin cubes `1, ..., K`. -/
def centralLowerExcitedSpinCubeRayPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedPairwiseVariance
    (centralLowerExcitedSpinCubeIndices w hw K)
    (centralPhysicalFiniteWeight w hw K 0)
    coefficient

/-- The same ray pairwise form enumerated by source spin offsets.  This is the
order used by the literal two-spoke flow. -/
def centralLowerExcitedSpinCubeOffsetPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      centralLowerExcitedSpinCubePairWeight w hw K pair *
        ((coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.1) +
            -coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.2)) *
          (coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.1) +
            -coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.2))))
    (centralLowerExcitedSpinCubeEndpointPairs K)

/-- Mapping the offset range into physical carrier indices does not change
the stationary pairwise form. -/
theorem centralLowerExcitedSpinCubeRayPairwiseVariance_eqv_offset
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeRayPairwiseVariance w hw K coefficient ≈
      centralLowerExcitedSpinCubeOffsetPairwiseVariance
        w hw K coefficient := by
  let index := centralLowerExcitedSpinCubeIndex w hw K
  let entry : Nat × Nat → Q' := fun pair =>
    centralLowerExcitedSpinCubePairWeight w hw K pair *
      ((coefficient (index pair.1) + -coefficient (index pair.2)) *
        (coefficient (index pair.1) + -coefficient (index pair.2)))
  unfold centralLowerExcitedSpinCubeRayPairwiseVariance
    finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    centralLowerExcitedSpinCubeIndices
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun left => listQSum (fun right => entry (left, right))
        (List.range K))
      (List.range K)) _ ?_ ?_
  · apply listQSum_congr
    intro left
    rw [listQSum_map]
    unfold finiteStationaryProductJoint entry index
    exact Q'.eqv_refl _
  · unfold centralLowerExcitedSpinCubeOffsetPairwiseVariance
      centralLowerExcitedSpinCubeEndpointPairs cartesian entry index
    let value : Nat × Nat → Q' := fun pair =>
      centralLowerExcitedSpinCubePairWeight w hw K pair *
        ((coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.1) +
            -coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.2)) *
          (coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.1) +
            -coefficient
              (centralLowerExcitedSpinCubeIndex w hw K pair.2)))
    have hflat := listQSum_flatMap value
      (fun left => (List.range K).map (fun right => (left, right)))
      (List.range K)
    have hrows : listQSum
        (fun left => listQSum value
          ((List.range K).map (fun right => (left, right))))
        (List.range K) ≈
      listQSum
        (fun left => listQSum (fun right => value (left, right))
          (List.range K))
        (List.range K) := by
      apply listQSum_congr
      intro left
      rw [listQSum_map]
      exact Q'.eqv_refl _
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _ hflat hrows)

/-! ## 2. The two-spoke occurrence budget exactly pays ray variance -/

/-- Before equal directed spokes are grouped, this is the literal weighted
edge-square budget of the ray flow. -/
def centralLowerExcitedSpinCubeRayRawOccurrenceEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceEnergy
    (centralLowerExcitedSpinCubeRayFlowOccurrences w hw K)
    coefficient (fun _ _ => 1)

private theorem pairWeight_nonnegative
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (pair : Nat × Nat)
    (hpair : pair ∈ centralLowerExcitedSpinCubeEndpointPairs K) :
    (0 : Q') ≤ centralLowerExcitedSpinCubePairWeight
      w (Q'.le_of_lt hw) K pair := by
  have hparts := (mem_cartesian_iff
    (List.range K) (List.range K) pair).mp hpair
  unfold centralLowerExcitedSpinCubePairWeight
  apply Q'.mul_nonneg
  · exact Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (centralLowerSpinCubeIndex_mem_vacuumSector hw (by
          have hoffset := List.mem_range.mp hparts.1
          omega)))
  · exact Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (centralLowerSpinCubeIndex_mem_vacuumSector hw (by
          have hoffset := List.mem_range.mp hparts.2
          omega)))

/-- One stationary endpoint-pair square is bounded by the literal weighted
cost of its two vacuum spokes. -/
theorem centralLowerExcitedSpinCubePairwiseTerm_le_occurrenceEnergy
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (coefficient : Nat → Q') (pair : Nat × Nat)
    (hpair : pair ∈ centralLowerExcitedSpinCubeEndpointPairs K) :
    centralLowerExcitedSpinCubePairWeight
        w (Q'.le_of_lt hw) K pair *
      ((coefficient
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K pair.1) +
          -coefficient
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K pair.2)) *
        (coefficient
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K pair.1) +
          -coefficient
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K pair.2))) ≤
      finiteWeightedOccurrenceEnergy
        (centralLowerExcitedSpinCubePairSpokeOccurrences
          w (Q'.le_of_lt hw) K pair)
        coefficient (fun _ _ => 1) := by
  have hparts := (mem_cartesian_iff
    (List.range K) (List.range K) pair).mp hpair
  have hleft : pair.1 + 1 ≤ K := by
    have := List.mem_range.mp hparts.1
    omega
  have hright : pair.2 + 1 ≤ K := by
    have := List.mem_range.mp hparts.2
    omega
  let path := centralLowerSpinCubeStarPath
    hw (pair.1 + 1) (pair.2 + 1) hleft hright
  let leftIndex := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K pair.1
  let rightIndex := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K pair.2
  let leftSquare := (coefficient leftIndex + -coefficient 0) *
    (coefficient leftIndex + -coefficient 0)
  let rightSquare := (coefficient 0 + -coefficient rightIndex) *
    (coefficient 0 + -coefficient rightIndex)
  have hendpoint :=
    centralLowerSpinCube_endpoint_sq_le_two_spoke_square_sum
      hw coefficient (pair.1 + 1) (pair.2 + 1) hleft hright
  have hedges :=
    PositiveKernelChainIn.edgeSquareSum_eqv_edgeDifferences
      coefficient path
  rw [centralLowerSpinCubeStarPath_directedEdges
    hw (pair.1 + 1) (pair.2 + 1) hleft hright] at hedges
  have hspokeSquares : leftSquare + rightSquare ≈
      listQSum (fun value => value * value)
        (PositiveKernelChainIn.edgeDifferences coefficient path) := by
    refine Q'.eqv_trans _ (leftSquare + (rightSquare + 0)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left leftSquare _ _
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' rightSquare)))
    · change
        (coefficient
              (centralLowerSpinCubeIndex
                w (Q'.le_of_lt hw) K (pair.1 + 1)) +
            -coefficient 0) *
            (coefficient
              (centralLowerSpinCubeIndex
                w (Q'.le_of_lt hw) K (pair.1 + 1)) +
            -coefficient 0) +
          ((coefficient 0 +
                -coefficient
                  (centralLowerSpinCubeIndex
                    w (Q'.le_of_lt hw) K (pair.2 + 1))) *
              (coefficient 0 +
                -coefficient
                  (centralLowerSpinCubeIndex
                    w (Q'.le_of_lt hw) K (pair.2 + 1))) + 0) ≈ _
      exact hedges
  have henergy : finiteWeightedOccurrenceEnergy
        (centralLowerExcitedSpinCubePairSpokeOccurrences
          w (Q'.le_of_lt hw) K pair)
        coefficient (fun _ _ => 1) ≈
      centralLowerExcitedSpinCubePairWeight
          w (Q'.le_of_lt hw) K pair *
        (2 * listQSum (fun value => value * value)
          (PositiveKernelChainIn.edgeDifferences coefficient path)) := by
    refine Q'.eqv_trans _
      (centralLowerExcitedSpinCubePairWeight
          w (Q'.le_of_lt hw) K pair *
        (2 * (leftSquare + rightSquare))) _ ?_ ?_
    · unfold finiteWeightedOccurrenceEnergy
        centralLowerExcitedSpinCubePairSpokeOccurrences
      change
        (centralLowerExcitedSpinCubePairWeight
              w (Q'.le_of_lt hw) K pair * 2) *
            (1 * leftSquare) +
          ((centralLowerExcitedSpinCubePairWeight
                w (Q'.le_of_lt hw) K pair * 2) *
              (1 * rightSquare) + 0) ≈ _
      refine Q'.eqv_trans _
        ((centralLowerExcitedSpinCubePairWeight
              w (Q'.le_of_lt hw) K pair * 2) * leftSquare +
          (centralLowerExcitedSpinCubePairWeight
              w (Q'.le_of_lt hw) K pair * 2) * rightSquare) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv leftSquare))
          (Q'.eqv_trans _
            ((centralLowerExcitedSpinCubePairWeight
                w (Q'.le_of_lt hw) K pair * 2) * rightSquare + 0) _
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _
                (Q'.one_mul_eqv rightSquare))
              (Q'.eqv_refl 0))
            (Q'.eqv_of_eq (Q'.add_zero' _)))
      · exact Q'.eqv_trans _
          ((centralLowerExcitedSpinCubePairWeight
              w (Q'.le_of_lt hw) K pair * 2) *
            (leftSquare + rightSquare)) _
          (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
          (Q'.mul_assoc_eqv _ _ _)
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left 2 _ _ hspokeSquares)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hendpoint
    (pairWeight_nonnegative hw pair hpair)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.eqv_symm henergy))

/-- Summing the two-edge Cauchy estimate over all stationary ray demands
controls the complete ray pairwise variance by the literal occurrence
energy. -/
theorem centralLowerExcitedSpinCubeRayPairwiseVariance_le_rawOccurrenceEnergy
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeRayPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient ≤
      centralLowerExcitedSpinCubeRayRawOccurrenceEnergy
        w (Q'.le_of_lt hw) K coefficient := by
  have hoffset : centralLowerExcitedSpinCubeOffsetPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient ≤
      centralLowerExcitedSpinCubeRayRawOccurrenceEnergy
        w (Q'.le_of_lt hw) K coefficient := by
    unfold centralLowerExcitedSpinCubeOffsetPairwiseVariance
      centralLowerExcitedSpinCubeRayRawOccurrenceEnergy
      centralLowerExcitedSpinCubeRayFlowOccurrences
    refine Q'.le_trans' _
      (listQSum
        (fun pair => finiteWeightedOccurrenceEnergy
          (centralLowerExcitedSpinCubePairSpokeOccurrences
            w (Q'.le_of_lt hw) K pair)
          coefficient (fun _ _ => 1))
        (centralLowerExcitedSpinCubeEndpointPairs K)) _ ?_ ?_
    · apply listQSum_mono
      intro pair hpair
      exact centralLowerExcitedSpinCubePairwiseTerm_le_occurrenceEnergy
        hw coefficient pair hpair
    · exact Q'.le_of_eqv
        (Q'.eqv_symm (listQSum_flatMap _ _ _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralLowerExcitedSpinCubeRayPairwiseVariance_eqv_offset
        w (Q'.le_of_lt hw) K coefficient))
    hoffset

/-! ## 3. Exact regrouping into the ray edge load -/

/-- The occurrence budget after all repeated uses of a directed spoke have
been grouped into their exact total load. -/
def centralLowerExcitedSpinCubeRayRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralLowerExcitedSpinCubeRayFlowOccurrences w hw K)
    coefficient (fun _ _ => 1)

private theorem rayOccurrence_shape
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeRayFlowOccurrences
        w (Q'.le_of_lt hw) K) :
    ∃ pair, pair ∈ centralLowerExcitedSpinCubeEndpointPairs K ∧
      (occurrence.1 =
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K pair.1, 0) ∨
        occurrence.1 =
          (0, centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K pair.2)) := by
  unfold centralLowerExcitedSpinCubeRayFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hlocal⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralLowerExcitedSpinCubePairSpokeOccurrences at hlocal
  rcases List.mem_cons.mp hlocal with hleft | htail
  · exact ⟨pair, hpair, Or.inl (congrArg Prod.fst hleft)⟩
  · have hright := List.mem_singleton.mp htail
    exact ⟨pair, hpair, Or.inr (congrArg Prod.fst hright)⟩

theorem centralLowerExcitedSpinCubeRayOccurrence_mem_vacuumSector
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeRayFlowOccurrences
        w (Q'.le_of_lt hw) K) :
    occurrence.1.1 ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 ∧
      occurrence.1.2 ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 := by
  rcases rayOccurrence_shape hw occurrence hoccurrence with
    ⟨pair, hpair, hleft | hright⟩
  · rw [hleft]
    have hparts := (mem_cartesian_iff
      (List.range K) (List.range K) pair).mp hpair
    exact ⟨
      centralLowerSpinCubeIndex_mem_vacuumSector hw (by
        have := List.mem_range.mp hparts.1
        omega),
      zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0⟩
  · rw [hright]
    have hparts := (mem_cartesian_iff
      (List.range K) (List.range K) pair).mp hpair
    exact ⟨
      zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0,
      centralLowerSpinCubeIndex_mem_vacuumSector hw (by
        have := List.mem_range.mp hparts.2
        omega)⟩

theorem centralLowerExcitedSpinCubeRayOccurrence_load_nonnegative
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeRayFlowOccurrences
        w (Q'.le_of_lt hw) K) :
    (0 : Q') ≤ occurrence.2 := by
  unfold centralLowerExcitedSpinCubeRayFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hlocal⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralLowerExcitedSpinCubePairSpokeOccurrences at hlocal
  rcases List.mem_cons.mp hlocal with hleft | htail
  · rw [hleft]
    exact Q'.mul_nonneg _ _
      (pairWeight_nonnegative hw pair hpair) (by decide)
  · have hright := List.mem_singleton.mp htail
    rw [hright]
    exact Q'.mul_nonneg _ _
      (pairWeight_nonnegative hw pair hpair) (by decide)

theorem centralLowerExcitedSpinCubeRayFlowLoad_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat) :
    (0 : Q') ≤ centralLowerExcitedSpinCubeRayFlowLoad
      w (Q'.le_of_lt hw) K source target := by
  unfold centralLowerExcitedSpinCubeRayFlowLoad
  exact weightedDirectedEdgeLoad_nonnegative _
    (centralLowerExcitedSpinCubeRayOccurrence_load_nonnegative hw)
    source target

/-- Exact edge-load regrouping: no repeated spoke occurrence is discarded. -/
theorem centralLowerExcitedSpinCubeRayRawOccurrenceEnergy_eqv_loadedDirichlet
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeRayRawOccurrenceEnergy
        w (Q'.le_of_lt hw) K coefficient ≈
      centralLowerExcitedSpinCubeRayRawLoadedDirichlet
        w (Q'.le_of_lt hw) K coefficient := by
  exact Q'.eqv_symm
    (finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw) K 0)
      coefficient (fun _ _ => 1)
      (centralLowerExcitedSpinCubeRayFlowOccurrences
        w (Q'.le_of_lt hw) K)
      (centralLowerExcitedSpinCubeRayOccurrence_mem_vacuumSector hw K))

/-! ## 4. Spoke capacity extends to every directed carrier edge -/

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

namespace CentralLowerExcitedSpinCubeFiniteRayCapacityAt

/-- A finite ray-capacity certificate controls the grouped ray load on every
directed edge.  On a used edge this is one of the two certified spokes; off
the literal occurrence support the nonnegative load is exactly zero. -/
theorem delta_mul_rayFlowLoad_le_physicalKernel
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (source target : Nat) :
    capacity.delta * centralLowerExcitedSpinCubeRayFlowLoad
        w (Q'.le_of_lt hw) K source target ≤
      centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target := by
  let occurrences := centralLowerExcitedSpinCubeRayFlowOccurrences
    w (Q'.le_of_lt hw) K
  let load := centralLowerExcitedSpinCubeRayFlowLoad
    w (Q'.le_of_lt hw) K source target
  have hload0 : (0 : Q') ≤ load :=
    centralLowerExcitedSpinCubeRayFlowLoad_nonnegative
      hw K source target
  by_cases hloadPos : (0 : Q') < load
  · have hwitness := exists_occurrence_of_weightedDirectedEdgeLoad_pos
      occurrences
      (centralLowerExcitedSpinCubeRayOccurrence_load_nonnegative hw)
      source target hloadPos
    rcases hwitness with ⟨occurrence, hoccurrence, hedge⟩
    rcases rayOccurrence_shape hw occurrence hoccurrence with
      ⟨pair, hpair, hleft | hright⟩
    · have hparts := (mem_cartesian_iff
        (List.range K) (List.range K) pair).mp hpair
      have hoffset : pair.1 < K := List.mem_range.mp hparts.1
      have heq := hleft.symm.trans hedge
      cases heq
      exact capacity.left_spoke pair.1 hoffset
    · have hparts := (mem_cartesian_iff
        (List.range K) (List.range K) pair).mp hpair
      have hoffset : pair.2 < K := List.mem_range.mp hparts.2
      have heq := hright.symm.trans hedge
      cases heq
      exact capacity.right_spoke pair.2 hoffset
  · have hloadNonpos : load ≤ 0 :=
      q_nonpos_of_not_pos_local hloadPos
    have hloadZero : load ≈ 0 :=
      Q'.eqv_of_le_le hloadNonpos hload0
    have hkernel0 : (0 : Q') ≤ centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target := by
      unfold centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0 _ _
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_trans _ (capacity.delta * 0) _
          (Q'.mul_eqv_congr_left capacity.delta _ _ hloadZero)
          (Q'.mul_zero_eqv capacity.delta)))
      hkernel0

end CentralLowerExcitedSpinCubeFiniteRayCapacityAt

/-! ## 5. Pointwise capacity contracts to Dirichlet coercivity -/

private theorem finiteJointDirichletBlock_scale_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => scale * joint left right) ≈
      scale * finiteJointDirichletBlock
        leftStates rightStates coefficient joint := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left => scale * listQSum
        (fun right =>
          joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right)))
        rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right => scale *
          (joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ rightStates
  · exact listQSum_mul_left scale _ leftStates

private theorem scale_mul_finiteJointDirichletBlock_le_of_joint_le_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (load kernel : State → State → Q')
    (hjoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        scale * load left right ≤ kernel left right) :
    scale * finiteJointDirichletBlock
        leftStates rightStates coefficient load ≤
      finiteJointDirichletBlock
        leftStates rightStates coefficient kernel := by
  have hsum : finiteJointDirichletBlock
        leftStates rightStates coefficient
          (fun left right => scale * load left right) ≤
      finiteJointDirichletBlock
        leftStates rightStates coefficient kernel := by
    unfold finiteJointDirichletBlock
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (hjoint left hleft right hright)
      (SumOfSquares.q_mul_self_nonneg
        (coefficient left + -coefficient right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletBlock_scale_joint_local
          leftStates rightStates coefficient scale load)))
    hsum

namespace CentralLowerExcitedSpinCubeFiniteRayCapacityAt

theorem delta_mul_rawLoadedDirichlet_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (coefficient : Nat → Q') :
    capacity.delta * centralLowerExcitedSpinCubeRayRawLoadedDirichlet
        w (Q'.le_of_lt hw) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  unfold centralLowerExcitedSpinCubeRayRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change capacity.delta * finiteJointDirichletBlock
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      coefficient
      (fun source target =>
        centralLowerExcitedSpinCubeRayFlowLoad
          w (Q'.le_of_lt hw) K source target * 1) ≤ _
  change _ ≤ finiteJointDirichletBlock
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      coefficient
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
  apply scale_mul_finiteJointDirichletBlock_le_of_joint_le_local
  intro source _hsource target _htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left capacity.delta _ _
        (Q'.mul_one_eqv
          (centralLowerExcitedSpinCubeRayFlowLoad
            w (Q'.le_of_lt hw) K source target))))
    (delta_mul_rayFlowLoad_le_physicalKernel capacity source target)

/-- The finite analytic contraction of ray capacity: the same `delta` that
pays every spoke controls the complete stationary pairwise variance on the
growing excited spin-cube ray by the genuine full-sector physical Dirichlet
energy. -/
theorem delta_mul_rayPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (coefficient : Nat → Q') :
    capacity.delta * centralLowerExcitedSpinCubeRayPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  have hpair :=
    centralLowerExcitedSpinCubeRayPairwiseVariance_le_rawOccurrenceEnergy
      hw K coefficient
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ capacity.delta hpair
    (Q'.le_of_lt capacity.delta_pos)
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left capacity.delta _ _
          (centralLowerExcitedSpinCubeRayRawOccurrenceEnergy_eqv_loadedDirichlet
            hw K coefficient)))
      (delta_mul_rawLoadedDirichlet_le_physicalDirichlet
        capacity coefficient))

end CentralLowerExcitedSpinCubeFiniteRayCapacityAt

/-! ## 6. The cutoff-uniform anchor theorem -/

namespace FixedNomeCofinalSpinCubeRayCapacity

def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (K : Nat) (hK : capacity.start ≤ K) :
    CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K where
  delta := capacity.delta
  delta_pos := capacity.delta_pos
  twice_le_return := fun offset hoffset =>
    capacity.twice_le_return K hK offset hoffset
  left_spoke := fun offset hoffset =>
    capacity.left_spoke K hK offset hoffset
  right_spoke := fun offset hoffset =>
    capacity.right_spoke K hK offset hoffset

theorem delta_mul_rayPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    {K : Nat} (hK : capacity.start ≤ K)
    (coefficient : Nat → Q') :
    capacity.delta * centralLowerExcitedSpinCubeRayPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.CentralLowerExcitedSpinCubeFiniteRayCapacityAt.delta_mul_rayPairwiseVariance_le_physicalDirichlet
    (finiteCapacityAt capacity K hK) coefficient

end FixedNomeCofinalSpinCubeRayCapacity

/-- Concrete cutoff-uniform ray-sector Dirichlet coercivity at the fixed
strong-coupling anchor, valid from the first cutoff onward. -/
theorem anchorCentralSpinCube_delta_mul_rayPairwiseVariance_le_physicalDirichlet
    (K : Nat) (coefficient : Nat → Q') :
    anchorCentralSpinCubeCofinalRayCapacity.delta *
        centralLowerExcitedSpinCubeRayPairwiseVariance
          anchorCoupling (by decide) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          anchorCoupling (by decide) K 0)
        coefficient
        (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0) := by
  exact YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.delta_mul_rayPairwiseVariance_le_physicalDirichlet
    anchorCentralSpinCubeCofinalRayCapacity (K := K) (by
        change 0 ≤ K
        exact Nat.zero_le K) coefficient

end YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.centralLowerExcitedSpinCubeRayPairwiseVariance_eqv_offset
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.centralLowerExcitedSpinCubePairwiseTerm_le_occurrenceEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.centralLowerExcitedSpinCubeRayPairwiseVariance_le_rawOccurrenceEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.centralLowerExcitedSpinCubeRayRawOccurrenceEnergy_eqv_loadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.CentralLowerExcitedSpinCubeFiniteRayCapacityAt.delta_mul_rayFlowLoad_le_physicalKernel
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.CentralLowerExcitedSpinCubeFiniteRayCapacityAt.delta_mul_rayPairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.delta_mul_rayPairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.anchorCentralSpinCube_delta_mul_rayPairwiseVariance_le_physicalDirichlet
