/-
# Adaptive exact-mass resistance flow on the full BF4 vacuum sector

The exact-mass root argument removes the component-mass denominator from the
finite Poincare frontier, but its original formulation freezes the root paths
to the generic loop-erased component paths.  Such paths prove connectivity;
they do not expose enough SU(2) geometry for a cofinal congestion estimate.

This module makes the root paths explicit data.  For any constructive positive
routing, resistance-weighted Cauchy--Schwarz and exact rooting give

    pairwiseVariance
      <= componentMass * routedResistanceLoadedDirichlet.

Consequently a single edgewise estimate

    fraction * routedResistanceFlowLoad(source,target) <= 1

compiles to the mass-normalized Poincare and posterior-variance certificates.
The canonical loop-erased routing is recovered by definitional equality, so
the new formulation is a conservative refinement rather than a new
observable.

No cofinal adaptive routing or congestion bound is inhabited here.  The open
mathematical problem is now path design plus a raw electrical-traffic bound,
with neither a component-mass floor nor a global minimum-edge factor.  No
thermodynamic or continuum limit, continuum QFT, or Clay conclusion is
asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K 0 state := by
  exact centralPhysicalRowMarginal_nonnegative hw K 0
    (centralPhysicalFiniteStateAt w hw K 0 state)

private theorem q_min_pos_local {left right : Q'}
    (hleft : (0 : Q') < left) (hright : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases horder : left ≤ right
  · rw [if_pos horder]
    exact hleft
  · rw [if_neg horder]
    exact hright

private theorem recipPos_mul_eqv_one_local
    (value : Q') (hvalue : (0 : Q') < value) :
    Q'.recipPos value hvalue * value ≈ 1 := by
  exact Q'.eqv_trans _ (value * Q'.recipPos value hvalue) _
    (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv value hvalue)

private theorem fraction_mul_mass_mul_eqv_mass_mul_fraction_mul_local
    (fraction mass value : Q') :
    fraction * (mass * value) ≈ mass * (fraction * value) := by
  refine Q'.eqv_trans _ ((fraction * mass) * value) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv fraction mass value)) ?_
  refine Q'.eqv_trans _ ((mass * fraction) * value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.mul_comm_eqv fraction mass)) ?_
  exact Q'.mul_assoc_eqv mass fraction value

/-! ## 1. Exact routed root budget -/

def centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') (state : Nat) : Q' :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    let path := routing.path state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
        path *
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
        coefficient path
  else 0

theorem centralPhysicalFiniteVacuumSector_root_sq_le_routedResistancePathBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (coefficient state + -coefficient 0) *
        (coefficient state + -coefficient 0) ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
        routing coefficient state := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
  rw [dif_pos hstate]
  exact
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.endpointDifference_sq_le_resistance_mul_linearEnergy
      coefficient
      (routing.path state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun state =>
      centralPhysicalFiniteWeight w hw K 0 state *
        centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
          routing coefficient state)
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
      routing coefficient +
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
      routing coefficient

theorem centralPhysicalFiniteVacuumSectorRootVariance_le_routedRootResistanceSingleRawBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootVariance
        w hw K 0 coefficient ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
        routing coefficient := by
  unfold centralPhysicalFiniteVacuumSectorRootVariance
    finiteWeightedRootVariance
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
  apply listQSum_mono
  intro state hstate
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (centralPhysicalFiniteVacuumSector_root_sq_le_routedResistancePathBudget
      routing coefficient state hstate)
    (centralPhysicalFiniteWeight_nonnegative_local w hw K state)

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_routedRootResistanceRawBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K 0 coefficient ≤
      centralPhysicalFiniteVacuumSectorMass w hw K 0 *
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawBudget
          routing coefficient := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw K 0
  let weight := centralPhysicalFiniteWeight w hw K 0
  let mass := centralPhysicalFiniteVacuumSectorMass w hw K 0
  let root := centralPhysicalFiniteVacuumSectorRootVariance
    w hw K 0 coefficient
  let single :=
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
      routing coefficient
  have hexact :=
    finiteWeightedPairwiseVariance_le_twice_mass_rootVariance
      states weight coefficient 0
  have hroot : root ≤ single := by
    unfold root single
    exact
      centralPhysicalFiniteVacuumSectorRootVariance_le_routedRootResistanceSingleRawBudget
        routing coefficient
  have hmass0 : (0 : Q') ≤ mass := by
    exact Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw K 0)
  have hscaled : mass * root ≤ mass * single :=
    Q'.mul_le_mul_of_nonneg_left _ _ mass hroot hmass0
  refine Q'.le_trans' _ (mass * root + mass * root) _ ?_ ?_
  · simpa only [states, weight, mass, root,
      centralPhysicalFiniteVacuumSectorPairwiseVariance,
      centralPhysicalFiniteVacuumSectorMass] using hexact
  · refine Q'.le_trans' _ (mass * single + mass * single) _
      (Q'.add_le_add hscaled hscaled) ?_
    unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawBudget
      single
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_add_eqv mass
          (centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
            routing coefficient)
          (centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
            routing coefficient)))

/-! ## 2. Literal routed electrical traffic -/

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (state : Nat) : List (WeightedDirectedEdgeOccurrence Nat) :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    let path := routing.path state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    let singleLoad := centralPhysicalFiniteWeight w hw K 0 state *
      BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
        path
    (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
      path).map (fun edge => (edge, singleLoad + singleLoad))
  else []

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).flatMap
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
      routing)

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences routing)
    source target

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawOccurrenceEnergy
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceEnergy
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences routing)
    coefficient (centralPhysicalFiniteKernel w hw K 0)

def centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences routing)
    coefficient (centralPhysicalFiniteKernel w hw K 0)

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrenceEnergy_eqv_budget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    finiteWeightedOccurrenceEnergy
        (centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
          routing state)
        coefficient (centralPhysicalFiniteKernel w hw K 0) ≈
      let term := centralPhysicalFiniteWeight w hw K 0 state *
        centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
          routing coefficient state
      term + term := by
  let path := routing.path state 0 hstate
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)
  let weight := centralPhysicalFiniteWeight w hw K 0 state
  let pathResistance :=
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
      path
  let singleLoad := weight * pathResistance
  let edgeEnergy : Nat × Nat → Q' := fun edge =>
    centralPhysicalFiniteKernel w hw K 0 edge.1 edge.2 *
      ((coefficient edge.1 + -coefficient edge.2) *
        (coefficient edge.1 + -coefficient edge.2))
  have hlinear :=
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.linearEnergy_eqv_directedEdges_sum
      coefficient path
  unfold
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
  rw [dif_pos hstate]
  unfold finiteWeightedOccurrenceEnergy
  rw [listQSum_map]
  refine Q'.eqv_trans _
    ((singleLoad + singleLoad) *
      listQSum edgeEnergy
        (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path)) _ ?_ ?_
  · exact listQSum_mul_left (singleLoad + singleLoad) _ _
  · refine Q'.eqv_trans _
      (singleLoad * listQSum edgeEnergy
          (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path) +
        singleLoad * listQSum edgeEnergy
          (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path)) _
      (Q'.add_mul_eqv _ _ _) ?_
    apply Q'.add_eqv_congr'
    · refine Q'.eqv_trans _
        (weight *
          (pathResistance *
            listQSum edgeEnergy
              (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
                path))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.mul_eqv_congr_left weight _ _ ?_
      refine Q'.eqv_trans _
        (pathResistance *
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
            coefficient path) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left pathResistance _ _
          (Q'.eqv_symm hlinear)
      · unfold centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
        rw [dif_pos hstate]
        exact Q'.eqv_refl _
    · refine Q'.eqv_trans _
        (weight *
          (pathResistance *
            listQSum edgeEnergy
              (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
                path))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.mul_eqv_congr_left weight _ _ ?_
      refine Q'.eqv_trans _
        (pathResistance *
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
            coefficient path) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left pathResistance _ _
          (Q'.eqv_symm hlinear)
      · unfold centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
        rw [dif_pos hstate]
        exact Q'.eqv_refl _

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawOccurrenceEnergy_eqv_rawBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawOccurrenceEnergy
        routing coefficient ≈
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawBudget
        routing coefficient := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawOccurrenceEnergy
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawBudget
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceSingleRawBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        finiteWeightedOccurrenceEnergy
          (centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
            routing state)
          coefficient (centralPhysicalFiniteKernel w hw K 0))
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          let term := centralPhysicalFiniteWeight w hw K 0 state *
            centralPhysicalFiniteVacuumSectorRoutedRootResistancePathBudget
              routing coefficient state
          term + term)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)) _ ?_ ?_
    · apply listQSum_congr_on
      intro state hstate
      exact
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrenceEnergy_eqv_budget
          routing coefficient state hstate
    · exact listQSum_add _ _
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceOccurrence_mem_sector
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences
        routing) :
    occurrence.1.1 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
      occurrence.1.2 ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  simpa only using
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
      hstate
      (routing.path state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))
      edge hedge

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceOccurrence_load_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences
        routing) :
    (0 : Q') ≤ occurrence.2 := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  have hsingle : (0 : Q') ≤
      centralPhysicalFiniteWeight w hw K 0 state *
        BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
          (routing.path state 0 hstate
            (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)) :=
    Q'.mul_nonneg _ _
      (centralPhysicalFiniteWeight_nonnegative_local w hw K state)
      (BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance_nonnegative
        (routing.path state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)))
  exact Q'.zero_le_add _ _ hsingle hsingle

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source target := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
  exact weightedDirectedEdgeLoad_nonnegative _
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceOccurrence_load_nonnegative
      routing)
    source target

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet_eqv_occurrenceEnergy
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet
        routing coefficient ≈
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawOccurrenceEnergy
        routing coefficient := by
  exact finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
    coefficient (centralPhysicalFiniteKernel w hw K 0)
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowOccurrences
      routing)
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceOccurrence_mem_sector
      routing)

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_routedRootResistanceRawLoadedDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K 0 coefficient ≤
      centralPhysicalFiniteVacuumSectorMass w hw K 0 *
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet
          routing coefficient := by
  let mass := centralPhysicalFiniteVacuumSectorMass w hw K 0
  have hraw :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_routedRootResistanceRawBudget
      routing coefficient
  have hbudget :
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawBudget
          routing coefficient ≈
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet
          routing coefficient := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawOccurrenceEnergy_eqv_rawBudget
          routing coefficient))
      (Q'.eqv_symm
        (centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet_eqv_occurrenceEnergy
          routing coefficient))
  exact Q'.le_trans' _
    (mass *
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawBudget
        routing coefficient) _ hraw
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left mass _ _ hbudget))

/-! ## 3. Routed raw capacity compiles to the posterior fraction -/

structure CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  edge_capacity : ∀ source target,
    fraction *
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
          routing source target ≤
      1

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

namespace CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt

private theorem fraction_mul_loadedDirichlet_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt
        hw K routing)
    (coefficient : Nat → Q') :
    capacity.fraction *
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet
          routing coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let load := centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
    routing
  let kernel := centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change capacity.fraction *
      finiteJointDirichletBlock states states coefficient
        (fun source target => load source target * kernel source target) ≤
    finiteJointDirichletBlock states states coefficient kernel
  refine Q'.le_trans' _
    (finiteJointDirichletBlock states states coefficient
      (fun source target =>
        capacity.fraction *
          (load source target * kernel source target))) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletBlock_scale_joint_local
          states states coefficient capacity.fraction
          (fun source target => load source target * kernel source target)))
  · unfold finiteJointDirichletBlock
    apply listQSum_mono
    intro source _hsource
    apply listQSum_mono
    intro target _htarget
    have hkernel0 : (0 : Q') ≤ kernel source target := by
      unfold kernel centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0 _ _
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (kernel source target)
      (capacity.edge_capacity source target) hkernel0
    have hjoint :
        capacity.fraction *
            (load source target * kernel source target) ≤
          kernel source target := by
      exact Q'.le_trans' _
        ((capacity.fraction * load source target) *
          kernel source target) _
        (Q'.le_of_eqv
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
        (Q'.le_trans' _ (1 * kernel source target) _ hscaled
          (Q'.le_of_eqv (Q'.one_mul_eqv _)))
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hjoint
      (SumOfSquares.q_mul_self_nonneg
        (coefficient source + -coefficient target))

def toMassNormalizedPairwiseCoercivityData
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt
        hw K routing) :
    CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
      w (Q'.le_of_lt hw) K 0 where
  fraction := capacity.fraction
  fraction_pos := capacity.fraction_pos
  fraction_le_one := capacity.fraction_le_one
  coercivity := fun coefficient => by
    let mass := centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K 0
    let loaded :=
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceRawLoadedDirichlet
        routing coefficient
    let energy := finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      coefficient
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
    have hroot :=
      centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_routedRootResistanceRawLoadedDirichlet
        routing coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ capacity.fraction
      hroot (Q'.le_of_lt capacity.fraction_pos)
    have hlocal : capacity.fraction * loaded ≤ energy := by
      unfold loaded energy
      exact capacity.fraction_mul_loadedDirichlet_le_physicalDirichlet
        coefficient
    have hmass0 : (0 : Q') ≤ mass := by
      unfold mass
      exact Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorWeightSum_pos
          w (Q'.le_of_lt hw) K 0)
    have hmassScaled := Q'.mul_le_mul_of_nonneg_left _ _ mass
      hlocal hmass0
    exact Q'.le_trans' _ (capacity.fraction * (mass * loaded)) _
      hscaled
      (Q'.le_trans' _ (mass * (capacity.fraction * loaded)) _
        (Q'.le_of_eqv
          (fraction_mul_mass_mul_eqv_mass_mul_fraction_mul_local
            capacity.fraction mass loaded))
        hmassScaled)

def toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt
        hw K routing) :=
  capacity.toMassNormalizedPairwiseCoercivityData
    |>.toConditionalVarianceGapData

end CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt

/-! ## 4. Canonical recovery and the exact adaptive cofinal frontier -/

theorem centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_canonical_eq
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
        source target =
      centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
        w hw K 0 source target := by
  rfl

/-- The remaining observable path-design problem: choose one positive routing
at every later cutoff and bound its raw resistance traffic by one scalar. -/
structure FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  bound : Q'
  bound_nonnegative : (0 : Q') ≤ bound
  routing : ∀ K, start ≤ K →
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  flowLoad_le : ∀ K, (hK : start ≤ K) → ∀ source target,
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (routing K hK) source target ≤
      bound

namespace FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound

def cost
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) : Q' :=
  1 + family.bound

theorem cost_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) :
    (0 : Q') < family.cost := by
  unfold cost
  exact Q'.pos_add_nonneg (by decide) family.bound_nonnegative

def fraction
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) : Q' :=
  Q'.min' 1 (Q'.recipPos family.cost family.cost_pos)

theorem fraction_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) :
    (0 : Q') < family.fraction := by
  unfold fraction
  exact q_min_pos_local (by decide) (Q'.recipPos_pos _ _)

theorem fraction_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) :
    family.fraction ≤ (1 : Q') := by
  unfold fraction
  exact Q'.min_le_left' _ _

theorem flowLoad_le_cost
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw)
    {K : Nat} (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (family.routing K hK) source target ≤
      family.cost := by
  have hbound := family.flowLoad_le K hK source target
  have hadd := Q'.add_le_add_right (0 : Q') 1 family.bound
    (by decide : (0 : Q') ≤ 1)
  have hboundCost : family.bound ≤ family.cost := by
    unfold cost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hbound hboundCost

theorem fraction_mul_flowLoad_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw)
    {K : Nat} (hK : family.start ≤ K) (source target : Nat) :
    family.fraction *
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
          (family.routing K hK) source target ≤
      1 := by
  let reciprocal := Q'.recipPos family.cost family.cost_pos
  let load := centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
    (family.routing K hK) source target
  have hfraction : family.fraction ≤ reciprocal := by
    unfold fraction reciprocal
    exact Q'.min_le_right' _ _
  have hload0 : (0 : Q') ≤ load := by
    unfold load
    exact centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_nonnegative
      (family.routing K hK) source target
  have hreciprocal0 : (0 : Q') ≤ reciprocal := by
    unfold reciprocal
    exact Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ load
    hfraction hload0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ reciprocal
    (family.flowLoad_le_cost hK source target) hreciprocal0
  exact Q'.le_trans' _ (reciprocal * load) _ hfirst
    (Q'.le_trans' _ (reciprocal * family.cost) _ hsecond
      (Q'.le_of_eqv
        (recipPos_mul_eqv_one_local family.cost family.cost_pos)))

def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) :
    CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt
      hw K (family.routing K hK) where
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  edge_capacity := fun source target =>
    family.fraction_mul_flowLoad_le_one hK source target

def toCofinalMassNormalizedPairwiseCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) :
    FixedNomeCofinalMassNormalizedPairwiseCoercivity hw where
  start := family.start
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  coercivity := fun K hK coefficient =>
    (family.finiteCapacityAt K hK).toMassNormalizedPairwiseCoercivityData
      |>.coercivity coefficient

def toCofinalConditionalVarianceFraction
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
        hw) :=
  family.toCofinalMassNormalizedPairwiseCoercivity
    |>.toCofinalConditionalVarianceFraction

/-- The adaptive theorem strictly contains the old canonical frontier. -/
def ofCanonical
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :
    FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
      hw where
  start := family.start
  bound := family.bound
  bound_nonnegative := family.bound_nonnegative
  routing := fun K _hK =>
    canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  flowLoad_le := fun K hK source target => by
    rw [centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_canonical_eq]
    exact family.flowLoad_le K hK source target

end FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_routedRootResistanceRawLoadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow.CentralPhysicalFiniteVacuumSectorMassExactAdaptiveRootResistanceFlowCapacityAt.toMassNormalizedPairwiseCoercivityData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow.centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_canonical_eq
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow.FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound.toCofinalConditionalVarianceFraction
