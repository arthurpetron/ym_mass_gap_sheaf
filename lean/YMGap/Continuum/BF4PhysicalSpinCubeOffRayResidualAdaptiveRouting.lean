/-
# Route-parametric positive-path compiler for the BF4 off-ray residual

The existing arbitrary-cutoff residual flow uses one canonical loop-erased
path between every pair of endpoints.  That path is sufficient for finite
connectivity, but it freezes the routing before any BF4-local or multiscale
estimate can choose paths adapted to the spin geometry.

This module exposes the routing choice as constructive `Type`-level data.  A
routing supplies an actual positive physical-kernel path for every ordered
pair in the finite vacuum sector.  The compiler then performs the complete
Cauchy--Schwarz and duplicate-preserving edge-load argument for that supplied
routing.  A pointwise routed capacity compiles losslessly to the already
canonical residual-coercivity interface and hence to the existing completed
strict-contraction consumer.

The canonical loop-erased routing is an inhabitant, and its routed load is
definitionally the previous load.  Thus this is a conservative refinement of
the existing frontier, not a parallel scorecard or a new gap assumption.

No routed capacity family is inhabited here.  No thermodynamic or continuum
limit, continuum Yang--Mills theory, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive routing data and the canonical inhabitant -/

/-- An explicit positive physical-kernel route for every ordered pair in the
finite central vacuum sector.  A future local or multiscale producer may
choose these routes using BF4 spin geometry. -/
structure CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type 1 where
  path : ∀ left right,
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
      PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        left right

/-- The previous loop-erased routing, retained as a literal inhabitant. -/
def canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K where
  path := fun left right hleft hright =>
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K 0 left right hleft hright

/-! ## 2. Routed endpoint Cauchy budget -/

def centralLowerExcitedSpinCubeOffRayResidualRoutedRawPathBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') (left right : Nat) : Q' :=
  if hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    if hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
      let path := routing.path left right hleft hright
      Q'.ofNat (PositiveKernelChainIn.edgeLength path) *
        listQSum (fun value => value * value)
          (PositiveKernelChainIn.edgeDifferences coefficient path)
    else 0
  else 0

theorem centralLowerExcitedSpinCubeOffRayResidual_endpoint_sq_le_routedRawPathBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (coefficient left + -coefficient right) *
        (coefficient left + -coefficient right) ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedRawPathBudget
        routing coefficient left right := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedRawPathBudget
  rw [dif_pos hleft, dif_pos hright]
  exact PositiveKernelChainIn.endpointDifference_sq_le_length_mul_edgeSquareSum
    coefficient (routing.path left right hleft hright)

def centralLowerExcitedSpinCubeOffRayResidualRoutedRawPairBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (centralPhysicalFiniteWeight w hw K 0 pair.1 *
          centralPhysicalFiniteWeight w hw K 0 pair.2) *
        centralLowerExcitedSpinCubeOffRayResidualRoutedRawPathBudget
          routing coefficient pair.1 pair.2)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K 0 state := by
  exact centralPhysicalRowMarginal_nonnegative hw K 0
    (centralPhysicalFiniteStateAt w hw K 0 state)

theorem centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawPairBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
        w hw K coefficient ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedRawPairBudget
        routing coefficient := by
  refine Q'.le_trans' _
    (centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance
      w hw K coefficient) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance_eqv_residual
          w hw K coefficient))
  · unfold centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance
      centralLowerExcitedSpinCubeOffRayResidualRoutedRawPairBudget
    apply listQSum_mono
    intro pair hpair
    have hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (centralLowerExcitedSpinCubeOffRayResidual_endpoint_sq_le_routedRawPathBudget
        routing coefficient pair.1 pair.2 hfull.1 hfull.2)
      (Q'.mul_nonneg _ _
        (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.1)
        (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.2))

/-! ## 3. Routed weighted occurrences and exact regrouping -/

def centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (left right : Nat) : List (WeightedDirectedEdgeOccurrence Nat) :=
  if hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    if hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
      let path := routing.path left right hleft hright
      let load :=
        (centralPhysicalFiniteWeight w hw K 0 left *
            centralPhysicalFiniteWeight w hw K 0 right) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path).map (fun edge => (edge, load))
    else []
  else []

def centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K).flatMap
    (fun pair =>
      centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
        routing pair.1 pair.2)

def centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing)
    source target

def centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceEnergy
    (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing)
    coefficient (fun _ _ => 1)

def centralLowerExcitedSpinCubeOffRayResidualRoutedRawLoadedDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing)
    coefficient (fun _ _ => 1)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathRawOccurrenceEnergy_eqv_pairBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    finiteWeightedOccurrenceEnergy
        (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
          routing left right)
        coefficient (fun _ _ => 1) ≈
      (centralPhysicalFiniteWeight w hw K 0 left *
          centralPhysicalFiniteWeight w hw K 0 right) *
        centralLowerExcitedSpinCubeOffRayResidualRoutedRawPathBudget
          routing coefficient left right := by
  let path := routing.path left right hleft hright
  let pairWeight := centralPhysicalFiniteWeight w hw K 0 left *
    centralPhysicalFiniteWeight w hw K 0 right
  let lengthQ := Q'.ofNat (PositiveKernelChainIn.edgeLength path)
  let edgeSquare : Nat × Nat → Q' := fun edge =>
    (coefficient edge.1 + -coefficient edge.2) *
      (coefficient edge.1 + -coefficient edge.2)
  have hedges := PositiveKernelChainIn.edgeSquareSum_eqv_edgeDifferences
    coefficient path
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
  rw [dif_pos hleft, dif_pos hright]
  unfold finiteWeightedOccurrenceEnergy
  rw [listQSum_map]
  refine Q'.eqv_trans _
    ((pairWeight * lengthQ) *
      listQSum edgeSquare
        (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((pairWeight * lengthQ) *
        listQSum (fun edge => (1 : Q') * edgeSquare edge)
          (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path)) _ ?_ ?_
    · exact listQSum_mul_left (pairWeight * lengthQ) _ _
    · exact Q'.mul_eqv_congr_left (pairWeight * lengthQ) _ _
        (Q'.eqv_trans _ _ _
          (listQSum_congr
            (fun edge => Q'.one_mul_eqv (edgeSquare edge)) _)
          (Q'.eqv_refl _))
  · refine Q'.eqv_trans _
      (pairWeight *
        (lengthQ *
          listQSum edgeSquare
            (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
              path))) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.mul_eqv_congr_left pairWeight _ _ ?_
    refine Q'.eqv_trans _
      (lengthQ *
        listQSum (fun value => value * value)
          (PositiveKernelChainIn.edgeDifferences coefficient path)) _
      (Q'.mul_eqv_congr_left lengthQ _ _ hedges) ?_
    unfold centralLowerExcitedSpinCubeOffRayResidualRoutedRawPathBudget
    rw [dif_pos hleft, dif_pos hright]
    exact Q'.eqv_refl _

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy_eqv_rawPairBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy
        routing coefficient ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedRawPairBudget
        routing coefficient := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy
    centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences
    centralLowerExcitedSpinCubeOffRayResidualRoutedRawPairBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        finiteWeightedOccurrenceEnergy
          (centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences
            routing pair.1 pair.2)
          coefficient (fun _ _ => 1))
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr_on
    intro pair hpair
    have hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathRawOccurrenceEnergy_eqv_pairBudget
        routing coefficient pair.1 pair.2 hfull.1 hfull.2

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_mem_sector
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing) :
    occurrence.1.1 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
      occurrence.1.2 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  simpa only using PositiveKernelChainIn.directedEdges_mem_support
    hfull.1 (routing.path pair.1 pair.2 hfull.1 hfull.2) edge hedge

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_kernel_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing) :
    (0 : Q') < centralPhysicalFiniteKernel
      w hw K 0 occurrence.1.1 occurrence.1.2 := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact PositiveKernelChainIn.directedEdges_kernel_pos
    (routing.path pair.1 pair.2 hfull.1 hfull.2) edge hedge

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_load_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing) :
    (0 : Q') ≤ occurrence.2 := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.1)
      (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.2))
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing source target := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
  exact weightedDirectedEdgeLoad_nonnegative _
    (centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_load_nonnegative
      routing) source target

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy_eqv_loadedDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy
        routing coefficient ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedRawLoadedDirichlet
        routing coefficient := by
  exact Q'.eqv_symm
    (finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
      coefficient (fun _ _ => 1)
      (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing)
      (centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_mem_sector routing))

theorem centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawLoadedDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
        w hw K coefficient ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedRawLoadedDirichlet
        routing coefficient := by
  exact Q'.le_trans' _ _ _
    (centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawPairBudget
      routing coefficient)
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy_eqv_rawPairBudget
            routing coefficient))
        (centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy_eqv_loadedDirichlet
          routing coefficient)))

/-! ## 4. Conservative bridge to the previous canonical routing -/

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_canonical_eq
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
        source target =
      centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w hw K source target := rfl

/-! ## 5. Pointwise routed capacity and lossless coercivity compiler -/

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

structure CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) : Type 1 where
  edge_capacity : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt

theorem sharedFloor_mul_routedRawLoadedDirichlet_le_half_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (flowCapacity :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
        hw K rayCapacity routing)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralLowerExcitedSpinCubeOffRayResidualRoutedRawLoadedDirichlet
          routing coefficient ≤
      HalfPow.half * finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRoutedRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
      finiteJointDirichletBlock
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (fun source target =>
          centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
            routing source target * 1) ≤ _
  change _ ≤ HalfPow.half * finiteJointDirichletBlock
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      coefficient
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
  have hscaled := scale_mul_finiteJointDirichletBlock_le_of_joint_le_local
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    coefficient
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
    (fun source target =>
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing source target * 1)
    (fun source target => HalfPow.half *
      centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target)
    (fun source hsource target htarget =>
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left
            (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity) _ _
            (Q'.mul_one_eqv
              (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
                routing source target))))
        (flowCapacity.edge_capacity source hsource target htarget))
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (finiteJointDirichletBlock_scale_joint_local
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient HalfPow.half
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)))

def toOffRayResidualCoercivityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (flowCapacity :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
      hw K rayCapacity where
  residual_coercivity := fun coefficient => by
    have hresidual :=
      centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawLoadedDirichlet
        routing coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
      hresidual
      (Q'.le_of_lt
        (centralLowerExcitedSpinCubeSharedCoercivityFloor_pos rayCapacity))
    exact Q'.le_trans' _ _ _ hscaled
      (flowCapacity.sharedFloor_mul_routedRawLoadedDirichlet_le_half_physicalDirichlet
        coefficient)

theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (flowCapacity :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
        hw K rayCapacity routing)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
      flowCapacity.toOffRayResidualCoercivityAt coefficient

def ofCanonical
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (flowCapacity : CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
      hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
      hw K rayCapacity
      (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        w (Q'.le_of_lt hw) K) where
  edge_capacity := fun source hsource target htarget => by
    rw [centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_canonical_eq]
    exact flowCapacity.edge_capacity source hsource target htarget

def toCanonical
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (flowCapacity :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
        hw K rayCapacity
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
          w (Q'.le_of_lt hw) K)) :
    CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget => by
    rw [← centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_canonical_eq]
    exact flowCapacity.edge_capacity source hsource target htarget

end CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt

/-! ## 6. Cofinal adaptive routing reaches the existing completed consumer -/

structure FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  routing : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  flow_capacity : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt
      hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)
      (routing K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity

def toCofinalResidualCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualCoercivity hw rayCapacity where
  residual := fun K hK =>
    (family.flow_capacity K hK).toOffRayResidualCoercivityAt

def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toCompletedStrictContractionData
    hw0 hw1 family.toCofinalResidualCoercivity

end FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawPairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.centralLowerExcitedSpinCubeOffRayResidualRoutedRawOccurrenceEnergy_eqv_rawPairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_mem_sector
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawLoadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_canonical_eq
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.toOffRayResidualCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.ofCanonical
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.toCanonical
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity.toCofinalResidualCoercivity
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity.toCompletedStrictContractionData
