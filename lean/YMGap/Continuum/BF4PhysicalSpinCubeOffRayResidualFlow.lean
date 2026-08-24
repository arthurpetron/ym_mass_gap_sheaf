/-
# A literal positive-path flow for the spin-cube off-ray residual

The exact residual frontier partitions the full stationary pairwise form into
the already controlled spin-cube ray and the three ordered blocks containing
at least one off-ray endpoint.  This module enumerates precisely those three
blocks and routes every stationary endpoint demand along the existing
loop-erased positive-physical-kernel path.

Each directed path edge receives the endpoint stationary-product weight times
the path length.  Finite Cauchy--Schwarz controls every endpoint square, and
duplicate-preserving regrouping contracts the entire coefficient-dependent
residual to one explicit coefficient-independent directed-edge load.

No uniform comparison between this residual load and the physical kernel is
proved here.  Thus no full-sector coercivity, transfer gap, thermodynamic or
continuum limit, continuum QFT, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal enumeration of the three residual endpoint blocks -/

/-- Ordered endpoint pairs containing at least one off-ray state, in exactly
the ray--off, off--ray, off--off order of the residual frontier. -/
def centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List (Nat × Nat) :=
  cartesian
      (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
      (centralLowerExcitedSpinCubeOffRayIndices w hw K) ++
    (cartesian
        (centralLowerExcitedSpinCubeOffRayIndices w hw K)
        (centralLowerExcitedSpinCubeFilteredRayIndices w hw K) ++
      cartesian
        (centralLowerExcitedSpinCubeOffRayIndices w hw K)
        (centralLowerExcitedSpinCubeOffRayIndices w hw K))

theorem centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat} {pair : Nat × Nat}
    (hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) :
    pair.1 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
      pair.2 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  rcases List.mem_append.mp hpair with hrayOff | hoffRayOrOffOff
  · have hparts := (mem_cartesian_iff
      (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
      (centralLowerExcitedSpinCubeOffRayIndices w hw K) pair).mp hrayOff
    exact ⟨(List.mem_filter.mp hparts.1).1,
      (List.mem_filter.mp hparts.2).1⟩
  · rcases List.mem_append.mp hoffRayOrOffOff with hoffRay | hoffOff
    · have hparts := (mem_cartesian_iff
        (centralLowerExcitedSpinCubeOffRayIndices w hw K)
        (centralLowerExcitedSpinCubeFilteredRayIndices w hw K) pair).mp hoffRay
      exact ⟨(List.mem_filter.mp hparts.1).1,
        (List.mem_filter.mp hparts.2).1⟩
    · have hparts := (mem_cartesian_iff
        (centralLowerExcitedSpinCubeOffRayIndices w hw K)
        (centralLowerExcitedSpinCubeOffRayIndices w hw K) pair).mp hoffOff
      exact ⟨(List.mem_filter.mp hparts.1).1,
        (List.mem_filter.mp hparts.2).1⟩

/-- The residual stationary form written as a single literal endpoint list. -/
def centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (centralPhysicalFiniteWeight w hw K 0 pair.1 *
          centralPhysicalFiniteWeight w hw K 0 pair.2) *
        ((coefficient pair.1 + -coefficient pair.2) *
          (coefficient pair.1 + -coefficient pair.2)))
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

private theorem finiteStationaryBlock_eqv_cartesian_local
    {State : Type}
    (leftStates rightStates : List State)
    (weight coefficient : State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (finiteStationaryProductJoint weight) ≈
      listQSum
        (fun pair =>
          (weight pair.1 * weight pair.2) *
            ((coefficient pair.1 + -coefficient pair.2) *
              (coefficient pair.1 + -coefficient pair.2)))
        (cartesian leftStates rightStates) := by
  unfold finiteJointDirichletBlock finiteStationaryProductJoint cartesian
  let entry : State × State → Q' := fun pair =>
    (weight pair.1 * weight pair.2) *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
  have hflat := listQSum_flatMap entry
    (fun left => rightStates.map (fun right => (left, right))) leftStates
  have hrows : listQSum
      (fun left =>
        listQSum entry
          (rightStates.map (fun right => (left, right))))
      leftStates ≈
      listQSum
        (fun left => listQSum
          (fun right =>
            (weight left * weight right) *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates)
        leftStates := by
    apply listQSum_congr
    intro left
    rw [listQSum_map]
    exact Q'.eqv_refl _
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hflat hrows)

/-- The single endpoint list is exactly the previously isolated three-block
off-ray residual, with no omitted or added stationary demand. -/
theorem centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance_eqv_residual
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance
        w hw K coefficient ≈
      centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
        w hw K coefficient := by
  let entry : Nat × Nat → Q' := fun pair =>
    (centralPhysicalFiniteWeight w hw K 0 pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
  unfold centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance
    centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
  refine Q'.eqv_trans _
    (listQSum entry
        (cartesian
          (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
          (centralLowerExcitedSpinCubeOffRayIndices w hw K)) +
      (listQSum entry
          (cartesian
            (centralLowerExcitedSpinCubeOffRayIndices w hw K)
            (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)) +
        listQSum entry
          (cartesian
            (centralLowerExcitedSpinCubeOffRayIndices w hw K)
            (centralLowerExcitedSpinCubeOffRayIndices w hw K)))) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (listQSum_append _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (listQSum_append _ _ _))
  · unfold centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
      centralLowerExcitedSpinCubeRayOffPairwiseVariance
      centralLowerExcitedSpinCubeOffRayPairwiseVariance
      centralLowerExcitedSpinCubeOffOffPairwiseVariance
    dsimp only [entry]
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm
        (finiteStationaryBlock_eqv_cartesian_local _ _ _ coefficient))
      (Q'.add_eqv_congr'
        (Q'.eqv_symm
          (finiteStationaryBlock_eqv_cartesian_local _ _ _ coefficient))
        (Q'.eqv_symm
          (finiteStationaryBlock_eqv_cartesian_local _ _ _ coefficient)))

/-! ## 2. Raw Cauchy budget along one loop-erased positive path -/

def centralLowerExcitedSpinCubeOffRayResidualRawPathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') (left right : Nat) : Q' :=
  if hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    if hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
      let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K 0 left right hleft hright
      Q'.ofNat
          (PositiveKernelChainIn.edgeLength path) *
        listQSum (fun value => value * value)
          (PositiveKernelChainIn.edgeDifferences coefficient path)
    else 0
  else 0

theorem centralLowerExcitedSpinCubeOffRayResidual_endpoint_sq_le_rawPathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (coefficient left + -coefficient right) *
        (coefficient left + -coefficient right) ≤
      centralLowerExcitedSpinCubeOffRayResidualRawPathBudget
        w hw K coefficient left right := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRawPathBudget
  rw [dif_pos hleft, dif_pos hright]
  exact PositiveKernelChainIn.endpointDifference_sq_le_length_mul_edgeSquareSum
    coefficient
    (centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K 0 left right hleft hright)

def centralLowerExcitedSpinCubeOffRayResidualRawPairBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (centralPhysicalFiniteWeight w hw K 0 pair.1 *
          centralPhysicalFiniteWeight w hw K 0 pair.2) *
        centralLowerExcitedSpinCubeOffRayResidualRawPathBudget
          w hw K coefficient pair.1 pair.2)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K 0 state := by
  exact centralPhysicalRowMarginal_nonnegative hw K 0
    (centralPhysicalFiniteStateAt w hw K 0 state)

theorem centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawPairBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
        w hw K coefficient ≤
      centralLowerExcitedSpinCubeOffRayResidualRawPairBudget
        w hw K coefficient := by
  refine Q'.le_trans' _
    (centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance
      w hw K coefficient) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance_eqv_residual
          w hw K coefficient))
  · unfold centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance
      centralLowerExcitedSpinCubeOffRayResidualRawPairBudget
    apply listQSum_mono
    intro pair hpair
    have hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (centralLowerExcitedSpinCubeOffRayResidual_endpoint_sq_le_rawPathBudget
        w hw K coefficient pair.1 pair.2 hfull.1 hfull.2)
      (Q'.mul_nonneg _ _
        (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.1)
        (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.2))

/-! ## 3. Literal weighted occurrences and exact regrouping -/

/-- One endpoint demand contributes the common load
`weight(left) * weight(right) * pathLength` to every directed edge of its
loop-erased positive path. -/
def centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K left right : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  if hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    if hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
      let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K 0 left right hleft hright
      let load :=
        (centralPhysicalFiniteWeight w hw K 0 left *
            centralPhysicalFiniteWeight w hw K 0 right) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path).map
        (fun edge => (edge, load))
    else []
  else []

def centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K).flatMap
    (fun pair =>
      centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
        w hw K pair.1 pair.2)

def centralLowerExcitedSpinCubeOffRayResidualFlowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences w hw K)
    source target

def centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceEnergy
    (centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences w hw K)
    coefficient (fun _ _ => 1)

def centralLowerExcitedSpinCubeOffRayResidualRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences w hw K)
    coefficient (fun _ _ => 1)

theorem centralLowerExcitedSpinCubeOffRayResidualWeightedPathRawOccurrenceEnergy_eqv_pairBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    finiteWeightedOccurrenceEnergy
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K left right)
        coefficient (fun _ _ => 1) ≈
      (centralPhysicalFiniteWeight w hw K 0 left *
          centralPhysicalFiniteWeight w hw K 0 right) *
        centralLowerExcitedSpinCubeOffRayResidualRawPathBudget
          w hw K coefficient left right := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw K 0 left right hleft hright
  let pairWeight := centralPhysicalFiniteWeight w hw K 0 left *
    centralPhysicalFiniteWeight w hw K 0 right
  let lengthQ := Q'.ofNat (PositiveKernelChainIn.edgeLength path)
  let edgeSquare : Nat × Nat → Q' := fun edge =>
    (coefficient edge.1 + -coefficient edge.2) *
      (coefficient edge.1 + -coefficient edge.2)
  have hedges := PositiveKernelChainIn.edgeSquareSum_eqv_edgeDifferences
    coefficient path
  unfold centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
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
        listQSum
          (fun edge => (1 : Q') * edgeSquare edge)
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
    unfold centralLowerExcitedSpinCubeOffRayResidualRawPathBudget
    rw [dif_pos hleft, dif_pos hright]
    exact Q'.eqv_refl _

theorem centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy_eqv_rawPairBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy
        w hw K coefficient ≈
      centralLowerExcitedSpinCubeOffRayResidualRawPairBudget
        w hw K coefficient := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy
    centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences
    centralLowerExcitedSpinCubeOffRayResidualRawPairBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        finiteWeightedOccurrenceEnergy
          (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
            w hw K pair.1 pair.2)
          coefficient (fun _ _ => 1))
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr_on
    intro pair hpair
    have hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    exact
      centralLowerExcitedSpinCubeOffRayResidualWeightedPathRawOccurrenceEnergy_eqv_pairBudget
        w hw K coefficient pair.1 pair.2 hfull.1 hfull.2

theorem centralLowerExcitedSpinCubeOffRayResidualOccurrence_mem_sector
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences w hw K) :
    occurrence.1.1 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
      occurrence.1.2 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  unfold centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  unfold centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  simpa only using PositiveKernelChainIn.directedEdges_mem_support
    hfull.1
    (centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K 0 pair.1 pair.2 hfull.1 hfull.2)
    edge hedge

theorem centralLowerExcitedSpinCubeOffRayResidualOccurrence_kernel_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences w hw K) :
    (0 : Q') < centralPhysicalFiniteKernel
      w hw K 0 occurrence.1.1 occurrence.1.2 := by
  unfold centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  unfold centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact PositiveKernelChainIn.directedEdges_kernel_pos
    (centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K 0 pair.1 pair.2 hfull.1 hfull.2)
    edge hedge

theorem centralLowerExcitedSpinCubeOffRayResidualOccurrence_load_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences w hw K) :
    (0 : Q') ≤ occurrence.2 := by
  unfold centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  unfold centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.1)
      (centralPhysicalFiniteWeight_nonnegative_local w hw K pair.2))
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

theorem centralLowerExcitedSpinCubeOffRayResidualFlowLoad_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    (0 : Q') ≤ centralLowerExcitedSpinCubeOffRayResidualFlowLoad
      w hw K source target := by
  unfold centralLowerExcitedSpinCubeOffRayResidualFlowLoad
  exact weightedDirectedEdgeLoad_nonnegative _
    (centralLowerExcitedSpinCubeOffRayResidualOccurrence_load_nonnegative
      w hw K)
    source target

theorem centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy_eqv_loadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy
        w hw K coefficient ≈
      centralLowerExcitedSpinCubeOffRayResidualRawLoadedDirichlet
        w hw K coefficient := by
  exact Q'.eqv_symm
    (finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
      coefficient (fun _ _ => 1)
      (centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences w hw K)
      (centralLowerExcitedSpinCubeOffRayResidualOccurrence_mem_sector w hw K))

/-- Floor-free residual control, fully contracted to one explicit
coefficient-independent directed-edge load. -/
theorem centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
        w hw K coefficient ≤
      centralLowerExcitedSpinCubeOffRayResidualRawLoadedDirichlet
        w hw K coefficient := by
  exact Q'.le_trans' _ _ _
    (centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawPairBudget
      w hw K coefficient)
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy_eqv_rawPairBudget
            w hw K coefficient))
        (centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy_eqv_loadedDirichlet
          w hw K coefficient)))

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance_eqv_residual
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawPairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy_eqv_rawPairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualOccurrence_mem_sector
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualOccurrence_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy_eqv_loadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow.centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawLoadedDirichlet
