/-
# Explicit all-spin vacuum spokes in the finite BF4 sector

The preceding carrier-growth theorem used existential carrier indices only
for counting.  A weighted-flow redesign needs actual computable vertices and
literal short paths.  This module locates every cutoff-admitted spin cube by
its faithful natural-number BF4 code, proves that the located vertex is in the
rooted vacuum component, and constructs the two oriented positive-kernel
spokes between it and the vacuum root.

Composing two spokes gives a path between any two spin cubes with exactly two
edges, independently of the cutoff and of the size of the full carrier.  This
shows that the growing spin-cube ray itself does not force the global `N^2`
path-length loss.  No capacity bound on the spoke loads, full-sector gap,
thermodynamic/continuum limit, or Clay conclusion is asserted.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
import YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth

namespace YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. A computable carrier index for every admitted spin cube -/

def centralLowerSpinCubeIndex
    (w : Q') (hw : (0 : Q') ≤ w) (K spin : Nat) : Nat :=
  centralPhysicalFiniteIndexOfState w hw K 0
    (centralLowerSpinCubeState spin)

theorem centralLowerSpinCubeIndex_lt
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin <
      centralPhysicalFiniteCarrierSize w (Q'.le_of_lt hw) K 0 := by
  unfold centralLowerSpinCubeIndex
  exact centralPhysicalFiniteIndexOfState_lt
    (centralLowerSpinCubeState_mem_centralPositiveHalfStates hw hspin)

theorem centralPhysicalFiniteStateAt_spinCubeIndex_eq
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) =
      centralLowerSpinCubeState spin := by
  unfold centralLowerSpinCubeIndex
  exact centralPhysicalFiniteStateAt_indexOfState_eq
    (centralLowerSpinCubeState_mem_centralPositiveHalfStates hw hspin)

/-! ## 2. Literal positive edges in both orientations -/

theorem centralPhysicalFiniteKernel_spinCubeIndex_zero_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0
      (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) 0 := by
  unfold centralPhysicalFiniteKernel
  rw [centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hspin,
    centralPhysicalFiniteStateAt_zero_eq_vacuum]
  exact centralLowerSpinCubeNormalizedJoint_pos hw hspin

theorem centralPhysicalFiniteKernel_zero_spinCubeIndex_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0 0
      (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) := by
  unfold centralPhysicalFiniteKernel
  rw [centralPhysicalFiniteStateAt_zero_eq_vacuum,
    centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hspin]
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_pos
    (centralPhysicalReflectedKernel_vacuum_spinCube_pos hw hspin)
    (Q'.recipPos_pos _ _)

theorem centralLowerSpinCubeIndex_mem_vacuumSector
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 := by
  let index := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
  have hindexCarrier : index ∈
      centralPhysicalFiniteIndexCarrier w (Q'.le_of_lt hw) K 0 :=
    List.mem_range.mpr (centralLowerSpinCubeIndex_lt hw hspin)
  have hadjacent :
      centralPhysicalFiniteSupportAdjacentB
        w (Q'.le_of_lt hw) K 0 0 index = true := by
    exact centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos
      w (Q'.le_of_lt hw) K 0
      (centralPhysicalFiniteStateAt_zero_eq_vacuum
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hspin)
      (centralPhysicalReflectedKernel_vacuum_spinCube_pos hw hspin)
  exact rootComponent_closed_under_edge
    (centralPhysicalFiniteSupportAdjacentB
      w (Q'.le_of_lt hw) K 0)
    (centralPhysicalFiniteSupportAdjacentB_symmetric
      w (Q'.le_of_lt hw) K 0)
    (zero_mem_centralPhysicalFiniteIndexCarrier
      w (Q'.le_of_lt hw) K 0)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    hindexCarrier hadjacent

/-! ## 3. Uniformly short positive-kernel spokes and star paths -/

def centralVacuumToLowerSpinCubeSpoke
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      0 (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) :=
  PositiveKernelChainIn.step
    (centralPhysicalFiniteKernel_zero_spinCubeIndex_pos hw hspin)
    (centralLowerSpinCubeIndex_mem_vacuumSector hw hspin)
    (PositiveKernelChainIn.refl _)

def centralLowerSpinCubeToVacuumSpoke
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin) 0 :=
  PositiveKernelChainIn.step
    (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw hspin)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (PositiveKernelChainIn.refl _)

def centralLowerSpinCubeStarPath
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (leftSpin rightSpin : Nat)
    (hleft : leftSpin ≤ K) (hright : rightSpin ≤ K) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K leftSpin)
      (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K rightSpin) :=
  PositiveKernelChainIn.trans
    (centralLowerSpinCubeToVacuumSpoke hw hleft)
    (centralVacuumToLowerSpinCubeSpoke hw hright)

theorem centralVacuumToLowerSpinCubeSpoke_edgeLength
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    PositiveKernelChainIn.edgeLength
        (centralVacuumToLowerSpinCubeSpoke hw hspin) = 1 := by
  rfl

theorem centralLowerSpinCubeStarPath_edgeLength
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (leftSpin rightSpin : Nat)
    (hleft : leftSpin ≤ K) (hright : rightSpin ≤ K) :
    PositiveKernelChainIn.edgeLength
        (centralLowerSpinCubeStarPath
          hw leftSpin rightSpin hleft hright) = 2 := by
  rfl

theorem centralLowerSpinCubeStarPath_directedEdges
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (leftSpin rightSpin : Nat)
    (hleft : leftSpin ≤ K) (hright : rightSpin ≤ K) :
    PositiveKernelChainIn.directedEdges
        (centralLowerSpinCubeStarPath
          hw leftSpin rightSpin hleft hright) =
      [ (centralLowerSpinCubeIndex
          w (Q'.le_of_lt hw) K leftSpin, 0),
        (0, centralLowerSpinCubeIndex
          w (Q'.le_of_lt hw) K rightSpin) ] := by
  rfl

/-- The spin-cube ray has a cutoff-independent two-edge Cauchy geometry.  The
remaining weighted-flow problem is capacity on the displayed vacuum spokes,
not the cardinality of the full physical carrier. -/
theorem centralLowerSpinCube_endpoint_sq_le_two_spoke_square_sum
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (coefficient : Nat → Q')
    (leftSpin rightSpin : Nat)
    (hleft : leftSpin ≤ K) (hright : rightSpin ≤ K) :
    let path := centralLowerSpinCubeStarPath
      hw leftSpin rightSpin hleft hright
    (coefficient
          (centralLowerSpinCubeIndex
            w (Q'.le_of_lt hw) K leftSpin) +
        -coefficient
          (centralLowerSpinCubeIndex
            w (Q'.le_of_lt hw) K rightSpin)) *
      (coefficient
          (centralLowerSpinCubeIndex
            w (Q'.le_of_lt hw) K leftSpin) +
        -coefficient
          (centralLowerSpinCubeIndex
            w (Q'.le_of_lt hw) K rightSpin)) ≤
      Q'.ofNat 2 *
        listQSum (fun value => value * value)
          (PositiveKernelChainIn.edgeDifferences coefficient path) := by
  dsimp only
  have hbound :=
    PositiveKernelChainIn.endpointDifference_sq_le_length_mul_edgeSquareSum
      coefficient
      (centralLowerSpinCubeStarPath
        hw leftSpin rightSpin hleft hright)
  rw [centralLowerSpinCubeStarPath_edgeLength
    hw leftSpin rightSpin hleft hright] at hbound
  exact hbound

end YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralLowerSpinCubeIndex_lt
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralPhysicalFiniteStateAt_spinCubeIndex_eq
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralPhysicalFiniteKernel_spinCubeIndex_zero_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralPhysicalFiniteKernel_zero_spinCubeIndex_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralLowerSpinCubeIndex_mem_vacuumSector
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralVacuumToLowerSpinCubeSpoke_edgeLength
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralLowerSpinCubeStarPath_edgeLength
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralLowerSpinCubeStarPath_directedEdges
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes.centralLowerSpinCube_endpoint_sq_le_two_spoke_square_sum
