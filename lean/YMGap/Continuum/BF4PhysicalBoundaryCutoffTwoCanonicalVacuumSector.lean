/-
# The cutoff-two 65-state block is the canonical vacuum component

The exact 65-state cube-subset block is already known to be row-closed and to
contain the vacuum.  This module proves the missing converse: every one of its
states is connected to the vacuum in the exact production-kernel support
graph.  The first stored row is strictly positive in all 65 columns, so the
fundamental cube is a hub, and the vacuum has a strictly positive edge to that
hub.

Consequently the literal 65-state block and the canonical finite vacuum
component have exactly the same state support.  This is finite cutoff two
only; it supplies neither a compatible cofinal sector family nor any limit.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorNoEscape

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorNoEscape
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-! ## 3. No canonical-vacuum path can leave the closed table sector -/

private theorem chain_stays_in_cutoffTwoSector
    {sourceIndex targetIndex : Nat}
    (chain : ChainIn
      (centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
        (by decide) 2 0)
      (centralPhysicalFiniteVacuumSectorIndices cutoffTwoHalfCoupling
        (by decide) 2 0)
      sourceIndex targetIndex)
    (hsourceIndex : sourceIndex < centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) 2 0)
    (hsource : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 sourceIndex ∈
      cutoffTwoCubeSectorStates) :
    centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 targetIndex ∈
      cutoffTwoCubeSectorStates := by
  induction chain with
  | refl _ => exact hsource
  | @step source next target hedge hnext rest ih =>
      have hnextIndex :=
        centralPhysicalFiniteVacuumSectorIndex_lt
          cutoffTwoHalfCoupling (by decide) 2 0 hnext
      have hnextSector := next_state_mem_cutoffTwoSector_of_adjacent
        hsourceIndex hnextIndex hsource hedge
      exact ih hnextIndex hnextSector

theorem canonicalVacuumSectorState_mem_cutoffTwoCubeSector
    {state : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates
      cutoffTwoHalfCoupling (by decide) 2 0) :
    state ∈ cutoffTwoCubeSectorStates := by
  rcases List.mem_map.mp hstate with ⟨index, hindex, hstateAt⟩
  have hzero := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 0
  have hchain := centralPhysicalFiniteVacuumSector_connected
    cutoffTwoHalfCoupling (by decide) 2 0 0 index hzero hindex
  have hvacuumSector : zeroEdgeLabelling ∈ cutoffTwoCubeSectorStates :=
    zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates
  have hrootSector : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 0 ∈
      cutoffTwoCubeSectorStates := by
    rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
    exact hvacuumSector
  have hrootIndex := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hzero
  have hfinal := chain_stays_in_cutoffTwoSector
    hchain hrootIndex hrootSector
  rw [hstateAt] at hfinal
  exact hfinal

/-- Exact support equality: the independently constructed canonical vacuum
component at cutoff two is precisely the certified 65-state sector. -/
theorem centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff
    (state : EdgeLabelling) :
    state ∈ centralPhysicalFiniteVacuumSectorStates
        cutoffTwoHalfCoupling (by decide) 2 0 ↔
      state ∈ cutoffTwoCubeSectorStates := by
  exact ⟨canonicalVacuumSectorState_mem_cutoffTwoCubeSector,
    cutoffTwoCubeSectorState_mem_canonicalVacuumSector⟩

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity.cutoffTwoCubeSectorState_mem_canonicalVacuumSector
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector.canonicalVacuumSectorState_mem_cutoffTwoCubeSector
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector.centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff
