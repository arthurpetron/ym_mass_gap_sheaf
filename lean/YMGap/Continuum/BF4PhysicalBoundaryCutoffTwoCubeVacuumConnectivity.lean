/-
# Every cutoff-two cube-sector state is vacuum-connected

The exact production-kernel row-zero star connects the table hub to every
state in the 65-state cutoff-two sector.  Constructive finite-list search
finds both the hub and the vacuum in the literal positive-row carrier.  The
symmetrized support graph then gives a two-edge vacuum-to-state chain.

This is an exact finite-cutoff connectivity theorem, not an all-cutoff,
thermodynamic, completed-space, or continuum statement.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeHubStateEdge
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumComponentIntro

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeHubStateEdge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumHub
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumComponentIntro
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Every literal state in the exact 65-state table belongs to the canonical
support component rooted at the physical vacuum index. -/
theorem cutoffTwoCubeSectorState_mem_canonicalVacuumSector
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    state ∈ centralPhysicalFiniteVacuumSectorStates
      cutoffTwoHalfCoupling (by decide) 2 0 := by
  apply cutoffTwoVacuumHub_elim
  intro hubIndex hhubIndex hhubState hvacuumHub
  apply cutoffTwoTableHub_stateEdge_elim hstate hhubState
  intro stateIndex hstateIndex hhubStateEdge hstateState
  exact cutoffTwoVacuumSectorState_mem_of_two_edges
    hhubIndex hstateIndex hvacuumHub hhubStateEdge hstateState

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity.cutoffTwoCubeSectorState_mem_canonicalVacuumSector
