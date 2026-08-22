/-
# Compact cutoff-two vacuum-component introduction rule

This module specializes the generic two-edge component theorem once at the
literal cutoff-two coupling and carrier.  Downstream proofs can provide the
two support edges without elaborating the concrete root-component list.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumComponentIntro

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Cutoff-two specialization of the generic two-edge component
introduction theorem. -/
theorem cutoffTwoVacuumSectorState_mem_of_two_edges
    {hubIndex stateIndex : Nat} {state : EdgeLabelling}
    (hhubIndex : hubIndex < centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) 2 0)
    (hstateIndex : stateIndex < centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) 2 0)
    (hrootHub : centralPhysicalFiniteSupportAdjacentB
      cutoffTwoHalfCoupling (by decide) 2 0 0 hubIndex = true)
    (hhubState : centralPhysicalFiniteSupportAdjacentB
      cutoffTwoHalfCoupling (by decide) 2 0 hubIndex stateIndex = true)
    (hstate : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 stateIndex = state) :
    state ∈ centralPhysicalFiniteVacuumSectorStates
      cutoffTwoHalfCoupling (by decide) 2 0 :=
  centralPhysicalFiniteVacuumSectorState_mem_of_two_edges
    cutoffTwoHalfCoupling (by decide) 2 0
    hhubIndex hstateIndex hrootHub hhubState hstate

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumComponentIntro

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumComponentIntro.cutoffTwoVacuumSectorState_mem_of_two_edges
