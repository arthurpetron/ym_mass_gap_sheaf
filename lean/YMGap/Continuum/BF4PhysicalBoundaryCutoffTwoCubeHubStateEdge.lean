/-
# The cutoff-two table hub reaches every table state

For any state in the exact 65-state sector and any positive-carrier index
representing table row zero, constructive search finds a carrier index for
the state and the sealed production row-zero star supplies the support edge.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumHub

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeHubStateEdge

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Proof-only eliminator for a carrier index representing the table state,
together with its hub edge and literal state equality. -/
theorem cutoffTwoTableHub_stateEdge_elim
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates)
    {hubIndex : Nat}
    (hhubState : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 hubIndex = cutoffTwoSectorStateAt 0)
    {goal : Prop}
    (consume : ∀ stateIndex,
      stateIndex < centralPhysicalFiniteCarrierSize cutoffTwoHalfCoupling
        (by decide) 2 0 →
      centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
        (by decide) 2 0 hubIndex stateIndex = true →
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) 2 0 stateIndex = state →
      goal) : goal := by
  obtain ⟨column, hcolumn, hcolumnState⟩ :=
    cutoffTwoCubeSectorState_exists_tableIndex hstate
  obtain ⟨stateIndex, hstateIndex, hstateState⟩ :=
    cutoffTwoCubeSectorState_exists_positiveIndex hstate
  have hstateIndexTable :
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) 2 0 stateIndex = cutoffTwoSectorStateAt column :=
    Eq.trans hstateState (Eq.symm hcolumnState)
  have hhubStateEdge :
      centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
        (by decide) 2 0 hubIndex stateIndex = true :=
    cutoffTwoTableHub_supportEdge
      hcolumn hhubState hstateIndexTable
  exact consume stateIndex hstateIndex hhubStateEdge hstateState

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeHubStateEdge

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeHubStateEdge.cutoffTwoTableHub_stateEdge_elim
