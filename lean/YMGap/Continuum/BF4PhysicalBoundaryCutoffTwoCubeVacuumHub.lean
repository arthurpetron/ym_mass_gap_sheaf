/-
# A cutoff-two table hub is adjacent to the physical vacuum

Constructive finite-list search finds the production table's row-zero hub in
the positive carrier and finds the vacuum in the same 65-state table.  The
positive table star gives the hub-to-vacuum edge; support symmetry reverses it
to the root-to-hub edge required by the canonical component.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumHub

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

/-- Proof-only eliminator for a hub index, its state identification, and the
physical root-to-hub support edge.  The index is consumed only inside `Prop`;
no computational witness or modulus is erased. -/
theorem cutoffTwoVacuumHub_elim
    {goal : Prop}
    (consume : ∀ hubIndex,
      hubIndex < centralPhysicalFiniteCarrierSize cutoffTwoHalfCoupling
        (by decide) 2 0 →
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) 2 0 hubIndex = cutoffTwoSectorStateAt 0 →
      centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
        (by decide) 2 0 0 hubIndex = true →
      goal) : goal := by
  have hhubSector : cutoffTwoSectorStateAt 0 ∈ cutoffTwoCubeSectorStates :=
    cutoffTwoSectorStateAt_mem (by decide : 0 < 65)
  obtain ⟨vacuumColumn, hvacuumColumn, hvacuumColumnState⟩ :=
    cutoffTwoCubeSectorState_exists_tableIndex
      zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates
  obtain ⟨hubIndex, hhubIndex, hhubState⟩ :=
    cutoffTwoCubeSectorState_exists_positiveIndex hhubSector
  have hvacuumIndexState :
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) 2 0 0 = cutoffTwoSectorStateAt vacuumColumn :=
    Eq.trans
      (centralPhysicalFiniteStateAt_zero_eq_vacuum
        cutoffTwoHalfCoupling (by decide) 2 0)
      (Eq.symm hvacuumColumnState)
  have hvacuumHub :
      centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
        (by decide) 2 0 0 hubIndex = true :=
    cutoffTwoTableHub_supportEdge_reverse
      hvacuumColumn hhubState hvacuumIndexState
  exact consume hubIndex hhubIndex hhubState hvacuumHub

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumHub

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumHub.cutoffTwoVacuumHub_elim
