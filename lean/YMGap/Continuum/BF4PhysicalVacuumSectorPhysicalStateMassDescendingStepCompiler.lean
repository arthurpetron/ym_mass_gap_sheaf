/-
# Compile physical-state BF4 lowering into indexed mass-descending steps

The finite BF4 routing graph is indexed, while a native local construction is
more naturally stated on literal lower-half edge labellings.  The repository
already has a constructive faithful-code locator for any positive physical
state.  This module uses that locator to turn literal state-level lowering data
into the indexed local-step interface.

The producer must still prove that its lowered labelling belongs to the
positive carrier and the vacuum-sector state list, that the normalized
reflected kernel from the source to the lowered state is positive, and that
literal twice-spin mass decreases.  None of these analytic or combinatorial
fields is inhabited here.  The accepted paired peel is still a different
two-replica carrier and is not silently identified with this single-state
input.  No congestion, continuum, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-! ## 1. Literal physical-state producer -/

/-- A single-state lowering rule for every non-root indexed source.  The
lowered labelling is literal data; the faithful-code locator will recover its
finite carrier index. -/
structure CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type 1 where
  lowerState : ∀ state,
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
    state ≠ 0 → EdgeLabelling
  lowerState_mem_positive : ∀ state hstate hnonzero,
    lowerState state hstate hnonzero ∈
      centralPositiveHalfStates w hw K 0
  lowerState_mem_vacuumSector : ∀ state hstate hnonzero,
    lowerState state hstate hnonzero ∈
      centralPhysicalFiniteVacuumSectorStates w hw K 0
  kernel_pos : ∀ state hstate hnonzero,
    (0 : Q') < centralNormalizedPhysicalReflectedKernel w hw K 0
      (centralPhysicalFiniteStateAt w hw K 0 state)
      (lowerState state hstate hnonzero)
  physicalMass_lt : ∀ state hstate hnonzero,
    listNatWeight (lowerState state hstate hnonzero)
        (centralLowerFaceIds 0) <
      centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state

namespace CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt

/-! ## 2. Constructive recoding into the indexed local step -/

/-- The code-located index of the literal lowered state. -/
def lowerIndex
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hnonzero : state ≠ 0) : Nat :=
  centralPhysicalFiniteIndexOfState w hw K 0
    (step.lowerState state hstate hnonzero)

theorem lowerIndex_mem_vacuumSector
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hnonzero : state ≠ 0) :
    step.lowerIndex state hstate hnonzero ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  let lower := step.lowerState state hstate hnonzero
  have hlowerPositive : lower ∈ centralPositiveHalfStates w hw K 0 :=
    step.lowerState_mem_positive state hstate hnonzero
  have hlowerSector : lower ∈
      centralPhysicalFiniteVacuumSectorStates w hw K 0 :=
    step.lowerState_mem_vacuumSector state hstate hnonzero
  unfold centralPhysicalFiniteVacuumSectorStates at hlowerSector
  obtain ⟨prior, hpriorSector, hpriorState⟩ :=
    List.mem_map.mp hlowerSector
  have hlocatedLt : step.lowerIndex state hstate hnonzero <
      centralPhysicalFiniteCarrierSize w hw K 0 := by
    exact centralPhysicalFiniteIndexOfState_lt hlowerPositive
  have hpriorLt : prior < centralPhysicalFiniteCarrierSize w hw K 0 :=
    centralPhysicalFiniteVacuumSectorIndex_lt w hw K 0 hpriorSector
  have hlocatedState :
      centralPhysicalFiniteStateAt w hw K 0
          (step.lowerIndex state hstate hnonzero) = lower := by
    exact centralPhysicalFiniteStateAt_indexOfState_eq hlowerPositive
  have hindexEq : step.lowerIndex state hstate hnonzero = prior :=
    centralPhysicalFiniteStateAt_injective_of_lt
      hlocatedLt hpriorLt (hlocatedState.trans hpriorState.symm)
  rw [hindexEq]
  exact hpriorSector

theorem lowerIndex_stateAt
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hnonzero : state ≠ 0) :
    centralPhysicalFiniteStateAt w hw K 0
        (step.lowerIndex state hstate hnonzero) =
      step.lowerState state hstate hnonzero :=
  centralPhysicalFiniteStateAt_indexOfState_eq
    (step.lowerState_mem_positive state hstate hnonzero)

/-- Literal state-level lowering compiles to the indexed local-step producer
without choice or propositional witness extraction. -/
def toPositiveMassDescendingRootStepAt
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
        w hw K) :
    CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
      w hw K where
  next := step.lowerIndex
  next_mem := step.lowerIndex_mem_vacuumSector
  kernel_pos := by
    intro state hstate hnonzero
    unfold centralPhysicalFiniteKernel
    rw [step.lowerIndex_stateAt state hstate hnonzero]
    exact step.kernel_pos state hstate hnonzero
  physicalMass_lt := by
    intro state hstate hnonzero
    unfold centralPhysicalFiniteVacuumSectorStatePhysicalMass
      centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
    rw [step.lowerIndex_stateAt state hstate hnonzero]
    exact step.physicalMass_lt state hstate hnonzero

/-- End-to-end cutoff compiler from literal state lowering to a complete
mass-descending root routing. -/
def toPhysicalMassDescendingRootRoutingAt
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
        w hw K) :
    CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt
      w hw K :=
  step.toPositiveMassDescendingRootStepAt
    |>.toPhysicalMassDescendingRootRoutingAt

end CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt

/-! ## 3. Cofinal compiler -/

structure FixedNomeCofinalVacuumSectorPhysicalStateMassDescendingRootStep
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  stepAt : ∀ K, start ≤ K →
    CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt
      w (Q'.le_of_lt hw) K

namespace FixedNomeCofinalVacuumSectorPhysicalStateMassDescendingRootStep

def toPositiveMassDescendingRootStep
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorPhysicalStateMassDescendingRootStep hw) :
    FixedNomeCofinalVacuumSectorPositiveMassDescendingRootStep hw where
  start := family.start
  stepAt := fun K hK =>
    (family.stepAt K hK).toPositiveMassDescendingRootStepAt

def toPhysicalMassDescendingRootRouting
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorPhysicalStateMassDescendingRootStep hw) :
    FixedNomeCofinalVacuumSectorPhysicalMassDescendingRootRouting hw :=
  family.toPositiveMassDescendingRootStep
    |>.toPhysicalMassDescendingRootRouting

end FixedNomeCofinalVacuumSectorPhysicalStateMassDescendingRootStep

end YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler.CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt.lowerIndex_mem_vacuumSector
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler.CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt.toPositiveMassDescendingRootStepAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler.CentralPhysicalFiniteVacuumSectorPhysicalStateMassDescendingRootStepAt.toPhysicalMassDescendingRootRoutingAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalStateMassDescendingStepCompiler.FixedNomeCofinalVacuumSectorPhysicalStateMassDescendingRootStep.toPhysicalMassDescendingRootRouting
