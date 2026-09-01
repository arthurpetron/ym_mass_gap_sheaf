/-
# Compile local mass-descending BF4 steps into root routing

The paired accepted-peeling machinery and the finite BF4 routing graph do not
have the same state type: the former carries two expanded sources and fusion
assignments, while the latter carries one indexed lower-half labelling.  This
module therefore states the honest local producer directly on the BF4 graph.

At one cutoff, a producer chooses a positive-kernel successor for every
non-root vacuum-sector index and proves that literal lower-half twice-spin mass
strictly decreases.  Well-founded recursion on that mass compiles the local
steps into an actual positive path to the vacuum.  The path is installed only
for root-directed requests; the existing canonical routing continues to serve
the other endpoint pairs.  The result inhabits the previously isolated
mass-descending routing interface.

No local-step producer is inhabited here.  In particular, no map from an
accepted paired peel to a single BF4 index or positive BF4 edge is asserted.
No congestion, continuum, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting

/-! ## 1. The local positive mass-descending producer -/

/-- A positive BF4 successor of smaller literal physical mass for every
non-root index in one finite vacuum sector.  This is local step data, not an
already constructed path or a hidden congestion bound. -/
structure CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type 1 where
  next : ∀ state,
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
    state ≠ 0 → Nat
  next_mem : ∀ state hstate hnonzero,
    next state hstate hnonzero ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0
  kernel_pos : ∀ state hstate hnonzero,
    (0 : Q') < centralPhysicalFiniteKernel w hw K 0 state
      (next state hstate hnonzero)
  physicalMass_lt : ∀ state hstate hnonzero,
    centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K
        (next state hstate hnonzero) <
      centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state

namespace CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt

/-! ## 2. Well-founded compilation to a positive root path -/

/-- The positive path and its edgewise strict-descent proof are constructed
together, so the recursive witness never loses the measure invariant. -/
def rootPathWithDescent
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    { path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        state 0 //
      positiveKernelChainStrictlyDecreases
        (centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K)
        path } :=
  if hzero : state = 0 then by
    subst state
    refine ⟨PositiveKernelChainIn.refl 0, ?_⟩
    intro edge hedge
    exact False.elim (List.not_mem_nil hedge)
  else
    let next := step.next state hstate hzero
    let hnext := step.next_mem state hstate hzero
    let tail := rootPathWithDescent step next hnext
    let path := PositiveKernelChainIn.step
      (step.kernel_pos state hstate hzero) hnext tail.1
    ⟨path, by
      intro edge hedge
      change edge ∈ (state, next) ::
        PositiveKernelChainIn.directedEdges tail.1 at hedge
      rcases List.mem_cons.mp hedge with hedge | hedge
      · rw [hedge]
        exact step.physicalMass_lt state hstate hzero
      · exact tail.2 edge hedge⟩
termination_by
  centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state
decreasing_by
  exact step.physicalMass_lt state hstate hzero

/-- The path projection of the bundled recursive witness. -/
def rootPath
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      state 0 :=
  (rootPathWithDescent step state hstate).1

theorem rootPath_strictlyDecreases
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    positiveKernelChainStrictlyDecreases
      (centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K)
      (step.rootPath state hstate) :=
  (rootPathWithDescent step state hstate).2

/-! ## 3. Install the root paths in a complete routing -/

/-- Use the compiled path for a request whose right endpoint is the root, and
retain the established canonical path for every other ordered pair. -/
def positivePath
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
        w hw K)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      left right :=
  if hzero : right = 0 then
    hzero.symm ▸ step.rootPath left hleft
  else
    (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w hw K).path left right hleft hright

/-- Local positive mass-descending successors are sufficient to inhabit the
cutoff-level mass-descending root-routing target. -/
def toPhysicalMassDescendingRootRoutingAt
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
        w hw K) :
    CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt
      w hw K where
  routing := {
    path := step.positivePath
  }
  rootPath_strictlyDecreases := by
    intro state hstate
    simpa [positivePath] using step.rootPath_strictlyDecreases state hstate

end CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt

/-! ## 4. Cofinal compiler -/

/-- A cofinal family of the local producer, still without any sharing or load
bound hidden in the data. -/
structure FixedNomeCofinalVacuumSectorPositiveMassDescendingRootStep
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  stepAt : ∀ K, start ≤ K →
    CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt
      w (Q'.le_of_lt hw) K

namespace FixedNomeCofinalVacuumSectorPositiveMassDescendingRootStep

/-- Compile a cofinal local-step producer into the cofinal mass-descending
routing target. -/
def toPhysicalMassDescendingRootRouting
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorPositiveMassDescendingRootStep hw) :
    FixedNomeCofinalVacuumSectorPhysicalMassDescendingRootRouting hw where
  start := family.start
  routingAt := fun K hK =>
    (family.stepAt K hK).toPhysicalMassDescendingRootRoutingAt

end FixedNomeCofinalVacuumSectorPositiveMassDescendingRootStep

end YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler.CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt.rootPathWithDescent
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler.CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt.rootPath_strictlyDecreases
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler.CentralPhysicalFiniteVacuumSectorPositiveMassDescendingRootStepAt.toPhysicalMassDescendingRootRoutingAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingStepCompiler.FixedNomeCofinalVacuumSectorPositiveMassDescendingRootStep.toPhysicalMassDescendingRootRouting
