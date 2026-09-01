/-
# Compile mass-amortized positive BF4 macro-steps into root routing

Strict physical-mass descent on every individual positive-kernel edge is
already obstructed at cutoff two.  The quantitative consequence that the
routing branch actually needs is weaker: the complete root path should have
length at most its source mass.  This module isolates a local producer that
retains that consequence while allowing temporary mass increase.

For every non-root state, the producer chooses a lower-mass endpoint and an
actual positive-kernel path to it.  The displayed macro-path length must be at
most the endpoint physical-mass drop.  Well-founded recursion concatenates
those macro-steps.  Exact additivity of edge length makes the drop budgets
 telescope, so the resulting root path still has length at most source mass.

No macro-step producer is inhabited here.  No sharing, resistance-load,
continuum, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting

/-! ## 1. Edge length is additive under path concatenation -/

theorem positiveKernelChain_edgeLength_trans
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first middle last : State}
      (left : PositiveKernelChainIn kernel support first middle)
      (right : PositiveKernelChainIn kernel support middle last),
      PositiveKernelChainIn.edgeLength (left.trans right) =
        PositiveKernelChainIn.edgeLength left +
          PositiveKernelChainIn.edgeLength right
  | _, _, _, PositiveKernelChainIn.refl _, right => by
      simp only [PositiveKernelChainIn.trans,
        PositiveKernelChainIn.edgeLength, Nat.zero_add]
  | _, _, _, PositiveKernelChainIn.step _ _ rest, right => by
      simp only [PositiveKernelChainIn.trans,
        PositiveKernelChainIn.edgeLength]
      rw [positiveKernelChain_edgeLength_trans rest right]
      omega

/-! ## 2. Cutoff-level routing target and local producer -/

/-- A complete finite-sector routing whose root paths retain the physical-mass
length budget, without requiring mass descent on each internal edge. -/
structure CentralPhysicalFiniteVacuumSectorPhysicalMassAmortizedRootRoutingAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type 1 where
  routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K
  rootPath_edgeLength_le_physicalMass : ∀ state,
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
    PositiveKernelChainIn.edgeLength
        (routing.path state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)) ≤
      centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state

/-- A positive macro-step to a lower-mass endpoint.  Internal vertices may
increase in physical mass, but the full macro-path length is paid by the
endpoint mass drop. -/
structure CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type 1 where
  next : ∀ state,
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
    state ≠ 0 → Nat
  next_mem : ∀ state hstate hnonzero,
    next state hstate hnonzero ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0
  macroPath : ∀ state hstate hnonzero,
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      state (next state hstate hnonzero)
  physicalMass_lt : ∀ state hstate hnonzero,
    centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K
        (next state hstate hnonzero) <
      centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state
  macroPath_edgeLength_le_massDrop : ∀ state hstate hnonzero,
    PositiveKernelChainIn.edgeLength
        (macroPath state hstate hnonzero) ≤
      centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state -
        centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K
          (next state hstate hnonzero)

namespace CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt

/-! ## 3. Well-founded concatenation and telescoping length -/

/-- The recursively concatenated root path bundled with its telescoped
physical-mass length bound. -/
def rootPathWithLength
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    { path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        state 0 //
      PositiveKernelChainIn.edgeLength path ≤
        centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state } :=
  if hzero : state = 0 then by
    subst state
    exact ⟨PositiveKernelChainIn.refl 0, Nat.zero_le _⟩
  else
    let next := step.next state hstate hzero
    let hnext := step.next_mem state hstate hzero
    let head := step.macroPath state hstate hzero
    let tail := rootPathWithLength step next hnext
    let path := head.trans tail.1
    ⟨path, by
      rw [positiveKernelChain_edgeLength_trans]
      have hhead : PositiveKernelChainIn.edgeLength head ≤
          centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state -
            centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K next := by
        dsimp only [head, next]
        exact step.macroPath_edgeLength_le_massDrop state hstate hzero
      have htail := tail.2
      have hsum := Nat.add_le_add hhead htail
      have hdrop :
          centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K next <
            centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state := by
        dsimp only [next]
        exact step.physicalMass_lt state hstate hzero
      exact Nat.le_trans hsum
        (Nat.le_of_eq (Nat.sub_add_cancel (Nat.le_of_lt hdrop)))⟩
termination_by
  centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state
decreasing_by
  exact step.physicalMass_lt state hstate hzero

def rootPath
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      state 0 :=
  (step.rootPathWithLength state hstate).1

theorem rootPath_edgeLength_le_physicalMass
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    PositiveKernelChainIn.edgeLength (step.rootPath state hstate) ≤
      centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state :=
  (step.rootPathWithLength state hstate).2

/-! ## 4. Install the root paths in a complete routing -/

def positivePath
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
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

def toPhysicalMassAmortizedRootRoutingAt
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (step :
      CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
        w hw K) :
    CentralPhysicalFiniteVacuumSectorPhysicalMassAmortizedRootRoutingAt
      w hw K where
  routing := { path := step.positivePath }
  rootPath_edgeLength_le_physicalMass := by
    intro state hstate
    simpa [positivePath] using
      step.rootPath_edgeLength_le_physicalMass state hstate

end CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt

/-! ## 5. Cofinal compiler -/

structure FixedNomeCofinalVacuumSectorPhysicalMassAmortizedRootRouting
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  routingAt : ∀ K, start ≤ K →
    CentralPhysicalFiniteVacuumSectorPhysicalMassAmortizedRootRoutingAt
      w (Q'.le_of_lt hw) K

structure FixedNomeCofinalVacuumSectorPositivePhysicalMassAmortizedRootMacroStep
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  stepAt : ∀ K, start ≤ K →
    CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt
      w (Q'.le_of_lt hw) K

namespace FixedNomeCofinalVacuumSectorPositivePhysicalMassAmortizedRootMacroStep

def toPhysicalMassAmortizedRootRouting
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorPositivePhysicalMassAmortizedRootMacroStep
        hw) :
    FixedNomeCofinalVacuumSectorPhysicalMassAmortizedRootRouting hw where
  start := family.start
  routingAt := fun K hK =>
    (family.stepAt K hK).toPhysicalMassAmortizedRootRoutingAt

end FixedNomeCofinalVacuumSectorPositivePhysicalMassAmortizedRootMacroStep

end YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler.positiveKernelChain_edgeLength_trans
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler.CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt.rootPathWithLength
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler.CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt.rootPath_edgeLength_le_physicalMass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler.CentralPhysicalFiniteVacuumSectorPositivePhysicalMassAmortizedRootMacroStepAt.toPhysicalMassAmortizedRootRoutingAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler.FixedNomeCofinalVacuumSectorPositivePhysicalMassAmortizedRootMacroStep.toPhysicalMassAmortizedRootRouting
