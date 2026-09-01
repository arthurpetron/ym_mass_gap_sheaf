/-
# Compile spin-cube terminal prefixes into BF4 root routing

The exact vacuum-root classifier leaves one concrete routing interface.  For
each non-vacuum state, a producer chooses an admitted spin and a positive path
from that state to the corresponding uniform central spin cube.  Appending
the certified one-edge spin-cube-to-vacuum spoke gives a positive root path
whose terminal source and decoded terminal spin are exactly the producer's
choice.

This module implements that compiler and extends the selected root paths to a
complete positive routing by using the canonical connectivity path away from
the root.  It does not construct a balanced prefix assignment, prove a
cutoff-uniform edge load, or assert a spectral, continuum, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler
import YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment

namespace YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassAmortizedMacroStepCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeTerminalAssignment
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

/-! ## 1. Generic concatenation facts -/

theorem positiveKernelChain_directedEdges_trans
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first middle last : State}
      (left : PositiveKernelChainIn kernel support first middle)
      (right : PositiveKernelChainIn kernel support middle last),
      PositiveKernelChainIn.directedEdges (left.trans right) =
        PositiveKernelChainIn.directedEdges left ++
          PositiveKernelChainIn.directedEdges right
  | _, _, _, PositiveKernelChainIn.refl _, _ => rfl
  | _, _, _, PositiveKernelChainIn.step _ _ rest, right => by
      simp only [PositiveKernelChainIn.trans,
        PositiveKernelChainIn.directedEdges, List.cons_append]
      exact congrArg (List.cons _)
        (positiveKernelChain_directedEdges_trans rest right)

/-- Concatenating any prefix with a literal final edge makes the source of
that edge the terminal source of the composite path. -/
theorem positiveKernelChain_terminalSource_trans_single
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first middle last : State}
      (leftPath : PositiveKernelChainIn kernel support first middle)
      (positive : (0 : Q') < kernel middle last)
      (last_mem : last ∈ support),
      PositiveKernelChainIn.terminalSource
          (leftPath.trans
            (PositiveKernelChainIn.step positive last_mem
              (PositiveKernelChainIn.refl last))) = middle
  | _, _, _, PositiveKernelChainIn.refl _, _, _ => rfl
  | _, _, _, PositiveKernelChainIn.step _ _ rest, positive, last_mem => by
      cases rest with
      | refl => rfl
      | step next_positive after_next_mem tail =>
          simp only [PositiveKernelChainIn.trans,
            PositiveKernelChainIn.terminalSource]
          exact positiveKernelChain_terminalSource_trans_single
            (PositiveKernelChainIn.step
              next_positive after_next_mem tail)
            positive last_mem

/-! ## 2. The classified terminal-prefix producer interface -/

/-- The positive path type from a finite-sector state to one selected
spin-cube root predecessor.  Keeping this repeated dependent type behind an
opaque name prevents the kernel normalizer from being unfolded while the
producer structure itself is elaborated. -/
def CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefix
    (w : Q') (hw : (0 : Q') < w) (K state spin : Nat) : Type :=
  PositiveKernelChainIn
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
    (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
    state
    (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin)

structure CentralPhysicalFiniteVacuumSectorAdmittedTerminalSpin
    (K : Nat) : Type where
  spin : Nat
  spin_le : spin ≤ K

/-- A proof-independent spin choice together with its admitted-range proof and
positive prefix family.  The unresolved constructive task is to inhabit this
interface with enough sharing and resistance control uniformly in `K`. -/
def CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
    (w : Q') (hw : (0 : Q') < w) (K : Nat) : Type :=
  ∀ state : Nat,
    Σ choice : CentralPhysicalFiniteVacuumSectorAdmittedTerminalSpin K,
      ∀ (_hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0),
        (_hne : state ≠ 0) →
        CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefix
          w hw K state choice.spin

namespace CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt

def terminalSpin {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (state : Nat) : Nat :=
  (assignment state).1.spin

theorem terminalSpin_le {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (state : Nat)
    (_hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (_hne : state ≠ 0) :
    assignment.terminalSpin state ≤ K :=
  (assignment state).1.spin_le

def prefixPath {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (state : Nat)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefix
      w hw K state (assignment.terminalSpin state) :=
  (assignment state).2 hstate hne

/-- Append the selected certified vacuum spoke to a producer's prefix. -/
def rootPath {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (state : Nat)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw) K 0)
      state 0 :=
  PositiveKernelChainIn.trans
    (assignment.prefixPath state hstate hne)
    (centralLowerSpinCubeToVacuumSpoke hw
      (assignment.terminalSpin_le state hstate hne))

theorem rootPath_edgeLength
    {w : Q'} {hw : (0 : Q') < w} {K state : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    PositiveKernelChainIn.edgeLength
        (assignment.rootPath state hstate hne) =
      PositiveKernelChainIn.edgeLength
          (assignment.prefixPath state hstate hne) + 1 := by
  unfold rootPath
  rw [positiveKernelChain_edgeLength_trans]
  rfl

theorem rootPath_directedEdges
    {w : Q'} {hw : (0 : Q') < w} {K state : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    PositiveKernelChainIn.directedEdges
        (assignment.rootPath state hstate hne) =
      PositiveKernelChainIn.directedEdges
          (assignment.prefixPath state hstate hne) ++
        [(centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
            (assignment.terminalSpin state), 0)] := by
  unfold rootPath
  rw [positiveKernelChain_directedEdges_trans]
  rfl

theorem rootPath_terminalSource
    {w : Q'} {hw : (0 : Q') < w} {K state : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    PositiveKernelChainIn.terminalSource
        (assignment.rootPath state hstate hne) =
      centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
        (assignment.terminalSpin state) := by
  unfold rootPath centralLowerSpinCubeToVacuumSpoke
  exact positiveKernelChain_terminalSource_trans_single
    (assignment.prefixPath state hstate hne)
    (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw
      (assignment.terminalSpin_le state hstate hne))
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)

/-! ## 3. Complete routing and exact recovery of the selected label -/

/-- Use the selected root path when the destination is the vacuum; use the
canonical positive connectivity path for all other ordered pairs. -/
def toPositiveRouting
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K where
  path := fun left right hleft hright =>
    if hrightZero : right = 0 then
      if hleftZero : left = 0 then by
        subst left
        subst right
        exact PositiveKernelChainIn.refl 0
      else by
        subst right
        exact assignment.rootPath left hleft hleftZero
    else
      centralPhysicalFiniteVacuumSector_positiveKernelConnected
        w (Q'.le_of_lt hw) K 0 left right hleft hright

theorem toPositiveRouting_rootPath
    {w : Q'} {hw : (0 : Q') < w} {K state : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    (assignment.toPositiveRouting.path state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)) =
      assignment.rootPath state hstate hne := by
  unfold toPositiveRouting
  simp [hne]

/-- The compiled route's literal final source is exactly the selected
spin-cube index. -/
theorem toPositiveRouting_terminalSource
    {w : Q'} {hw : (0 : Q') < w} {K state : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
        assignment.toPositiveRouting state hstate =
      centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
        (assignment.terminalSpin state) := by
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSource
  rw [assignment.toPositiveRouting_rootPath hstate hne]
  exact assignment.rootPath_terminalSource hstate hne

/-- The generic terminal decoder recovers the producer's selected spin
without loss. -/
theorem toPositiveRouting_terminalSpin
    {w : Q'} {hw : (0 : Q') < w} {K state : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
        assignment.toPositiveRouting state hstate =
      assignment.terminalSpin state := by
  unfold centralPhysicalFiniteVacuumSectorSimpleRootTerminalSpin
  rw [assignment.toPositiveRouting_terminalSource hstate hne,
    centralPhysicalFiniteStateAt_spinCubeIndex_eq hw
      (assignment.terminalSpin_le state hstate hne)]
  exact centralLowerSpinCubeState_eq_spin_on_cube
    (assignment.terminalSpin state) (by decide)

end CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt

end YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler.positiveKernelChain_terminalSource_trans_single
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler.CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.rootPath_edgeLength
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler.CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.rootPath_directedEdges
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler.CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.toPositiveRouting_terminalSource
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler.CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.toPositiveRouting_terminalSpin
