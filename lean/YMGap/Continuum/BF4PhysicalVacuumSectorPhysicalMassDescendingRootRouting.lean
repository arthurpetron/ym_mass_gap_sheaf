/-
# Physical-mass-descending root routing for the finite BF4 vacuum sector

This module isolates the constructive combinatorics required of a
mass-monotone adaptive root route.  A positive path is strictly descending
when the literal lower-half twice-spin mass decreases across every directed
edge.  Such a path is automatically vertex-simple and its edge length is at
most its initial mass.

The cutoff-level and cofinal structures record actual positive BF4 routing
data together with this edgewise mass descent.  No such routing is inhabited
here.  In particular, the accepted paired-peeling process already has a
strict mass measure, but a separate theorem must still realize each peel as a
positive edge of this finite BF4 kernel.  No congestion, continuum, or Clay
conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Generic strict descent on an actual positive-kernel path -/

/-- Every literal directed edge of the supplied path strictly decreases the
chosen natural-number measure. -/
def positiveKernelChainStrictlyDecreases
    {State : Type} (measure : State → Nat)
    {kernel : State → State → Q'} {support : List State}
    {first last : State}
    (path : PositiveKernelChainIn kernel support first last) : Prop :=
  ∀ edge, edge ∈ PositiveKernelChainIn.directedEdges path →
    measure edge.2 < measure edge.1

theorem positiveKernelChainStrictlyDecreases_vertices_measure_le_start
    {State : Type} (measure : State → Nat)
    {kernel : State → State → Q'} {support : List State} :
    ∀ {first last : State}
      (path : PositiveKernelChainIn kernel support first last),
      positiveKernelChainStrictlyDecreases measure path →
      ∀ state, state ∈ PositiveKernelChainIn.vertices path →
        measure state ≤ measure first
  | _, _, PositiveKernelChainIn.refl first, _hdescending,
      state, hstate => by
      rw [List.mem_singleton.mp hstate]
      exact Nat.le_refl _
  | first, _last,
      PositiveKernelChainIn.step (next := next) _positive _nextMem rest,
      hdescending, state, hstate => by
      rcases List.mem_cons.mp hstate with hfirst | hrest
      · rw [hfirst]
        exact Nat.le_refl _
      · have hstep : measure next < measure first :=
          hdescending (first, next) List.mem_cons_self
        have htail : positiveKernelChainStrictlyDecreases measure rest := by
          intro edge hedge
          exact hdescending edge (List.mem_cons_of_mem (first, next) hedge)
        exact Nat.le_trans
          (positiveKernelChainStrictlyDecreases_vertices_measure_le_start
            measure rest htail state hrest)
          (Nat.le_of_lt hstep)

/-- Strict descent rules out every repeated vertex constructively. -/
theorem positiveKernelChainStrictlyDecreases_vertices_nodup
    {State : Type} (measure : State → Nat)
    {kernel : State → State → Q'} {support : List State} :
    ∀ {first last : State}
      (path : PositiveKernelChainIn kernel support first last),
      positiveKernelChainStrictlyDecreases measure path →
      (PositiveKernelChainIn.vertices path).Nodup
  | _, _, PositiveKernelChainIn.refl _, _ =>
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | first, _last,
      PositiveKernelChainIn.step (next := next) _positive _nextMem rest,
      hdescending => by
      have hstep : measure next < measure first :=
        hdescending (first, next) List.mem_cons_self
      have htail : positiveKernelChainStrictlyDecreases measure rest := by
        intro edge hedge
        exact hdescending edge (List.mem_cons_of_mem (first, next) hedge)
      apply List.nodup_cons.mpr
      constructor
      · intro hfirst
        have hle : measure first ≤ measure next :=
          positiveKernelChainStrictlyDecreases_vertices_measure_le_start
            measure rest htail first hfirst
        exact (Nat.not_le_of_lt hstep) hle
      · exact positiveKernelChainStrictlyDecreases_vertices_nodup
          measure rest htail

/-- Every strict natural-number drop pays for one path edge. -/
theorem positiveKernelChainStrictlyDecreases_edgeLength_le_measure
    {State : Type} (measure : State → Nat)
    {kernel : State → State → Q'} {support : List State} :
    ∀ {first last : State}
      (path : PositiveKernelChainIn kernel support first last),
      positiveKernelChainStrictlyDecreases measure path →
      PositiveKernelChainIn.edgeLength path ≤ measure first
  | _, _, PositiveKernelChainIn.refl _, _ => Nat.zero_le _
  | first, _last,
      PositiveKernelChainIn.step (next := next) _positive _nextMem rest,
      hdescending => by
      have hstep : measure next < measure first :=
        hdescending (first, next) List.mem_cons_self
      have htail : positiveKernelChainStrictlyDecreases measure rest := by
        intro edge hedge
        exact hdescending edge (List.mem_cons_of_mem (first, next) hedge)
      have ih := positiveKernelChainStrictlyDecreases_edgeLength_le_measure
        measure rest htail
      simp only [PositiveKernelChainIn.edgeLength]
      omega

/-! ## 2. Literal lower-half twice-spin mass on the full sector -/

/-- The same physical source mass used by the off-ray shell compiler, now
named without an off-ray restriction because it is defined on every finite
sector index. -/
def centralPhysicalFiniteVacuumSectorStatePhysicalMass
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) : Nat :=
  centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass w hw K state

theorem centralPhysicalFiniteVacuumSectorStatePhysicalMass_eq_offRayRootStatePhysicalMass
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state =
      centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
        w hw K state :=
  rfl

/-! ## 3. Cutoff-level mass-descending root routing -/

structure CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type 1 where
  routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K
  rootPath_strictlyDecreases : ∀ state
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0),
    positiveKernelChainStrictlyDecreases
      (centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K)
      (routing.path state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))

namespace CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt

theorem rootPath_vertices_nodup
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (route :
      CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (PositiveKernelChainIn.vertices
      (route.routing.path state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))).Nodup :=
  positiveKernelChainStrictlyDecreases_vertices_nodup
    (centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K)
    _ (route.rootPath_strictlyDecreases state hstate)

theorem rootPath_edgeLength_le_physicalMass
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (route :
      CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt
        w hw K)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    PositiveKernelChainIn.edgeLength
        (route.routing.path state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)) ≤
      centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K state :=
  positiveKernelChainStrictlyDecreases_edgeLength_le_measure
    (centralPhysicalFiniteVacuumSectorStatePhysicalMass w hw K)
    _ (route.rootPath_strictlyDecreases state hstate)

end CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt

/-! ## 4. The cofinal route-design target, without a hidden load bound -/

structure FixedNomeCofinalVacuumSectorPhysicalMassDescendingRootRouting
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  routingAt : ∀ K, start ≤ K →
    CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt
      w (Q'.le_of_lt hw) K

namespace FixedNomeCofinalVacuumSectorPhysicalMassDescendingRootRouting

theorem rootPath_edgeLength_le_physicalMass
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalVacuumSectorPhysicalMassDescendingRootRouting hw)
    (K : Nat) (hK : family.start ≤ K)
    (state : Nat)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    PositiveKernelChainIn.edgeLength
        ((family.routingAt K hK).routing.path state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K 0)) ≤
      centralPhysicalFiniteVacuumSectorStatePhysicalMass
        w (Q'.le_of_lt hw) K state :=
  (family.routingAt K hK).rootPath_edgeLength_le_physicalMass state hstate

end FixedNomeCofinalVacuumSectorPhysicalMassDescendingRootRouting

end YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting.positiveKernelChainStrictlyDecreases_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting.positiveKernelChainStrictlyDecreases_edgeLength_le_measure
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting.CentralPhysicalFiniteVacuumSectorPhysicalMassDescendingRootRoutingAt.rootPath_vertices_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPhysicalMassDescendingRootRouting.FixedNomeCofinalVacuumSectorPhysicalMassDescendingRootRouting.rootPath_edgeLength_le_physicalMass
