/-
# Cofinal load target for the normalized central-face BF4 routing

The normalized positive central-face routing is now literal at every positive
cutoff, vertex-simple, root-terminal through one of exactly `K` excited spin
cubes, and connected to the generic exact resistance-flow formalism.  What it
still lacks is quantitative: a cutoff-independent bound on the users of every
directed edge and on each user's exact multiplicity-aware resistance load.

This module packages precisely those two producer obligations for this exact
routing.  It compiles them into the existing generic bounded-sharing theorem
and then into the simple cofinal resistance-congestion interface consumed by
the finite all-vector gap chain.  The exact `K`-bin carrier also yields the
corresponding necessary sector-cardinality inequality.

No inhabitant of the new cofinal structure is asserted.  In particular this
module proves no cutoff-uniform load bound, unconditional cofinal finite gap,
physical scaling theorem, continuum construction, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment

/-! ## 1. The two exact quantitative producer obligations -/

/-- A cofinal bounded-sharing and per-user-load certificate specialized to
the normalized positive central-face routing. -/
structure FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad
    {w : Q'} (hw : (0 : Q') < w) : Type where
  start : Nat
  start_positive : 1 ≤ start
  sharingBound : Q'
  stateEdgeLoadBound : Q'
  sharingBound_nonnegative : (0 : Q') ≤ sharingBound
  stateEdgeLoadBound_nonnegative : (0 : Q') ≤ stateEdgeLoadBound
  edgeUsers_cardinality_le : ∀ K, (hK : start ≤ K) →
    ∀ source target,
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
            (simplePositiveCentralFaceRouting hw K
              (Nat.le_trans start_positive hK))
            source target).length ≤
        sharingBound
  stateEdgeLoad_le : ∀ K, (hK : start ≤ K) →
    ∀ source target state,
      state ∈ centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
          (simplePositiveCentralFaceRouting hw K
            (Nat.le_trans start_positive hK))
          source target →
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
            (simplePositiveCentralFaceRouting hw K
              (Nat.le_trans start_positive hK))
            state source target ≤
          stateEdgeLoadBound

namespace FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad

/-! ## 2. Compilation into the generic exact flow bound -/

def toBoundedSharing
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad hw) :
    FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
      hw where
  start := family.start
  sharingBound := family.sharingBound
  stateEdgeLoadBound := family.stateEdgeLoadBound
  sharingBound_nonnegative := family.sharingBound_nonnegative
  stateEdgeLoadBound_nonnegative := family.stateEdgeLoadBound_nonnegative
  routing := fun K hK =>
    simplePositiveCentralFaceRouting hw K
      (Nat.le_trans family.start_positive hK)
  edgeUsers_cardinality_le := family.edgeUsers_cardinality_le
  stateEdgeLoad_le := family.stateEdgeLoad_le

/-- The specialized producer is sufficient for the exact simple cofinal
resistance-congestion interface used downstream. -/
def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw where
  start := family.start
  bound := family.sharingBound * family.stateEdgeLoadBound
  bound_nonnegative := Q'.mul_nonneg _ _
    family.sharingBound_nonnegative family.stateEdgeLoadBound_nonnegative
  routing := fun K hK =>
    simplePositiveCentralFaceRouting hw K
      (Nat.le_trans family.start_positive hK)
  path_vertices_nodup := by
    intro K hK left right hleft hright
    exact simplePositiveCentralFaceRouting_path_vertices_nodup
      hw (Nat.le_trans family.start_positive hK)
      left right hleft hright
  flowLoad_le := by
    intro K hK source target
    exact family.toBoundedSharing.flowLoad_le_product
      K hK source target

theorem flowLoad_le_product
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (simplePositiveCentralFaceRouting hw K
          (Nat.le_trans family.start_positive hK))
        source target ≤
      family.sharingBound * family.stateEdgeLoadBound :=
  family.toBoundedSharing.flowLoad_le_product K hK source target

/-! ## 3. Exact terminal consequences for this routing -/

/-- The complete non-vacuum carrier must fit through `K` excited terminal
spokes at the compiled common congestion bound. -/
theorem nonzero_cardinality_le_cutoff_mul_loadBound
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad hw)
    (K : Nat) (hK : family.start ≤ K) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K).length ≤
      Q'.ofNat K *
        (family.sharingBound * family.stateEdgeLoadBound) := by
  have hused :=
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.nonzero_cardinality_le_usedTerminalSources_mul_bound
      family.toSimpleRootResistanceCongestionBound K hK
  have hlength :=
    simplePositiveCentralFaceRouting_usedTerminalSources_length_le_cutoff
      hw (Nat.le_trans family.start_positive hK)
  exact Q'.le_trans' _ _ _ hused
    (Q'.mul_le_mul_of_nonneg_right _ _
      (family.sharingBound * family.stateEdgeLoadBound)
      (Q'.ofNat_le_ofNat hlength)
      (Q'.mul_nonneg _ _ family.sharingBound_nonnegative
        family.stateEdgeLoadBound_nonnegative))

/-- The same compiled bound controls the exact stationary-mass-weighted
inverse-kernel demand of every positive terminal spoke. -/
theorem terminalFiberResistanceDemand_le_loadBound
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad hw)
    (K : Nat) (hK : family.start ≤ K) (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        (simplePositiveCentralFaceRouting hw K
          (Nat.le_trans family.start_positive hK))
        source hpositive ≤
      family.sharingBound * family.stateEdgeLoadBound :=
  FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.terminalFiberResistanceDemand_le_bound
    family.toSimpleRootResistanceCongestionBound K hK source hpositive

end FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget.FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad.toSimpleRootResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget.FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad.flowLoad_le_product
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget.FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad.nonzero_cardinality_le_cutoff_mul_loadBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget.FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad.terminalFiberResistanceDemand_le_loadBound
