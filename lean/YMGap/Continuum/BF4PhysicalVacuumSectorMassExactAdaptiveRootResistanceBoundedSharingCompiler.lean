/-
# Bounded-sharing compiler for adaptive exact-mass BF4 root routing

For an arbitrary supplied positive root routing, the exact resistance flow on
one directed edge is the sum of the multiplicity-aware edge loads of its
literal user states.  Therefore a uniform bound on user cardinality times a
uniform bound on each user's exact edge load gives a uniform adaptive
resistance-congestion certificate.

This is the route-parametric companion to the canonical off-ray
bounded-sharing compiler.  Repeated edge traversals are retained inside the
per-user edge load, so no simplicity assumption is hidden.  The resulting
adaptive certificate can be loop-erased at no extra cost by the existing
compiler.  Neither uniform producer is constructed here, and no continuum or
Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceBoundedSharingCompiler
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Route-parametric sharing and exact per-edge load -/

/-- A supplied cofinal routing with uniform rational ceilings on the literal
users of every directed edge and on each user's exact multiplicity-aware edge
load. -/
structure FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  sharingBound : Q'
  stateEdgeLoadBound : Q'
  sharingBound_nonnegative : (0 : Q') ≤ sharingBound
  stateEdgeLoadBound_nonnegative : (0 : Q') ≤ stateEdgeLoadBound
  routing : ∀ K, start ≤ K →
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  edgeUsers_cardinality_le : ∀ K, (hK : start ≤ K) →
    ∀ source target,
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
          (routing K hK) source target).length ≤
      sharingBound
  stateEdgeLoad_le : ∀ K, (hK : start ≤ K) →
    ∀ source target state,
    state ∈ centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
        (routing K hK) source target →
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        (routing K hK) state source target ≤
      stateEdgeLoadBound

namespace FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad

/-! ## 2. Exact adaptive flow bound -/

theorem flowLoad_le_product
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
        hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (family.routing K hK) source target ≤
      family.sharingBound * family.stateEdgeLoadBound := by
  let routing := family.routing K hK
  let states := centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
    routing source target
  let value := fun state =>
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
      routing state source target
  have hflow :
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
          routing source target ≤
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
          routing source target :=
    Q'.le_of_eqv
      (centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_edgeTail
        routing source target)
  have hsum : listQSum value states ≤
      Q'.ofNat states.length * family.stateEdgeLoadBound := by
    apply listQSum_le_length_mul_of_bound
      value family.stateEdgeLoadBound_nonnegative states
    intro state hstate
    exact family.stateEdgeLoad_le K hK source target state hstate
  have hcardinality : Q'.ofNat states.length ≤ family.sharingBound :=
    family.edgeUsers_cardinality_le K hK source target
  have hscaled : Q'.ofNat states.length * family.stateEdgeLoadBound ≤
      family.sharingBound * family.stateEdgeLoadBound :=
    Q'.mul_le_mul_of_nonneg_right _ _ family.stateEdgeLoadBound
      hcardinality family.stateEdgeLoadBound_nonnegative
  refine Q'.le_trans' _
    (centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
      routing source target) _ hflow ?_
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceEdgeTail
  exact Q'.le_trans' _ _ _ hsum hscaled

/-! ## 3. Existing adaptive and simple consumers -/

def toAdaptiveResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
        hw) :
    FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound
      hw where
  start := family.start
  bound := family.sharingBound * family.stateEdgeLoadBound
  bound_nonnegative := Q'.mul_nonneg _ _
    family.sharingBound_nonnegative family.stateEdgeLoadBound_nonnegative
  routing := family.routing
  flowLoad_le := family.flowLoad_le_product

/-- Loop erasure turns the compiled adaptive certificate into the exact
simple-routing consumer without increasing its bound. -/
def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad
        hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting.FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceCongestionBound.toSimple
    family.toAdaptiveResistanceCongestionBound

end FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler.FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad.flowLoad_le_product
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler.FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad.toAdaptiveResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingCompiler.FixedNomeCofinalVacuumSectorMassExactAdaptiveRootResistanceBoundedSharingEdgeLoad.toSimpleRootResistanceCongestionBound
