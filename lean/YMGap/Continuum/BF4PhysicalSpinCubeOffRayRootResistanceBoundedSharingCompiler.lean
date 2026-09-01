/-
# Bounded-sharing compiler for BF4 off-ray root resistance flow

The physical-mass pointwise-decay route is obstructed because every literal
edge user costs at least one.  A compatible replacement is to bound two
quantities uniformly: the number of selected off-ray root paths using one
directed edge and the resistance load of each such user.  Their product
bounds the exact edge tail and therefore the exact resistance flow load.

This module packages that lossless finite reduction and compiles it, together
with the already separate direct spin-ray capacity, to the full simple root
routing certificate.  It does not construct either uniform producer and does
not assert a continuum or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeSharingObstruction

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceBoundedSharingCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. The two compatible uniform producers -/

/-- Uniform literal edge sharing and a uniform per-user resistance-load
ceiling for the selected canonical off-ray root paths.  Unlike geometric
pointwise decay, the constant ceiling is compatible with the proved unit
lower bound on every actual edge user. -/
structure FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  sharingBound : Q'
  stateLoadBound : Q'
  sharingBound_nonnegative : (0 : Q') ≤ sharingBound
  stateLoadBound_nonnegative : (0 : Q') ≤ stateLoadBound
  edgeUsers_cardinality_le : ∀ K, start ≤ K → ∀ source target,
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
          w (Q'.le_of_lt hw) K source target).length ≤
      sharingBound
  stateLoad_le : ∀ K, start ≤ K → ∀ source target state,
    state ∈ centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
        w (Q'.le_of_lt hw) K source target →
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w (Q'.le_of_lt hw) K state ≤
      stateLoadBound

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad

/-! ## 2. Exact product bound on the literal flow load -/

theorem flowLoad_le_product
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K source target ≤
      family.sharingBound * family.stateLoadBound := by
  let states := centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
    w (Q'.le_of_lt hw) K source target
  let value := centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    w (Q'.le_of_lt hw) K
  have hflow :
      centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K source target ≤
        centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
          w (Q'.le_of_lt hw) K source target :=
    Q'.le_of_eqv
      (centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_edgeTail
        w (Q'.le_of_lt hw) K source target)
  have hsum : listQSum value states ≤
      Q'.ofNat states.length * family.stateLoadBound := by
    apply listQSum_le_length_mul_of_bound
      value family.stateLoadBound_nonnegative states
    intro state hstate
    exact family.stateLoad_le K hK source target state hstate
  have hcardinality : Q'.ofNat states.length ≤ family.sharingBound :=
    family.edgeUsers_cardinality_le K hK source target
  have hscaled : Q'.ofNat states.length * family.stateLoadBound ≤
      family.sharingBound * family.stateLoadBound :=
    Q'.mul_le_mul_of_nonneg_right _ _ family.stateLoadBound
      hcardinality family.stateLoadBound_nonnegative
  refine Q'.le_trans' _
    (centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
      w (Q'.le_of_lt hw) K source target) _ hflow ?_
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
  exact Q'.le_trans' _ _ _ hsum hscaled

/-! ## 3. Existing congestion and full-routing consumers -/

def toResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw where
  start := family.start
  bound := family.sharingBound * family.stateLoadBound
  bound_nonnegative := Q'.mul_nonneg _ _
    family.sharingBound_nonnegative family.stateLoadBound_nonnegative
  flowLoad_le := family.flowLoad_le_product

/-- Bounded off-ray sharing and per-user load, together with the direct-ray
capacity, construct the complete full-sector simple-routing certificate. -/
def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  fixedNomeCofinalSimpleRootResistanceCongestionBound_of_ray_offRay
    ray family.toResistanceCongestionBound

end FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceBoundedSharingCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceBoundedSharingCompiler.FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad.flowLoad_le_product
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceBoundedSharingCompiler.FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad.toResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceBoundedSharingCompiler.FixedNomeCofinalSpinCubeOffRayRootResistanceBoundedSharingLoad.toSimpleRootResistanceCongestionBound
