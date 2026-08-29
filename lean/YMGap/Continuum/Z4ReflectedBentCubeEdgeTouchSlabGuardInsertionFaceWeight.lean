/-
# Exact heat-face cost of the reflected guarded insertion

The canonical guard peeling clears the terminal on every positive face of the
reflected-bent pattern.  The general cleared-support factorization therefore
identifies the grafted left heat product with the isolated pattern factor times
the terminal left factor.  The right graft is literally the terminal and has
no insertion cost.

This is the exact analytic identity needed before a receiver-weight floor can
be stated.  It keeps the coupling and cutoff visible; no beta-uniformity is
claimed.

Constructive contract: specialization of exact finite-product identities only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabPhysicalInsertionFactorization
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionFaceWeight

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPhysicalInsertionFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

local infix:50 " ≈ " => Q'.eqv

/-- The peeled terminal left field vanishes wherever the inserted pattern is
positive. -/
theorem reflectedBentGuardCanonicalTerminalLeft_zero_on_pattern
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hphysical : faceId ∈ slabPhysicalFaceEdges D.extent)
    (hpositive : 0 < reflectedBentSwitchLeftPhysical faceId) :
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 faceId = 0 := by
  have hphysicalFive : faceId ∈ slabPhysicalFaceEdges 5 := by
    simpa only [hextent] using hphysical
  have hpattern : faceId ∈ reflectedBentPatternFaceIds :=
    (mem_reflectedBentPatternFaceIds_iff hphysicalFive).mpr hpositive
  exact (reflectedBentGuardCanonicalPeeling_final_zero
    D hextent state faceId
      (reflectedBentPatternFace_mem_guard hpattern)).1

/-- Exact coupling-visible heat-face factorization of the grafted left
replica. -/
theorem reflectedBentGuardGraftLeftPhysicalFaceFactor_eqv
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
        (reflectedBentGuardGraftLeftPhysical D hextent state) ≈
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          reflectedBentSwitchLeftPhysical *
        slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          (reflectedBentGuardCanonicalPeeling
            D hextent state).1.1.1.1 := by
  simpa only [reflectedBentGuardGraftLeftPhysical, positiveSupportInsert] using
    (slabParametricKPhysicalFaceFactor_positiveSupportInsert_eqv_mul
      D.coupling D.cutoff D.extent reflectedBentSwitchLeftPhysical
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
      (reflectedBentGuardCanonicalTerminalLeft_zero_on_pattern
        D hextent state))

/-- The right physical field is retained literally, so its heat-face factor is
unchanged. -/
theorem reflectedBentGuardGraftRightPhysicalFaceFactor_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
        (reflectedBentGuardGraftRightPhysical D hextent state) =
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
        (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 :=
  rfl

#print axioms reflectedBentGuardCanonicalTerminalLeft_zero_on_pattern
#print axioms reflectedBentGuardGraftLeftPhysicalFaceFactor_eqv
#print axioms reflectedBentGuardGraftRightPhysicalFaceFactor_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionFaceWeight
