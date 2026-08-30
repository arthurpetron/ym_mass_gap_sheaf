/-
# The guarded receiver recovers its peeled terminal at every cutoff

Terminal recovery is a semantic property of the four grafted fields: the two
physical labellings and the two accepted auxiliary assignments.  The original
theorem packaged those fields only at cutoff one.  The ambient-cutoff graft
uses the same fields with different membership proofs, so equality of two such
accepted grafts recovers equality of their peeled terminals for every cutoff
at least one.

Constructive contract: equality of accepted-state projections and the
componentwise terminal-recovery theorem only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverability

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverabilityCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverability

/-- Equality of the ambient-cutoff accepted grafts recovers equality of the
canonical guard-cleared terminals.  No equality with cutoff one is needed. -/
theorem reflectedBentGuardCanonicalPeeling_terminal_eq_of_graftOfOneLE_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedStateOfOneLE
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedStateOfOneLE
        D hcutoff hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1 := by
  have hleftSource := congrArg (fun state => state.1.1) hgraft
  change (reflectedBentGuardGraftAcceptedStateOfOneLE
      D hcutoff hextent left).1.1 =
    (reflectedBentGuardGraftAcceptedStateOfOneLE
      D hcutoff hextent right).1.1 at hleftSource
  rw [reflectedBentGuardGraftAcceptedStateOfOneLE_leftSource,
    reflectedBentGuardGraftAcceptedStateOfOneLE_leftSource] at hleftSource
  have hleft :
      reflectedBentGuardGraftLeftPhysical D hextent left =
          reflectedBentGuardGraftLeftPhysical D hextent right ∧
        reflectedBentGuardGraftLeftAssignment D hextent left =
          reflectedBentGuardGraftLeftAssignment D hextent right := by
    simpa only [Prod.mk.injEq] using hleftSource
  have hrightSource := congrArg (fun state => state.2.1) hgraft
  change (reflectedBentGuardGraftAcceptedStateOfOneLE
      D hcutoff hextent left).2.1 =
    (reflectedBentGuardGraftAcceptedStateOfOneLE
      D hcutoff hextent right).2.1 at hrightSource
  rw [reflectedBentGuardGraftAcceptedStateOfOneLE_rightSource,
    reflectedBentGuardGraftAcceptedStateOfOneLE_rightSource] at hrightSource
  have hright :
      reflectedBentGuardGraftRightPhysical D hextent left =
          reflectedBentGuardGraftRightPhysical D hextent right ∧
        reflectedBentGuardGraftRightAssignment D hextent left =
          reflectedBentGuardGraftRightAssignment D hextent right := by
    simpa only [Prod.mk.injEq] using hrightSource
  exact reflectedBentGuardCanonicalPeeling_terminal_eq_of_graftComponents_eq
    D hextent left right hleft.1 hleft.2 hright.1 hright.2

#print axioms reflectedBentGuardCanonicalPeeling_terminal_eq_of_graftOfOneLE_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverabilityCutoffPersistence
