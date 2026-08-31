/-
# Complete provenance decoder for the reflected-bent guard switch

For guarded reflected-bent source pairs, the fixed provenance code stores the
strand-mask word and the rank of the complete active auxiliary-row table.
Equality of the final switched target and this code already recovers the two
source physical fields and active rows.  The generic active/inactive auxiliary
reconstruction theorem then recovers both complete source assignments.

Thus the final target together with one code in the fixed, cutoff-independent
provenance carrier determines the literal switchable source.  This closes the
data-level decoder seam.  A subsequent counting lemma must still turn this
injectivity into a receiver-fiber cardinality and retained-weight estimate.

Constructive contract: composition of the proved finite code and auxiliary
decoder theorems only.  No `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAuxiliaryRecovery
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardProvenanceDecoder

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAuxiliaryRecovery
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

/-- On the reflected guard carrier, the final switched receiver and the fixed
provenance code recover the literal source pair. -/
theorem reflectedBentGuardGraft_pair_eq_of_target_eq_of_provenanceCode_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (firstState secondState : SlabAcceptedTwoReplicaState D)
    (first second : SlabObservablePairedFaceSwitchablePair
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hfirstLeft : first.pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent firstState)
    (hfirstRight : first.pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent firstState)
    (hsecondLeft : second.pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent secondState)
    (hsecondRight : second.pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent secondState)
    (htargetPair : slabObservablePairedFaceSwitchableTargetPair
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
        first =
      slabObservablePairedFaceSwitchableTargetPair
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
        second)
    (hcode : reflectedBentGuardGraft_pairProvenanceCode D first.pair =
      reflectedBentGuardGraft_pairProvenanceCode D second.pair) :
    first.pair = second.pair := by
  have hprovenance :=
    reflectedBentGuardGraft_provenance_of_target_eq_of_code_eq
      D hextent firstState secondState first second
        hfirstLeft hfirstRight hsecondLeft hsecondRight htargetPair hcode
  exact
    slabObservablePairedFaceSwitchable_sourcePair_eq_of_targetPair_eq_of_physical_eq_of_activeRows_eq
      first second htargetPair hprovenance.1 hprovenance.2.2

/-- The receiver-and-code key is injective on guarded switchable sources,
including their proof-carrying switchability witnesses. -/
theorem reflectedBentGuardGraft_source_eq_of_target_eq_of_provenanceCode_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (firstState secondState : SlabAcceptedTwoReplicaState D)
    (first second : SlabObservablePairedFaceSwitchablePair
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hfirstLeft : first.pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent firstState)
    (hfirstRight : first.pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent firstState)
    (hsecondLeft : second.pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent secondState)
    (hsecondRight : second.pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent secondState)
    (htargetPair : slabObservablePairedFaceSwitchableTargetPair
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
        first =
      slabObservablePairedFaceSwitchableTargetPair
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
        second)
    (hcode : reflectedBentGuardGraft_pairProvenanceCode D first.pair =
      reflectedBentGuardGraft_pairProvenanceCode D second.pair) :
    first = second := by
  have hpair :=
    reflectedBentGuardGraft_pair_eq_of_target_eq_of_provenanceCode_eq
      D hextent firstState secondState first second
        hfirstLeft hfirstRight hsecondLeft hsecondRight htargetPair hcode
  cases first
  cases second
  cases hpair
  rfl

#print axioms reflectedBentGuardGraft_pair_eq_of_target_eq_of_provenanceCode_eq
#print axioms reflectedBentGuardGraft_source_eq_of_target_eq_of_provenanceCode_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardProvenanceDecoder
