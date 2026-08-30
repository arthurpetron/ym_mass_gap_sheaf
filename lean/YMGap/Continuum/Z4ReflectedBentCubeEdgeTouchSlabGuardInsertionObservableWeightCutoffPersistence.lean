/-
# Exact guarded observable-source weight at every cutoff

The guarded graft exists as a literal observable source for every
`1 ≤ D.cutoff`.  Its two entry weights are still exactly their physical
heat-face factors, so the cleared-support insertion identity gives the same
factorization at the ambient cutoff:

  guarded source weight
    = inserted-pattern heat factor * peeled-terminal weight.

All coupling, cutoff, and extent dependence remains explicit.  No uniform
lower bound is claimed.

Constructive contract: exact `Q'` equivalences and finite-product
factorizations only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeight
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeightCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedEntryFaceWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionFaceWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Exact coupling- and cutoff-visible receiver-weight factorization for the
ambient guarded observable source. -/
theorem reflectedBentGuardGraftObservableSourcePairAtCutoffWeight_eqv
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabObservableTwoReplicaPairWeight D
        (reflectedBentGuardGraftObservableSourcePairAtCutoff
          D hcutoff hextent state) ≈
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          reflectedBentSwitchLeftPhysical *
        (slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.1 *
          slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.2) := by
  have hleftEntry :=
    slabObservablePositiveEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardGraftLeftPositiveEntryAtCutoff
        D hcutoff hextent state)
  have hrightEntry :=
    slabExpandedFineEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardGraftRightExpandedEntryAtCutoff
        D hcutoff hextent state)
  have hterminalLeft :=
    slabExpandedFineEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1
  have hterminalRight :=
    slabExpandedFineEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2
  have hsourceFaces :
      slabObservableTwoReplicaPairWeight D
          (reflectedBentGuardGraftObservableSourcePairAtCutoff
            D hcutoff hextent state) ≈
        slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
            (reflectedBentGuardGraftLeftPhysical D hextent state) *
          slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
            (reflectedBentGuardGraftRightPhysical D hextent state) := by
    unfold slabObservableTwoReplicaPairWeight
      reflectedBentGuardGraftObservableSourcePairAtCutoff
    exact qmul_congr
      (by
        simpa only [reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical]
          using hleftEntry)
      (by
        simpa only [reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical]
          using hrightEntry)
  have hgraftFaces :
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          (reflectedBentGuardGraftLeftPhysical D hextent state) *
        slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          (reflectedBentGuardGraftRightPhysical D hextent state) ≈
      (slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          reflectedBentSwitchLeftPhysical *
        slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1) *
        slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 :=
    qmul_congr
      (reflectedBentGuardGraftLeftPhysicalFaceFactor_eqv
        D hextent state)
      (Q'.eqv_of_eq
        (reflectedBentGuardGraftRightPhysicalFaceFactor_eq
          D hextent state))
  have hterminalFaces :
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 *
        slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 ≈
      slabExpandedFineEntryWeight D
          (reflectedBentGuardCanonicalPeeling D hextent state).1.1 *
        slabExpandedFineEntryWeight D
          (reflectedBentGuardCanonicalPeeling D hextent state).1.2 :=
    qmul_congr (Q'.eqv_symm hterminalLeft)
      (Q'.eqv_symm hterminalRight)
  exact Q'.eqv_trans _ _ _ hsourceFaces
    (Q'.eqv_trans _ _ _ hgraftFaces
      (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv
          (slabParametricKPhysicalFaceFactor
            D.coupling D.cutoff D.extent reflectedBentSwitchLeftPhysical)
          (slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
            (reflectedBentGuardCanonicalPeeling
              D hextent state).1.1.1.1)
          (slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
            (reflectedBentGuardCanonicalPeeling
              D hextent state).1.2.1.1))
        (Q'.mul_eqv_congr_left
          (slabParametricKPhysicalFaceFactor
            D.coupling D.cutoff D.extent reflectedBentSwitchLeftPhysical)
          _ _ hterminalFaces)))

#print axioms reflectedBentGuardGraftObservableSourcePairAtCutoffWeight_eqv

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeightCutoffPersistence
