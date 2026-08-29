/-
# Exact observable source weight of the reflected guarded insertion

The observable pair weight is the product of two expanded-entry weights, and
each retained intertwiner coordinate has unit counting weight.  Combining this
with the cleared-support face factorization gives an exact identity:

  guarded source weight
    = isolated reflected-pattern face factor * peeled-terminal weight.

The factor still names the physical coupling, cutoff, and extent.  This is a
receiver-weight identity, not a beta-uniform lower bound.

Constructive contract: exact `Q'` equivalences and existing physical
factorizations only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabExpandedEntryFaceWeight
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionFaceWeight
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeight

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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- **Exact guarded receiver-weight factorization.**  The only numerical cost
of the guarded source relative to its peeled terminal is the isolated heat-face
factor of the inserted reflected pattern. -/
theorem reflectedBentGuardGraftObservableSourcePairWeight_eqv
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabObservableTwoReplicaPairWeight D
        (reflectedBentGuardGraftObservableSourcePair
          D hcutoff hextent state) ≈
      slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
          reflectedBentSwitchLeftPhysical *
        (slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.1 *
          slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.2) := by
  have hleftEntry :=
    slabObservablePositiveEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardGraftLeftPositiveEntry
        D hcutoff hextent state)
  have hrightEntry :=
    slabExpandedFineEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardGraftRightExpandedEntry
        D hcutoff hextent state)
  have hterminalLeft :=
    slabExpandedFineEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1
  have hterminalRight :=
    slabExpandedFineEntryWeight_eqv_physicalFaceFactor D
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2
  have hsourceFaces :
      slabObservableTwoReplicaPairWeight D
          (reflectedBentGuardGraftObservableSourcePair
            D hcutoff hextent state) ≈
        slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
            (reflectedBentGuardGraftLeftPhysical D hextent state) *
          slabParametricKPhysicalFaceFactor D.coupling D.cutoff D.extent
            (reflectedBentGuardGraftRightPhysical D hextent state) := by
    unfold slabObservableTwoReplicaPairWeight
      reflectedBentGuardGraftObservableSourcePair
    exact qmul_congr
      (by simpa only [reflectedBentGuardGraftLeftPositiveEntry_physical]
        using hleftEntry)
      (by simpa only [reflectedBentGuardGraftRightExpandedEntry_physical]
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

#print axioms reflectedBentGuardGraftObservableSourcePairWeight_eqv

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeight
