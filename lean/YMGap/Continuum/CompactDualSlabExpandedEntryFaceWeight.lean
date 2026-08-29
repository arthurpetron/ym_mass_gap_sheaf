/-
# Expanded slab entries carry exactly their heat face factor

The retained fine-intertwiner coordinate has unit counting weight.  Therefore
every literal expanded source entry carries exactly its physical heat face
factor, up to the constructive rational equivalence used throughout the model.

Constructive contract: definitional unfolding and exact `Q'` algebra only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction

namespace YMGap.Continuum.CompactDualSlabExpandedEntryFaceWeight

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-- The auxiliary assignment affects membership, but its retained raw weight is
one; the numerical entry weight is exactly the physical heat product. -/
theorem slabExpandedFineEntryWeight_eqv_physicalFaceFactor
    (D : SlabPhysicalData) (entry : SlabExpandedFineSourceEntry D) :
    slabExpandedFineEntryWeight D entry ≈
      slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent entry.1.1 := by
  unfold slabExpandedFineEntryWeight slabExpandedFineSourceWeight
    retainedFineIntertwinerPhysicalFiberWeight
    retainedFineIntertwinerRawWeight
  exact Q'.mul_one_eqv _

/-- The same identity on the positive-root subtype used as the first observable
replica. -/
theorem slabObservablePositiveEntryWeight_eqv_physicalFaceFactor
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D rootFaceId) :
    slabObservablePositiveEntryWeight D entry ≈
      slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent entry.1.1 := by
  unfold slabObservablePositiveEntryWeight slabExpandedFineSourceWeight
    retainedFineIntertwinerPhysicalFiberWeight
    retainedFineIntertwinerRawWeight
  exact Q'.mul_one_eqv _

#print axioms slabExpandedFineEntryWeight_eqv_physicalFaceFactor
#print axioms slabObservablePositiveEntryWeight_eqv_physicalFaceFactor

end YMGap.Continuum.CompactDualSlabExpandedEntryFaceWeight
