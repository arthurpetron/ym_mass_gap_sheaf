/-
# The two posterior transports occupy disjoint physical target sectors

The union-support connectedness predicate depends only on the two physical
face labellings.  Any facewise transposition preserves their pointwise union,
so it preserves this predicate.  Consequently:

* the existing full-mass support switch sends every support-disconnected
  source to a support-disconnected target;
* every successful strand-recoupling face switch sends a support-connected
  source to a support-connected target.

Thus these two transports never compete for the same physical target column.
This is the exact separation needed to combine the already normalized
disconnected branch with a later thinned or weighted connected branch.  No
connected-branch column estimate or positive aggregate floor is claimed here.

Constructive contract: definitional physical projections and the proved
face-swap invariance of union support only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization

namespace YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Physical sector invariance under an arbitrary face swap -/

/-- Union-support connectedness is unchanged by any facewise transposition
of the two physical replicas. -/
theorem slabTwoReplicaSupportConnectedB_faceSwap
    (extent rootFaceId targetFaceId : Nat)
    (selected : Nat → Bool) (left right : SlabLabelling) :
    slabTwoReplicaSupportSwapMask extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right)
        targetFaceId rootFaceId =
      slabTwoReplicaSupportSwapMask extent
        left right targetFaceId rootFaceId := by
  exact congrFun
    (slabTwoReplicaSupportSwapMask_faceSwap
      extent targetFaceId selected left right)
    rootFaceId

/-! ## 2. The full-mass support branch stays disconnected -/

/-- Every target of the existing support-aligned transport remains in the
support-disconnected physical sector. -/
theorem slabObservablePairedSupportRecoupledTargetPair_disconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId
        (slabObservablePairedSupportRecoupledTargetPair
          D rootFaceId targetFaceId htarget source choice) = false := by
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabObservablePairedSupportRecoupledTargetPair
  rw [slabObservablePairedSupportRecoupledLeftEntry_physical,
    slabObservablePairedSupportRecoupledRightEntry_physical]
  unfold slabObservablePairSupportSwitchedLeftPhysical
    slabObservablePairSupportSwitchedRightPhysical
  rw [slabTwoReplicaSupportConnectedB_faceSwap]
  exact source.disconnected

/-! ## 3. The strand branch preserves the source support sector -/

/-- A successful strand-recoupling face switch changes auxiliary strand
connectivity but preserves the physical union-support sector of its source. -/
theorem slabObservablePairedStrandRecoupledTargetPair_supportConnectedB
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId
        (slabObservablePairedStrandRecoupledTargetPair
          D rootFaceId targetFaceId htarget source choice) =
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source.1 := by
  let pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source choice.1
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabObservablePairedStrandRecoupledTargetPair
  rw [slabObservablePairedStrandSwitchedLeftEntry_physical,
    slabObservablePairedStrandSwitchedRightEntry_physical]
  rw [slabObservablePairedFaceSwapLeftPhysical_eq,
    slabObservablePairedFaceSwapRightPhysical_eq]
  rw [slabTwoReplicaSupportConnectedB_faceSwap]
  change slabTwoReplicaSupportSwapMask D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId rootFaceId = _
  change slabTwoReplicaSupportSwapMask D.extent
      source.1.1.1.1 source.1.2.1.1 targetFaceId rootFaceId = _
  rfl

/-- In particular, connected sources in the strand branch land only in
connected physical target columns. -/
theorem slabObservablePairedStrandRecoupledTargetPair_connected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source)
    (hconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source.1 = true) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId
        (slabObservablePairedStrandRecoupledTargetPair
          D rootFaceId targetFaceId htarget source choice) = true := by
  rw [slabObservablePairedStrandRecoupledTargetPair_supportConnectedB]
  exact hconnected

end YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation.slabTwoReplicaSupportConnectedB_faceSwap
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation.slabObservablePairedSupportRecoupledTargetPair_disconnected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation.slabObservablePairedStrandRecoupledTargetPair_supportConnectedB
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation.slabObservablePairedStrandRecoupledTargetPair_connected
