/-
# The exact decoder frontier for the paired-face component switch

Whole-slab recoupling may send many accepted source rows into one target
column; this multiplicity is legitimate and is controlled by bistochastic
column normalization.  The subsequent paired-face component switch must not
identify two different realized target columns.  The minimal constructive
datum is therefore a left inverse for that switch on strand-disconnected
source-cell pairs.

This module defines the direct switch on such a pair, states its explicit
decoder certificate, and proves the exact consequence needed by the column
argument: equality of two final successful outputs recovers equality of the
intermediate recoupled pairs.  For a fixed source row it then recovers the
SU(2) target column itself.

No decoder certificate is inhabited here.  No column-capacity, aggregate
floor, uniform rate, operator gap, or continuum claim is made.

Constructive contract: explicit functions and left-inverse equations only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization

namespace YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The direct component switch on a disconnected pair -/

/-- An accepted source-cell pair whose target-rooted paired strand component
does not contain the fixed root. -/
structure SlabObservablePairedFaceSwitchablePair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) where
  pair : SlabObservableTwoReplicaPair D rootFaceId
  pair_mem : pair ∈ slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId
  disconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
    D rootFaceId targetFaceId pair = false

def slabObservablePairedFaceSwitchableLeftEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId) :
    SlabObservablePositiveSourceEntry D rootFaceId :=
  slabObservablePositiveSourceEntryOfCarrier
    D rootFaceId
    (slabObservablePairedFaceSwapLeftPhysical
      D targetFaceId source.pair)
    (slabObservablePairedFaceSwapLeftPhysical_mem
      D targetFaceId source.pair)
    (slabObservablePairSwitchedLeftAssignment
      D rootFaceId targetFaceId htarget source.pair source.pair_mem)
    (slabObservablePairSwitchedLeftAssignment_mem
      D rootFaceId targetFaceId htarget source.pair source.pair_mem)
    (slabObservablePairedFaceSwapLeftPhysical_root_positive
      D rootFaceId targetFaceId source.pair source.disconnected)

def slabObservablePairedFaceSwitchableRightEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId) : SlabExpandedFineSourceEntry D :=
  slabExpandedFineSourceEntryOfCarrier
    D (slabObservablePairedFaceSwapRightPhysical
      D targetFaceId source.pair)
    (slabObservablePairedFaceSwapRightPhysical_mem
      D targetFaceId source.pair)
    (slabObservablePairSwitchedRightAssignment
      D rootFaceId targetFaceId htarget source.pair source.pair_mem)
    (slabObservablePairSwitchedRightAssignment_mem
      D rootFaceId targetFaceId htarget source.pair source.pair_mem)

/-- The literal paired-face switch, separated from the recoupling row that
produced its input pair. -/
def slabObservablePairedFaceSwitchableTargetPair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  (slabObservablePairedFaceSwitchableLeftEntry
      D rootFaceId targetFaceId htarget source,
    slabObservablePairedFaceSwitchableRightEntry
      D rootFaceId targetFaceId htarget source)

theorem slabObservablePairedFaceSwitchableLeftEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId) :
    (slabObservablePairedFaceSwitchableLeftEntry
      D rootFaceId targetFaceId htarget source).1.1 =
        slabObservablePairedFaceSwapLeftPhysical
          D targetFaceId source.pair := by
  unfold slabObservablePairedFaceSwitchableLeftEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

theorem slabObservablePairedFaceSwitchableRightEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId) :
    (slabObservablePairedFaceSwitchableRightEntry
      D rootFaceId targetFaceId htarget source).1.1 =
        slabObservablePairedFaceSwapRightPhysical
          D targetFaceId source.pair := by
  unfold slabObservablePairedFaceSwitchableRightEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

theorem slabObservablePairedFaceSwitchableTargetPair_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId) :
    slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget source ∈
      slabObservableFourCellTargetPairs D rootFaceId targetFaceId := by
  unfold slabObservablePairedFaceSwitchableTargetPair
  apply faceSwapEntries_mem_fourCellTarget
    D rootFaceId targetFaceId source.pair source.pair_mem
  · exact slabObservablePairedFaceSwitchableLeftEntry_physical
      D rootFaceId targetFaceId htarget source
  · exact slabObservablePairedFaceSwitchableRightEntry_physical
      D rootFaceId targetFaceId htarget source
  · exact source.disconnected
  · exact slabObservableTwoReplicaPairPairedFaceSwapMask_target
      D rootFaceId targetFaceId htarget source.pair source.pair_mem

/-! ## 2. The explicit left-inverse certificate -/

/-- The remaining combinatorial compiler: from any physical output pair,
construct a candidate original pair, and prove it is a left inverse on every
accepted strand-disconnected component switch.  Values away from the image
are intentionally unconstrained. -/
structure SlabObservablePairedFaceSwitchDecoderCertificate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) where
  decode : SlabObservableTwoReplicaPair D rootFaceId →
    SlabObservableTwoReplicaPair D rootFaceId
  left_inverse : ∀ source : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId,
    decode (slabObservablePairedFaceSwitchableTargetPair
      D rootFaceId targetFaceId htarget source) = source.pair

namespace SlabObservablePairedFaceSwitchDecoderCertificate

/-- A constructive left inverse makes the direct paired-face component
switch injective on its switchable carrier. -/
theorem targetPair_injective
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (first second : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId)
    (heq : slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget first =
      slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget second) :
    first.pair = second.pair := by
  have hdecoded := congrArg certificate.decode heq
  rw [certificate.left_inverse first,
    certificate.left_inverse second] at hdecoded
  exact hdecoded

/-! ## 3. Recover the intermediate recoupled column -/

def slabObservablePairedStrandSuccessfulSwitchablePair
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId where
  pair := slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId source choice.1
  pair_mem := slabObservablePairedStrandRecoupledPair_mem_source
    D rootFaceId targetFaceId source choice.1
  disconnected := choice.disconnected

theorem slabObservablePairedStrandRecoupledTargetPair_eq_direct
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source) :
    slabObservablePairedStrandRecoupledTargetPair
        D rootFaceId targetFaceId htarget source choice =
      slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget
        (slabObservablePairedStrandSuccessfulSwitchablePair
          source choice) := by
  unfold slabObservablePairedStrandRecoupledTargetPair
    slabObservablePairedStrandSwitchedLeftEntry
    slabObservablePairedStrandSwitchedRightEntry
    slabObservablePairedFaceSwitchableTargetPair
    slabObservablePairedFaceSwitchableLeftEntry
    slabObservablePairedFaceSwitchableRightEntry
    slabObservablePairedStrandSuccessfulSwitchablePair
  rfl

/-- Equality after successful component switching recovers equality of the
intermediate accepted recoupled pairs.  This is the exact coherence needed
before applying one common SU(2) column normalization. -/
theorem recoupledPair_eq_of_targetPair_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (firstSource : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId firstSource)
    (secondSource : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (secondChoice : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId secondSource)
    (heq : slabObservablePairedStrandRecoupledTargetPair
        D rootFaceId targetFaceId htarget firstSource firstChoice =
      slabObservablePairedStrandRecoupledTargetPair
        D rootFaceId targetFaceId htarget secondSource secondChoice) :
    slabObservablePairedStrandRecoupledPair
        D rootFaceId targetFaceId firstSource firstChoice.1 =
      slabObservablePairedStrandRecoupledPair
        D rootFaceId targetFaceId secondSource secondChoice.1 := by
  apply certificate.targetPair_injective
    (slabObservablePairedStrandSuccessfulSwitchablePair
      firstSource firstChoice)
    (slabObservablePairedStrandSuccessfulSwitchablePair
      secondSource secondChoice)
  rw [← slabObservablePairedStrandRecoupledTargetPair_eq_direct
    htarget firstSource firstChoice]
  rw [← slabObservablePairedStrandRecoupledTargetPair_eq_direct
    htarget secondSource secondChoice]
  exact heq

/-- On one fixed source row, the final physical output retains the successful
SU(2) target column. -/
theorem successfulChoice_eq_of_fixed_source_targetPair_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservablePairedFaceSwitchDecoderCertificate
      D rootFaceId targetFaceId htarget)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (first second : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source)
    (heq : slabObservablePairedStrandRecoupledTargetPair
        D rootFaceId targetFaceId htarget source first =
      slabObservablePairedStrandRecoupledTargetPair
        D rootFaceId targetFaceId htarget source second) :
    first = second := by
  have hpairs := certificate.recoupledPair_eq_of_targetPair_eq
    source first source second heq
  have hleft :
      (source.anchor.realize first.1).leftAssignment =
        (source.anchor.realize second.1).leftAssignment := by
    exact congrArg (fun pair => pair.1.1.2) hpairs
  have hright :
      (source.anchor.realize first.1).rightAssignment =
        (source.anchor.realize second.1).rightAssignment := by
    exact congrArg (fun pair => pair.2.1.2) hpairs
  have htarget := source.anchor.target_eq_of_realizations_eq
    source.anchor rfl rfl first.1 second.1 hleft hright
  rw [transportSlabPhysicalPairRecouplingTargetAssignment_rfl] at htarget
  exact Subtype.ext htarget

end SlabObservablePairedFaceSwitchDecoderCertificate

end YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder.slabObservablePairedFaceSwitchableTargetPair_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder.SlabObservablePairedFaceSwitchDecoderCertificate.targetPair_injective
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder.SlabObservablePairedFaceSwitchDecoderCertificate.recoupledPair_eq_of_targetPair_eq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder.SlabObservablePairedFaceSwitchDecoderCertificate.successfulChoice_eq_of_fixed_source_targetPair_eq
