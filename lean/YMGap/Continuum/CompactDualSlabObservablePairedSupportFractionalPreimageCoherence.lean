/-
# Common-column coherence of paired-support target preimages

Two source-dependent recoupling choices can be compared only after their
switched physical fields are identified.  Equality of their concrete
four-cell targets supplies exactly those two field equalities.  Transporting
the first choice along them places both choices in one physical-only product
target carrier.

The concrete target equality also identifies both realized auxiliary
assignments.  Canonical whole-slab anchor independence moves the second
realization to the first source anchor, and target faithfulness then recovers
equality of the two abstract target columns.

Constructive contract: equality transport and the canonical finite target
compiler only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Concrete target equality supplies the physical transport -/

theorem slabObservablePairedSupportRecoupledTargetPair_leftPhysical_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) :
    slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId first.1 =
      slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId second.1 := by
  have hphysical := congrArg
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.1.1.1) heq
  change
    (slabObservablePairedSupportRecoupledLeftEntry
      D rootFaceId targetFaceId htarget first firstChoice).1.1 =
    (slabObservablePairedSupportRecoupledLeftEntry
      D rootFaceId targetFaceId htarget second secondChoice).1.1
    at hphysical
  rw [slabObservablePairedSupportRecoupledLeftEntry_physical,
    slabObservablePairedSupportRecoupledLeftEntry_physical] at hphysical
  exact hphysical

theorem slabObservablePairedSupportRecoupledTargetPair_rightPhysical_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) :
    slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId first.1 =
      slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId second.1 := by
  have hphysical := congrArg
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.2.1.1) heq
  change
    (slabObservablePairedSupportRecoupledRightEntry
      D rootFaceId targetFaceId htarget first firstChoice).1.1 =
    (slabObservablePairedSupportRecoupledRightEntry
      D rootFaceId targetFaceId htarget second secondChoice).1.1
    at hphysical
  rw [slabObservablePairedSupportRecoupledRightEntry_physical,
    slabObservablePairedSupportRecoupledRightEntry_physical] at hphysical
  exact hphysical

def slabObservablePairedSupportTransportChoiceOfTargetPairEq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) :
    SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second :=
  transportSlabPhysicalPairRecouplingTargetAssignment
    (slabObservablePairedSupportRecoupledTargetPair_leftPhysical_eq
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq)
    (slabObservablePairedSupportRecoupledTargetPair_rightPhysical_eq
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq)
    firstChoice

/-! ## 3. Both realized assignments identify one abstract column -/

theorem slabObservablePairedSupportRecoupledLeftEntry_assignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedSupportRecoupledLeftEntry
      D rootFaceId targetFaceId htarget source choice).1.2 =
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget source choice).leftAssignment := rfl

theorem slabObservablePairedSupportRecoupledRightEntry_assignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedSupportRecoupledRightEntry
      D rootFaceId targetFaceId htarget source choice).1.2 =
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget source choice).rightAssignment := rfl

theorem slabObservablePairedSupportRecoupledTargetPair_leftAssignment_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) :
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget first firstChoice).leftAssignment =
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget second secondChoice).leftAssignment := by
  have hraw := congrArg
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.1.1.2) heq
  simpa only [slabObservablePairedSupportRecoupledTargetPair,
    slabObservablePairedSupportRecoupledLeftEntry_assignment] using hraw

theorem slabObservablePairedSupportRecoupledTargetPair_rightAssignment_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) :
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget first firstChoice).rightAssignment =
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget second secondChoice).rightAssignment := by
  have hraw := congrArg
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.2.1.2) heq
  simpa only [slabObservablePairedSupportRecoupledTargetPair,
    slabObservablePairedSupportRecoupledRightEntry_assignment] using hraw

/-- The four exact consequences of equality of two concrete target pairs,
packaged once for the common-column compiler. -/
structure SlabObservablePairedSupportTargetPairEqData
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) where
  leftPhysical :
    slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId first.1 =
      slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId second.1
  rightPhysical :
    slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId first.1 =
      slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId second.1
  leftAssignment :
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget first firstChoice).leftAssignment =
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget second secondChoice).leftAssignment
  rightAssignment :
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget first firstChoice).rightAssignment =
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget second secondChoice).rightAssignment

def slabObservablePairedSupportTargetPairEqData
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) :
    SlabObservablePairedSupportTargetPairEqData
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq where
  leftPhysical :=
    slabObservablePairedSupportRecoupledTargetPair_leftPhysical_eq
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq
  rightPhysical :=
    slabObservablePairedSupportRecoupledTargetPair_rightPhysical_eq
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq
  leftAssignment :=
    slabObservablePairedSupportRecoupledTargetPair_leftAssignment_eq
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq
  rightAssignment :=
    slabObservablePairedSupportRecoupledTargetPair_rightAssignment_eq
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq

theorem SlabObservablePairedSupportTargetPairEqData.transport_choice_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId}
    {firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first}
    {secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second}
    {heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice}
    (data : SlabObservablePairedSupportTargetPairEqData
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq) :
    slabObservablePairedSupportTransportChoiceOfTargetPairEq
        D rootFaceId targetFaceId htarget
        first second firstChoice secondChoice heq =
      secondChoice :=
  slabObservablePairedSupportCanonicalAnchor_target_eq_of_result_eq
    D rootFaceId targetFaceId htarget first second
    firstChoice secondChoice data.leftPhysical data.rightPhysical
    data.leftAssignment data.rightAssignment

/-- **Every pair of preimages of one concrete four-cell target lies over one
common abstract target column.** -/
theorem slabObservablePairedSupportTransportChoiceOfTargetPairEq_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget first firstChoice =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget second secondChoice) :
    slabObservablePairedSupportTransportChoiceOfTargetPairEq
        D rootFaceId targetFaceId htarget
        first second firstChoice secondChoice heq =
      secondChoice := by
  exact SlabObservablePairedSupportTargetPairEqData.transport_choice_eq
    (slabObservablePairedSupportTargetPairEqData
      D rootFaceId targetFaceId htarget
      first second firstChoice secondChoice heq)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence.slabObservablePairedSupportRecoupledTargetPair_leftPhysical_eq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence.slabObservablePairedSupportRecoupledTargetPair_rightPhysical_eq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence.slabObservablePairedSupportTransportChoiceOfTargetPairEq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence.slabObservablePairedSupportTargetPairEqData
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence.SlabObservablePairedSupportTargetPairEqData.transport_choice_eq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence.slabObservablePairedSupportTransportChoiceOfTargetPairEq_eq
