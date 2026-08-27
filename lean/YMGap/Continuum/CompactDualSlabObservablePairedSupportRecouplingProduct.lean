/-
# One common recoupling matrix above a paired-support physical target

The union-support switch sends each switchable two-replica source to two
physical output labellings and two accepted auxiliary assignments.  Sources
with the same physical output therefore point at rows of one definitionally
common physical-pair recoupling matrix.

This module proves that the row code is injective on that fiber.  Equality of
rows first recovers the two switched auxiliary assignments by the exact
whole-slab production-row decoder.  The physical and auxiliary support
switches are involutions, so the original two expanded sources are then
recovered exactly.

Constructive contract: literal finite carriers and exact involutions only;
no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The switched physical output -/

def slabObservablePairSupportSwitchedLeftPhysical
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : SlabLabelling :=
  twoReplicaFaceSwapLeft
    (slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId)
    pair.1.1.1 pair.2.1.1

def slabObservablePairSupportSwitchedRightPhysical
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : SlabLabelling :=
  twoReplicaFaceSwapRight
    (slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId)
    pair.1.1.1 pair.2.1.1

/-! ## 2. Exact injectivity of the complete physical/auxiliary switch -/

theorem slabObservablePairSupportSwitch_injective
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleftPhysical :
      slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId left =
        slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId right)
    (hrightPhysical :
      slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId left =
        slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId right)
    (hleftAssignment :
      slabObservablePairSupportSwitchedLeftAssignment
          D rootFaceId targetFaceId left =
        slabObservablePairSupportSwitchedLeftAssignment
          D rootFaceId targetFaceId right)
    (hrightAssignment :
      slabObservablePairSupportSwitchedRightAssignment
          D rootFaceId targetFaceId left =
        slabObservablePairSupportSwitchedRightAssignment
          D rootFaceId targetFaceId right) :
    left = right := by
  have hleftOriginalPhysical : left.1.1.1 = right.1.1.1 := by
    have hleftInverse :=
      slabTwoReplicaCanonicalSupportSwapLeft_involutive
        D.extent targetFaceId left.1.1.1 left.2.1.1
    have hrightInverse :=
      slabTwoReplicaCanonicalSupportSwapLeft_involutive
        D.extent targetFaceId right.1.1.1 right.2.1.1
    change twoReplicaFaceSwapLeft
        (slabTwoReplicaSupportSwapMask D.extent
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId left)
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId left)
          targetFaceId)
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId left)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId left) = left.1.1.1 at hleftInverse
    change twoReplicaFaceSwapLeft
        (slabTwoReplicaSupportSwapMask D.extent
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId right)
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId right)
          targetFaceId)
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId right)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId right) = right.1.1.1 at hrightInverse
    rw [hleftPhysical, hrightPhysical] at hleftInverse
    exact hleftInverse.symm.trans hrightInverse
  have hrightOriginalPhysical : left.2.1.1 = right.2.1.1 := by
    have hleftInverse :=
      slabTwoReplicaCanonicalSupportSwapRight_involutive
        D.extent targetFaceId left.1.1.1 left.2.1.1
    have hrightInverse :=
      slabTwoReplicaCanonicalSupportSwapRight_involutive
        D.extent targetFaceId right.1.1.1 right.2.1.1
    change twoReplicaFaceSwapRight
        (slabTwoReplicaSupportSwapMask D.extent
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId left)
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId left)
          targetFaceId)
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId left)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId left) = left.2.1.1 at hleftInverse
    change twoReplicaFaceSwapRight
        (slabTwoReplicaSupportSwapMask D.extent
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId right)
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId right)
          targetFaceId)
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId right)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId right) = right.2.1.1 at hrightInverse
    rw [hleftPhysical, hrightPhysical] at hleftInverse
    exact hleftInverse.symm.trans hrightInverse
  have hleftOriginalAssignment : left.1.1.2 = right.1.1.2 := by
    have hleftInverse :=
      slabTwoReplicaSupportSwitchedLeftAssignment_involutive
        D.cutoff D.extent targetFaceId
        left.1.1.1 left.2.1.1 left.1.1.2 left.2.1.2
        left.1.assignment_mem
        (slabExpandedFineSourceEntryAssignment_mem left.2)
    have hrightInverse :=
      slabTwoReplicaSupportSwitchedLeftAssignment_involutive
        D.cutoff D.extent targetFaceId
        right.1.1.1 right.2.1.1 right.1.1.2 right.2.1.2
        right.1.assignment_mem
        (slabExpandedFineSourceEntryAssignment_mem right.2)
    change slabTwoReplicaSupportSwitchedLeftAssignment D.extent
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId left)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId left)
        targetFaceId
        (slabObservablePairSupportSwitchedLeftAssignment
          D rootFaceId targetFaceId left)
        (slabObservablePairSupportSwitchedRightAssignment
          D rootFaceId targetFaceId left) = left.1.1.2 at hleftInverse
    change slabTwoReplicaSupportSwitchedLeftAssignment D.extent
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId right)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId right)
        targetFaceId
        (slabObservablePairSupportSwitchedLeftAssignment
          D rootFaceId targetFaceId right)
        (slabObservablePairSupportSwitchedRightAssignment
          D rootFaceId targetFaceId right) = right.1.1.2 at hrightInverse
    rw [hleftPhysical, hrightPhysical,
      hleftAssignment, hrightAssignment] at hleftInverse
    exact hleftInverse.symm.trans hrightInverse
  have hrightOriginalAssignment : left.2.1.2 = right.2.1.2 := by
    have hleftInverse :=
      slabTwoReplicaSupportSwitchedRightAssignment_involutive
        D.cutoff D.extent targetFaceId
        left.1.1.1 left.2.1.1 left.1.1.2 left.2.1.2
        left.1.assignment_mem
        (slabExpandedFineSourceEntryAssignment_mem left.2)
    have hrightInverse :=
      slabTwoReplicaSupportSwitchedRightAssignment_involutive
        D.cutoff D.extent targetFaceId
        right.1.1.1 right.2.1.1 right.1.1.2 right.2.1.2
        right.1.assignment_mem
        (slabExpandedFineSourceEntryAssignment_mem right.2)
    change slabTwoReplicaSupportSwitchedRightAssignment D.extent
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId left)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId left)
        targetFaceId
        (slabObservablePairSupportSwitchedLeftAssignment
          D rootFaceId targetFaceId left)
        (slabObservablePairSupportSwitchedRightAssignment
          D rootFaceId targetFaceId left) = left.2.1.2 at hleftInverse
    change slabTwoReplicaSupportSwitchedRightAssignment D.extent
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId right)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId right)
        targetFaceId
        (slabObservablePairSupportSwitchedLeftAssignment
          D rootFaceId targetFaceId right)
        (slabObservablePairSupportSwitchedRightAssignment
          D rootFaceId targetFaceId right) = right.2.1.2 at hrightInverse
    rw [hleftPhysical, hrightPhysical,
      hleftAssignment, hrightAssignment] at hleftInverse
    exact hleftInverse.symm.trans hrightInverse
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext hleftOriginalPhysical hleftOriginalAssignment
  · apply Subtype.ext
    exact Prod.ext hrightOriginalPhysical hrightOriginalAssignment

/-! ## 3. One physical fiber of switchable sources -/

structure SlabObservablePairedSupportContributorAt
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling) : Type where
  pair : SlabObservableTwoReplicaPair D rootFaceId
  pair_mem : pair ∈ slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId
  disconnected :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId pair = false
  leftPhysical_eq :
    slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId pair = leftPhysical
  rightPhysical_eq :
    slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId pair = rightPhysical

def SlabObservablePairedSupportContributorAt.leftAssignment
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (contributor : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    SlabFusionWitnessAssignment :=
  slabObservablePairSupportSwitchedLeftAssignment
    D rootFaceId targetFaceId contributor.pair

def SlabObservablePairedSupportContributorAt.rightAssignment
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (contributor : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    SlabFusionWitnessAssignment :=
  slabObservablePairSupportSwitchedRightAssignment
    D rootFaceId targetFaceId contributor.pair

theorem SlabObservablePairedSupportContributorAt.leftAssignment_mem
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (contributor : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    contributor.leftAssignment ∈
      slabFineFusionWitnesses D leftPhysical := by
  exact Eq.mp
    (congrArg
      (fun physical => contributor.leftAssignment ∈
        slabFineFusionWitnesses D physical)
      contributor.leftPhysical_eq)
    (slabObservablePairSupportSwitchedLeftAssignment_mem
      D rootFaceId targetFaceId htarget
        contributor.pair contributor.pair_mem)

theorem SlabObservablePairedSupportContributorAt.rightAssignment_mem
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {leftPhysical rightPhysical : SlabLabelling}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (contributor : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    contributor.rightAssignment ∈
      slabFineFusionWitnesses D rightPhysical := by
  exact Eq.mp
    (congrArg
      (fun physical => contributor.rightAssignment ∈
        slabFineFusionWitnesses D physical)
      contributor.rightPhysical_eq)
    (slabObservablePairSupportSwitchedRightAssignment_mem
      D rootFaceId targetFaceId htarget
        contributor.pair contributor.pair_mem)

/-! ## 4. The common-matrix production row and its exact decoder -/

def slabObservablePairedSupportContributorProductionRow
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (contributor : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    SlabPhysicalPairRecouplingSourceAssignment
      D.extent leftPhysical rightPhysical :=
  slabPhysicalPairRecouplingProductionSource
    D.cutoff D.extent leftPhysical rightPhysical
    contributor.leftAssignment contributor.rightAssignment
    (contributor.leftAssignment_mem htarget)
    (contributor.rightAssignment_mem htarget)

/-- Contributors with the same switched physical output occupy distinct rows
of the one common physical-pair matrix. -/
theorem slabObservablePairedSupportContributorProductionRow_injective
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical)
    (heq : slabObservablePairedSupportContributorProductionRow
        D rootFaceId targetFaceId leftPhysical rightPhysical htarget left =
      slabObservablePairedSupportContributorProductionRow
        D rootFaceId targetFaceId leftPhysical rightPhysical htarget right) :
    left = right := by
  have hassignments :=
    slabPhysicalPairRecouplingProductionSource_assignments_injective
      D.cutoff D.extent leftPhysical rightPhysical
      left.leftAssignment left.rightAssignment
      right.leftAssignment right.rightAssignment
      (left.leftAssignment_mem htarget)
      (left.rightAssignment_mem htarget)
      (right.leftAssignment_mem htarget)
      (right.rightAssignment_mem htarget)
      heq
  have hpairs : left.pair = right.pair :=
    slabObservablePairSupportSwitch_injective D left.pair right.pair
      (left.leftPhysical_eq.trans right.leftPhysical_eq.symm)
      (left.rightPhysical_eq.trans right.rightPhysical_eq.symm)
      hassignments.1 hassignments.2
  cases left
  cases right
  simp only at hpairs
  subst hpairs
  rfl

end YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct.slabObservablePairSupportSwitch_injective
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct.SlabObservablePairedSupportContributorAt.leftAssignment_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct.SlabObservablePairedSupportContributorAt.rightAssignment_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct.slabObservablePairedSupportContributorProductionRow
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct.slabObservablePairedSupportContributorProductionRow_injective
