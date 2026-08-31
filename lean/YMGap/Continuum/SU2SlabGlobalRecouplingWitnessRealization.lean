/-
# Whole-slab physical realization of recoupling targets

The local rank compiler realizes every right-tree recoupling target by two
literal accepted production witnesses.  Direct recursion through the opaque
all-valence package needlessly recompiles the degree split at every link.
Instead this module first exposes a small realized package: its target type,
link, and two witness functions are stored fields.  A structural dependent
fold then assembles accepted global auxiliary assignments.

The resulting assignments lie above the canonical paired-face physical swap.
The Boolean four-cell realization is built in the final section.  Global
column capacity remains a separate obligation.

Constructive contract: structural dependent products and literal finite-list
membership only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabLocalRecouplingWitnessRealization
import YMGap.Continuum.SU2SlabRecouplingFractionalSwitch

namespace YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct
open YMGap.Continuum.SU2SlabGlobalCrossedSchurProduct
open YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
open YMGap.Continuum.SU2SlabLocalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabRecouplingFractionalSwitch
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Small proof-carrying realized packages -/

structure SlabObservableRealizedBistochasticPackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) where
  linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}
  Target : Type
  pointed : PointedFiniteBistochasticQKernelPackage
  decodeTarget : pointed.package.Target → Target
  leftAuxiliary : Target → SlabLabelling
  rightAuxiliary : Target → SlabLabelling
  left_mem : ∀ target, leftAuxiliary target ∈
    slabLinkFusionWitnesses D.cutoff D.extent
      (twoReplicaFaceSwapLeft
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D pair targetFaceId)
        pair.1.1.1 pair.2.1.1)
      linked.1
  right_mem : ∀ target, rightAuxiliary target ∈
    slabLinkFusionWitnesses D.cutoff D.extent
      (twoReplicaFaceSwapRight
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D pair targetFaceId)
        pair.1.1.1 pair.2.1.1)
      linked.1

theorem slabObservablePairCrossedSwitchDataAtLink_leftPhysical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    higherCrossedLeftPhysical
        (slabObservablePairCrossedSwitchDataAtLink
          D rootFaceId targetFaceId htarget pair hpair linked) =
      twoReplicaFaceSwapLeft
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D pair targetFaceId)
        pair.1.1.1 pair.2.1.1 := by
  unfold slabObservablePairCrossedSwitchDataAtLink
  apply slabObservablePairCrossedSwitchDataAtLinkWithMask_leftPhysical

theorem slabObservablePairCrossedSwitchDataAtLink_rightPhysical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    higherCrossedRightPhysical
        (slabObservablePairCrossedSwitchDataAtLink
          D rootFaceId targetFaceId htarget pair hpair linked) =
      twoReplicaFaceSwapRight
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D pair targetFaceId)
        pair.1.1.1 pair.2.1.1 := by
  unfold slabObservablePairCrossedSwitchDataAtLink
  apply slabObservablePairCrossedSwitchDataAtLinkWithMask_rightPhysical

def slabObservableRealizedBistochasticPackageAtLink
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    SlabObservableRealizedBistochasticPackage
      D rootFaceId targetFaceId pair :=
  let localData := slabObservablePairCrossedSwitchDataAtLink
    D rootFaceId targetFaceId htarget pair hpair linked
  { linked := linked
    Target :=
      (crossedLinkBistochasticKernelPackage
        (slabIncidentPlaqIds D.extent linked.1).length localData).Target
    pointed := slabObservablePairCrossedPointedBistochasticPackageAtLink
      D rootFaceId targetFaceId htarget pair hpair linked
    decodeTarget := fun target => target
    leftAuxiliary := fun target =>
      (crossedLinkTargetProductionWitnessPair
        localData target).leftAuxiliary
    rightAuxiliary := fun target =>
      (crossedLinkTargetProductionWitnessPair
        localData target).rightAuxiliary
    left_mem := fun target => by
      rw [← slabObservablePairCrossedSwitchDataAtLink_leftPhysical
        D rootFaceId targetFaceId htarget pair hpair linked]
      exact (crossedLinkTargetProductionWitnessPair
        localData target).left_mem
    right_mem := fun target => by
      rw [← slabObservablePairCrossedSwitchDataAtLink_rightPhysical
        D rootFaceId targetFaceId htarget pair hpair linked]
      exact (crossedLinkTargetProductionWitnessPair
        localData target).right_mem }

def slabObservableRealizedBistochasticPackages
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    List (SlabObservableRealizedBistochasticPackage
      D rootFaceId targetFaceId pair) :=
  (boundaryCompleteSlabLinks D.extent).attach.map fun linked =>
    slabObservableRealizedBistochasticPackageAtLink
      D rootFaceId targetFaceId htarget pair hpair linked

def pointedPackagesOfRealized
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {pair : SlabObservableTwoReplicaPair D rootFaceId} :
    List (SlabObservableRealizedBistochasticPackage
      D rootFaceId targetFaceId pair) →
      List PointedFiniteBistochasticQKernelPackage
  | [] => []
  | package :: packages =>
      package.pointed :: pointedPackagesOfRealized packages

theorem slabObservableRealized_pointedPackages
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    pointedPackagesOfRealized
        (slabObservableRealizedBistochasticPackages
          D rootFaceId targetFaceId htarget pair hpair) =
      slabObservablePairCrossedPointedBistochasticPackages
        D rootFaceId targetFaceId htarget pair hpair := by
  unfold slabObservableRealizedBistochasticPackages
    slabObservablePairCrossedPointedBistochasticPackages
  induction (boundaryCompleteSlabLinks D.extent).attach with
  | nil => rfl
  | cons linked rest ih =>
      simp only [List.map_cons, pointedPackagesOfRealized,
        slabObservableRealizedBistochasticPackageAtLink]
      exact congrArg
        (List.cons
          (slabObservablePairCrossedPointedBistochasticPackageAtLink
            D rootFaceId targetFaceId htarget pair hpair linked)) ih

theorem slabObservableRealized_links
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    (slabObservableRealizedBistochasticPackages
        D rootFaceId targetFaceId htarget pair hpair).map
        (fun package => package.linked.1) =
      boundaryCompleteSlabLinks D.extent := by
  unfold slabObservableRealizedBistochasticPackages
  rw [List.map_map]
  change (boundaryCompleteSlabLinks D.extent).attach.map Subtype.val = _
  exact List.attach_map_subtype_val _

/-! ## 2. The cheap structural fold -/

structure SlabObservableRealizedAssignmentsResult
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (packages : List (SlabObservableRealizedBistochasticPackage
      D rootFaceId targetFaceId pair)) where
  leftAssignment : SlabFusionWitnessAssignment
  rightAssignment : SlabFusionWitnessAssignment
  left_mem : leftAssignment ∈
    slabFusionWitnessAssignmentsOn D.cutoff D.extent
      (twoReplicaFaceSwapLeft
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D pair targetFaceId)
        pair.1.1.1 pair.2.1.1)
      (packages.map fun package => package.linked.1)
  right_mem : rightAssignment ∈
    slabFusionWitnessAssignmentsOn D.cutoff D.extent
      (twoReplicaFaceSwapRight
        (slabObservableTwoReplicaPairPairedFaceSwapMask
          D pair targetFaceId)
        pair.1.1.1 pair.2.1.1)
      (packages.map fun package => package.linked.1)

def slabObservableRealizeTargetAssignments
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    (packages : List (SlabObservableRealizedBistochasticPackage
      D rootFaceId targetFaceId pair)) →
    FiniteBistochasticTargetAssignment
      (finiteBistochasticPackagesOfPointed
        (pointedPackagesOfRealized packages)) →
    SlabObservableRealizedAssignmentsResult
      D rootFaceId targetFaceId pair packages
  | [], _ => ⟨[], [], List.mem_cons_self, List.mem_cons_self⟩
  | package :: packages, target => by
      let tail := slabObservableRealizeTargetAssignments
        D rootFaceId targetFaceId pair packages target.2
      exact
        { leftAssignment :=
            (package.linked.1,
              package.leftAuxiliary (package.decodeTarget target.1)) ::
              tail.leftAssignment
          rightAssignment :=
            (package.linked.1,
              package.rightAuxiliary (package.decodeTarget target.1)) ::
              tail.rightAssignment
          left_mem := by
            simp only [List.map_cons, slabFusionWitnessAssignmentsOn]
            apply List.mem_flatMap.mpr
            refine ⟨package.leftAuxiliary (package.decodeTarget target.1),
              package.left_mem (package.decodeTarget target.1), ?_⟩
            exact List.mem_map.mpr
              ⟨tail.leftAssignment, tail.left_mem, rfl⟩
          right_mem := by
            simp only [List.map_cons, slabFusionWitnessAssignmentsOn]
            apply List.mem_flatMap.mpr
            refine ⟨package.rightAuxiliary (package.decodeTarget target.1),
              package.right_mem (package.decodeTarget target.1), ?_⟩
            exact List.mem_map.mpr
              ⟨tail.rightAssignment, tail.right_mem, rfl⟩ }

/-! ## 3. Transport the existing target assignment into the realized fold -/

def transportFiniteBistochasticTargetAssignment
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (target : FiniteBistochasticTargetAssignment right) :
    FiniteBistochasticTargetAssignment left := by
  cases hpackages
  exact target

def slabObservableRecoupledAssignmentsResult
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    SlabObservableRealizedAssignmentsResult
      D rootFaceId targetFaceId pair
      (slabObservableRealizedBistochasticPackages
        D rootFaceId targetFaceId htarget pair hpair) :=
  let packages := slabObservableRealizedBistochasticPackages
    D rootFaceId targetFaceId htarget pair hpair
  let hpointed := slabObservableRealized_pointedPackages
    D rootFaceId targetFaceId htarget pair hpair
  let hpackages := congrArg finiteBistochasticPackagesOfPointed hpointed
  slabObservableRealizeTargetAssignments
    D rootFaceId targetFaceId pair packages
    (transportFiniteBistochasticTargetAssignment hpackages target)

theorem slabObservableRecoupledLeftAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    (slabObservableRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget pair hpair target).leftAssignment ∈
      slabFineFusionWitnesses D
        (twoReplicaFaceSwapLeft
          (slabObservableTwoReplicaPairPairedFaceSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) := by
  unfold slabFineFusionWitnesses
  rw [← slabObservableRealized_links
    D rootFaceId targetFaceId htarget pair hpair]
  exact (slabObservableRecoupledAssignmentsResult
    D rootFaceId targetFaceId htarget pair hpair target).left_mem

theorem slabObservableRecoupledRightAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    (slabObservableRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget pair hpair target).rightAssignment ∈
      slabFineFusionWitnesses D
        (twoReplicaFaceSwapRight
          (slabObservableTwoReplicaPairPairedFaceSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) := by
  unfold slabFineFusionWitnesses
  rw [← slabObservableRealized_links
    D rootFaceId targetFaceId htarget pair hpair]
  exact (slabObservableRecoupledAssignmentsResult
    D rootFaceId targetFaceId htarget pair hpair target).right_mem

/-! ## 4. The crossed physical fields remain in the literal carrier -/

theorem twoReplicaFaceSwapLeft_mem_bounded
    {K extent : Nat} (mask : Nat → Bool)
    {leftPhysical rightPhysical : SlabLabelling}
    (hleft : leftPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent))
    (hright : rightPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent)) :
    twoReplicaFaceSwapLeft mask leftPhysical rightPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent) := by
  have hleftSound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) leftPhysical hleft
  have hrightSound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) rightPhysical hright
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hleftSound.1 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hrightSound.1 faceId hface
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hleftSound.2 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hrightSound.2 faceId hface

theorem twoReplicaFaceSwapRight_mem_bounded
    {K extent : Nat} (mask : Nat → Bool)
    {leftPhysical rightPhysical : SlabLabelling}
    (hleft : leftPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent))
    (hright : rightPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent)) :
    twoReplicaFaceSwapRight mask leftPhysical rightPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent) := by
  have hleftSound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) leftPhysical hleft
  have hrightSound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) rightPhysical hright
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hrightSound.1 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hleftSound.1 faceId hface
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hrightSound.2 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hleftSound.2 faceId hface

/-! ## 5. Actual accepted target entries -/

def faceSwapLeftPhysicalOfMask
    (mask : Nat → Bool)
    (leftPhysical rightPhysical : SlabLabelling) : SlabLabelling :=
  twoReplicaFaceSwapLeft mask leftPhysical rightPhysical

def faceSwapRightPhysicalOfMask
    (mask : Nat → Bool)
    (leftPhysical rightPhysical : SlabLabelling) : SlabLabelling :=
  twoReplicaFaceSwapRight mask leftPhysical rightPhysical

theorem faceSwapLeftPhysicalOfMask_eq
    (mask : Nat → Bool)
    (leftPhysical rightPhysical : SlabLabelling) :
    faceSwapLeftPhysicalOfMask mask leftPhysical rightPhysical =
      twoReplicaFaceSwapLeft mask leftPhysical rightPhysical := rfl

theorem faceSwapRightPhysicalOfMask_eq
    (mask : Nat → Bool)
    (leftPhysical rightPhysical : SlabLabelling) :
    faceSwapRightPhysicalOfMask mask leftPhysical rightPhysical =
      twoReplicaFaceSwapRight mask leftPhysical rightPhysical := rfl

def slabObservablePairedFaceSwapLeftPhysical
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : SlabLabelling :=
  faceSwapLeftPhysicalOfMask
    (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
    pair.1.1.1 pair.2.1.1

def slabObservablePairedFaceSwapRightPhysical
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : SlabLabelling :=
  faceSwapRightPhysicalOfMask
    (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
    pair.1.1.1 pair.2.1.1

theorem slabObservablePairedFaceSwapLeftPhysical_eq
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    slabObservablePairedFaceSwapLeftPhysical D targetFaceId pair =
      twoReplicaFaceSwapLeft
        (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
        pair.1.1.1 pair.2.1.1 := by
  unfold slabObservablePairedFaceSwapLeftPhysical
  apply faceSwapLeftPhysicalOfMask_eq

theorem slabObservablePairedFaceSwapRightPhysical_eq
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    slabObservablePairedFaceSwapRightPhysical D targetFaceId pair =
      twoReplicaFaceSwapRight
        (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
        pair.1.1.1 pair.2.1.1 := by
  unfold slabObservablePairedFaceSwapRightPhysical
  apply faceSwapRightPhysicalOfMask_eq

def slabObservableRecoupledLeftAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    SlabFusionWitnessAssignment :=
  (slabObservableRecoupledAssignmentsResult
    D rootFaceId targetFaceId htarget pair hpair target).leftAssignment

def slabObservableRecoupledRightAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    SlabFusionWitnessAssignment :=
  (slabObservableRecoupledAssignmentsResult
    D rootFaceId targetFaceId htarget pair hpair target).rightAssignment

theorem slabObservableRecoupledLeftAssignment_accepted
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    slabObservableRecoupledLeftAssignment
        D rootFaceId targetFaceId htarget pair hpair target ∈
      slabFineFusionWitnesses D
        (slabObservablePairedFaceSwapLeftPhysical
          D targetFaceId pair) := by
  unfold slabObservableRecoupledLeftAssignment
    slabObservablePairedFaceSwapLeftPhysical
  exact slabObservableRecoupledLeftAssignment_mem
    D rootFaceId targetFaceId htarget pair hpair target

theorem slabObservableRecoupledRightAssignment_accepted
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    slabObservableRecoupledRightAssignment
        D rootFaceId targetFaceId htarget pair hpair target ∈
      slabFineFusionWitnesses D
        (slabObservablePairedFaceSwapRightPhysical
          D targetFaceId pair) := by
  unfold slabObservableRecoupledRightAssignment
    slabObservablePairedFaceSwapRightPhysical
  exact slabObservableRecoupledRightAssignment_mem
    D rootFaceId targetFaceId htarget pair hpair target

theorem slabObservablePairedFaceSwapLeftPhysical_mem
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    slabObservablePairedFaceSwapLeftPhysical D targetFaceId pair ∈
      D.physicalLabellings := by
  unfold slabObservablePairedFaceSwapLeftPhysical
    SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  exact twoReplicaFaceSwapLeft_mem_bounded
    (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
    pair.1.physical_mem
    (mem_slabExpandedFineSources_iff.mp pair.2.2).1

theorem slabObservablePairedFaceSwapRightPhysical_mem
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    slabObservablePairedFaceSwapRightPhysical D targetFaceId pair ∈
      D.physicalLabellings := by
  unfold slabObservablePairedFaceSwapRightPhysical
    SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  exact twoReplicaFaceSwapRight_mem_bounded
    (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
    pair.1.physical_mem
    (mem_slabExpandedFineSources_iff.mp pair.2.2).1

def slabExpandedFineSourceEntryOfCarrier
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical) :
    SlabExpandedFineSourceEntry D :=
  ⟨(physical, assignment),
    mem_slabExpandedFineSources_iff.mpr ⟨hphysical, hassignment⟩⟩

def slabObservablePositiveSourceEntryOfCarrier
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical)
    (hpositive : 0 < physical rootFaceId) :
    SlabObservablePositiveSourceEntry D rootFaceId :=
  ⟨(physical, assignment),
    mem_slabObservablePositiveExpandedSources_iff.mpr
      ⟨mem_slabExpandedFineSources_iff.mpr
          ⟨hphysical, hassignment⟩,
        hpositive⟩⟩

theorem slabExpandedFineSourceEntryOfCarrier_physical
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical) :
    (slabExpandedFineSourceEntryOfCarrier
      D physical hphysical assignment hassignment).1.1 = physical := rfl

theorem slabObservablePositiveSourceEntryOfCarrier_physical
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical)
    (hpositive : 0 < physical rootFaceId) :
    (slabObservablePositiveSourceEntryOfCarrier
      D rootFaceId physical hphysical assignment
        hassignment hpositive).1.1 = physical := rfl

theorem slabExpandedFineSourceEntryOfCarrier_assignment
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical) :
    (slabExpandedFineSourceEntryOfCarrier
      D physical hphysical assignment hassignment).1.2 = assignment := rfl

theorem slabObservablePositiveSourceEntryOfCarrier_assignment
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (physical : SlabLabelling)
    (hphysical : physical ∈ D.physicalLabellings)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical)
    (hpositive : 0 < physical rootFaceId) :
    (slabObservablePositiveSourceEntryOfCarrier
      D rootFaceId physical hphysical assignment
        hassignment hpositive).1.2 = assignment := rfl

theorem slabObservablePairedFaceSwapLeftPhysical_root_positive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hdisconnected : slabObservableTwoReplicaPairPairedFaceConnectedB
      D rootFaceId targetFaceId pair = false) :
    0 < slabObservablePairedFaceSwapLeftPhysical
      D targetFaceId pair rootFaceId := by
  unfold slabObservablePairedFaceSwapLeftPhysical
    faceSwapLeftPhysicalOfMask twoReplicaFaceSwapLeft
  rw [slabObservableTwoReplicaPairPairedFaceSwapMask_root_of_disconnected
    D rootFaceId targetFaceId pair hdisconnected]
  exact pair.1.source_positive

def slabObservableRecoupledLeftEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    SlabObservablePositiveSourceEntry D rootFaceId :=
  slabObservablePositiveSourceEntryOfCarrier
    D rootFaceId
    (slabObservablePairedFaceSwapLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairedFaceSwapLeftPhysical_mem
      D targetFaceId source.1)
    (slabObservableRecoupledLeftAssignment
      D rootFaceId targetFaceId htarget source.1
        source.pair_mem_fourCell choice)
    (slabObservableRecoupledLeftAssignment_accepted
      D rootFaceId targetFaceId htarget source.1
        source.pair_mem_fourCell choice)
    (slabObservablePairedFaceSwapLeftPhysical_root_positive
      D rootFaceId targetFaceId source.1 source.pairedFace_disconnected)

def slabObservableRecoupledRightEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    SlabExpandedFineSourceEntry D :=
  slabExpandedFineSourceEntryOfCarrier
    D
    (slabObservablePairedFaceSwapRightPhysical
      D targetFaceId source.1)
    (slabObservablePairedFaceSwapRightPhysical_mem
      D targetFaceId source.1)
    (slabObservableRecoupledRightAssignment
      D rootFaceId targetFaceId htarget source.1
        source.pair_mem_fourCell choice)
    (slabObservableRecoupledRightAssignment_accepted
      D rootFaceId targetFaceId htarget source.1
        source.pair_mem_fourCell choice)

def slabObservableRecoupledTargetPair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  (slabObservableRecoupledLeftEntry
      D rootFaceId targetFaceId htarget source choice,
    slabObservableRecoupledRightEntry
      D rootFaceId targetFaceId htarget source choice)

theorem slabObservableRecoupledLeftEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    (slabObservableRecoupledLeftEntry
        D rootFaceId targetFaceId htarget source choice).1.1 =
      slabObservablePairedFaceSwapLeftPhysical
        D targetFaceId source.1 := by
  unfold slabObservableRecoupledLeftEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

theorem slabObservableRecoupledRightEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    (slabObservableRecoupledRightEntry
        D rootFaceId targetFaceId htarget source choice).1.1 =
      slabObservablePairedFaceSwapRightPhysical
        D targetFaceId source.1 := by
  unfold slabObservableRecoupledRightEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

theorem faceSwapEntries_mem_fourCellTarget
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservableTwoReplicaPair D rootFaceId)
    (hsource : source ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (left : SlabObservablePositiveSourceEntry D rootFaceId)
    (right : SlabExpandedFineSourceEntry D)
    (hleft : left.1.1 =
      slabObservablePairedFaceSwapLeftPhysical D targetFaceId source)
    (hright : right.1.1 =
      slabObservablePairedFaceSwapRightPhysical D targetFaceId source)
    (hroot : slabObservableTwoReplicaPairPairedFaceSwapMask
      D source targetFaceId rootFaceId = false)
    (htarget : slabObservableTwoReplicaPairPairedFaceSwapMask
      D source targetFaceId targetFaceId = true) :
    (left, right) ∈
      slabObservableFourCellTargetPairs
        D rootFaceId targetFaceId := by
  have hcells := (mem_cartesian_iff
    (slabObservableRootTargetEntries D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetComplementEntries
      D rootFaceId targetFaceId) source).mp hsource
  have hfirst := List.mem_filter.mp hcells.1
  have hsecond := List.mem_filter.mp hcells.2
  have hsecondParts := (Bool.and_eq_true _ _).mp hsecond.2
  apply (mem_cartesian_iff
    (slabObservableRootTargetComplementEntries
      D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetEntries
      D rootFaceId targetFaceId)
    (left, right)).mpr
  constructor
  · apply List.mem_filter.mpr
    constructor
    · exact List.mem_attach _ left
    · unfold SlabObservablePositiveSourceEntry.facePositiveB
      rw [hleft]
      simp only [slabObservablePairedFaceSwapLeftPhysical,
        faceSwapLeftPhysicalOfMask, twoReplicaFaceSwapLeft,
        htarget, if_true]
      exact hsecondParts.2
  · apply List.mem_filter.mpr
    constructor
    · exact List.mem_attach _ right
    · apply (Bool.and_eq_true _ _).mpr
      constructor
      · unfold SlabExpandedFineSourceEntry.facePositiveB
        rw [hright]
        simp only [slabObservablePairedFaceSwapRightPhysical,
          faceSwapRightPhysicalOfMask, twoReplicaFaceSwapRight, hroot]
        exact hsecondParts.1
      · unfold SlabExpandedFineSourceEntry.facePositiveB
        rw [hright]
        simp only [slabObservablePairedFaceSwapRightPhysical,
          faceSwapRightPhysicalOfMask, twoReplicaFaceSwapRight,
          htarget, if_true]
        exact hfirst.2

theorem slabObservableRecoupledTargetPair_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableSeparatedRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservableSeparatedRecouplingChoice
      D rootFaceId targetFaceId htarget source) :
    slabObservableRecoupledTargetPair
        D rootFaceId targetFaceId htarget source choice ∈
      slabObservableFourCellTargetPairs
        D rootFaceId targetFaceId := by
  unfold slabObservableRecoupledTargetPair
  apply faceSwapEntries_mem_fourCellTarget
    D rootFaceId targetFaceId source.1 source.pair_mem_fourCell
  · exact slabObservableRecoupledLeftEntry_physical
      D rootFaceId targetFaceId htarget source choice
  · exact slabObservableRecoupledRightEntry_physical
      D rootFaceId targetFaceId htarget source choice
  · exact slabObservableTwoReplicaPairPairedFaceSwapMask_root_of_disconnected
      D rootFaceId targetFaceId source.1 source.pairedFace_disconnected
  · exact slabObservableTwoReplicaPairPairedFaceSwapMask_target
      D rootFaceId targetFaceId htarget source.1 source.pair_mem_fourCell

/-! ## 6. Close the physical realization node -/

def slabObservableRecouplingTargetRealization
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    SlabObservableRecouplingTargetRealization
      D rootFaceId targetFaceId htarget where
  realize := slabObservableRecoupledTargetPair
    D rootFaceId targetFaceId htarget
  realize_left_physical := by
    intro source choice
    unfold slabObservableRecoupledTargetPair
    exact Eq.trans
      (slabObservableRecoupledLeftEntry_physical
        D rootFaceId targetFaceId htarget source choice)
      (slabObservablePairedFaceSwapLeftPhysical_eq
        D targetFaceId source.1)
  realize_right_physical := by
    intro source choice
    unfold slabObservableRecoupledTargetPair
    exact Eq.trans
      (slabObservableRecoupledRightEntry_physical
        D rootFaceId targetFaceId htarget source choice)
      (slabObservablePairedFaceSwapRightPhysical_eq
        D targetFaceId source.1)
  realize_mem_target := by
    intro source choice
    exact slabObservableRecoupledTargetPair_mem
      D rootFaceId targetFaceId htarget source choice

#print axioms slabObservableRealizedBistochasticPackageAtLink
#print axioms slabObservableRealized_pointedPackages
#print axioms slabObservableRealizeTargetAssignments
#print axioms slabObservableRecoupledLeftAssignment_mem
#print axioms slabObservableRecoupledRightAssignment_mem
#print axioms twoReplicaFaceSwapLeft_mem_bounded
#print axioms twoReplicaFaceSwapRight_mem_bounded
#print axioms slabObservableRecoupledLeftEntry
#print axioms slabObservableRecoupledRightEntry
#print axioms slabObservableRecoupledTargetPair
#print axioms slabObservableRecoupledLeftEntry_physical
#print axioms slabObservableRecoupledRightEntry_physical
#print axioms faceSwapEntries_mem_fourCellTarget
#print axioms slabObservableRecoupledTargetPair_mem
#print axioms slabObservableRecouplingTargetRealization

end YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
