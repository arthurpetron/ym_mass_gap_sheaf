/-
# The guarded positive target as an observable recoupling choice

Attach the selected finite target column to the literal guarded-graft
observable source.  The canonical observable realizer then returns both of
the already constructed accepted target assignments.  Retaining both sides
is necessary because the peeled right background is not globally vacuum.

Constructive contract: dependent target transport and structural list
recursion only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

/-! ## 1. The finite target in the observable package carrier -/

abbrev ReflectedBentGuardGraftLinkedPackagesFrom
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  linkedList.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state) linked

def reflectedBentGuardGraftTargetMembershipPackageFrom
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    TargetMembershipPackage
      (ReflectedBentGuardGraftLinkedPackagesFrom
        D hextent state linkedList) :=
  { target := reflectedBentGuardGraftTargetAssignmentFrom
      D hcutoff hextent state linkedList
    target_mem := reflectedBentGuardGraftTargetAssignmentFrom_mem
      D hcutoff hextent state linkedList }

theorem reflectedBentGuardGraftTargetMembershipPackageFrom_target
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (reflectedBentGuardGraftTargetMembershipPackageFrom
      D hcutoff hextent state linkedList).target =
        reflectedBentGuardGraftTargetAssignmentFrom
          D hcutoff hextent state linkedList := rfl

theorem reflectedBentGuardGraftObservableRecouplingPackages_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftObservableRecouplingSource
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftObservableRecouplingSource
          D hcutoff hextent state).1.2.1.1 =
      ReflectedBentGuardGraftLinkedPackagesFrom D hextent state
        (boundaryCompleteSlabLinks 5).attach := by
  rw [hextent,
    reflectedBentGuardGraftObservableRecouplingSource_leftPhysical,
    reflectedBentGuardGraftObservableRecouplingSource_rightPhysical]
  unfold slabPhysicalPairRecouplingPackages
    ReflectedBentGuardGraftLinkedPackagesFrom
  rfl

theorem reflectedBentGuardGraftReferenceRecouplingPackages_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state) =
      ReflectedBentGuardGraftLinkedPackagesFrom D hextent state
        (boundaryCompleteSlabLinks 5).attach := by
  rw [hextent]
  unfold slabPhysicalPairRecouplingPackages
    ReflectedBentGuardGraftLinkedPackagesFrom
  rfl

opaque reflectedBentGuardGraftObservableTargetPackage
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    TransportedTargetPackage
      (slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftObservableRecouplingSource
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftObservableRecouplingSource
          D hcutoff hextent state).1.2.1.1)
      (ReflectedBentGuardGraftLinkedPackagesFrom D hextent state
        (boundaryCompleteSlabLinks 5).attach)
      (reflectedBentGuardGraftObservableRecouplingPackages_eq
        D hcutoff hextent state) :=
  transportedTargetPackage
    (reflectedBentGuardGraftObservableRecouplingPackages_eq
      D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFrom
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach)

/-! ## 2. Structural equality with the classified realization -/

theorem reflectedBentGuardGraftRealizedAssignmentsFrom_eq_canonical
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      let canonical := slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        (reflectedBentGuardGraftLeftAssignment D hextent state)
        (reflectedBentGuardGraftRightAssignment D hextent state)
        (reflectedBentGuardGraftLeftAssignment_mem_five
          D hcutoff hextent state)
        (reflectedBentGuardGraftRightAssignment_mem_five
          D hcutoff hextent state)
        (reflectedBentGuardGraftLeftPhysical_bounded_five
          D hcutoff hextent state)
        (reflectedBentGuardGraftRightPhysical_bounded_five
          D hcutoff hextent state)
        linkedList
        (reflectedBentGuardGraftTargetAssignmentFrom
          D hcutoff hextent state linkedList)
      reflectedBentGuardGraftRealizedLeftAssignmentFrom
          D hcutoff hextent state linkedList = canonical.leftAssignment ∧
        reflectedBentGuardGraftRealizedRightAssignmentFrom
          D hcutoff hextent state linkedList = canonical.rightAssignment
  | [] => ⟨rfl, rfl⟩
  | linked :: rest => by
      have htail := reflectedBentGuardGraftRealizedAssignmentsFrom_eq_canonical
        D hcutoff hextent state rest
      change
        (linked.1,
            (reflectedBentGuardGraftLocalRealizedPair
              D hcutoff hextent state linked).leftAuxiliary) ::
              reflectedBentGuardGraftRealizedLeftAssignmentFrom
                D hcutoff hextent state rest =
          (linked.1,
            (reflectedBentGuardGraftLocalRealizedPair
              D hcutoff hextent state linked).leftAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                (reflectedBentGuardGraftLeftAssignment D hextent state)
                (reflectedBentGuardGraftRightAssignment D hextent state)
                (reflectedBentGuardGraftLeftAssignment_mem_five
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightAssignment_mem_five
                  D hcutoff hextent state)
                (reflectedBentGuardGraftLeftPhysical_bounded_five
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightPhysical_bounded_five
                  D hcutoff hextent state)
                rest
                (reflectedBentGuardGraftTargetAssignmentFrom
                  D hcutoff hextent state rest)).leftAssignment ∧
        (linked.1,
            (reflectedBentGuardGraftLocalRealizedPair
              D hcutoff hextent state linked).rightAuxiliary) ::
              reflectedBentGuardGraftRealizedRightAssignmentFrom
                D hcutoff hextent state rest =
          (linked.1,
            (reflectedBentGuardGraftLocalRealizedPair
              D hcutoff hextent state linked).rightAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
                (reflectedBentGuardGraftLeftPhysical D hextent state)
                (reflectedBentGuardGraftRightPhysical D hextent state)
                (reflectedBentGuardGraftLeftAssignment D hextent state)
                (reflectedBentGuardGraftRightAssignment D hextent state)
                (reflectedBentGuardGraftLeftAssignment_mem_five
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightAssignment_mem_five
                  D hcutoff hextent state)
                (reflectedBentGuardGraftLeftPhysical_bounded_five
                  D hcutoff hextent state)
                (reflectedBentGuardGraftRightPhysical_bounded_five
                  D hcutoff hextent state)
                rest
                (reflectedBentGuardGraftTargetAssignmentFrom
                  D hcutoff hextent state rest)).rightAssignment
      constructor
      · rw [htail.1]
      · rw [htail.2]

/-! ## 3. Transport to the literal observable anchor -/

theorem canonicalAnchor_realize_physicalTransport_assignments_eq
    {K extent : Nat}
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (firstLeftAssignment firstRightAssignment :
      SlabFusionWitnessAssignment)
    (firstLeft_mem : firstLeftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstRight_mem : firstRightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₁
        (boundaryCompleteSlabLinks extent))
    (firstLeftBounded : SlabFaceLabellingBounded K extent leftPhysical₁)
    (firstRightBounded : SlabFaceLabellingBounded K extent rightPhysical₁)
    (second : SlabPhysicalPairCanonicalAnchor K extent
      leftPhysical₂ rightPhysical₂)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₁ rightPhysical₁) :
    let realized := second.realize
      (transportSlabPhysicalPairRecouplingTargetAssignment
        hleft hright target)
    let first := slabPhysicalPairCanonicalTargetAssignmentsResult
      K extent leftPhysical₁ rightPhysical₁
      firstLeftAssignment firstRightAssignment
      firstLeft_mem firstRight_mem firstLeftBounded firstRightBounded target
    realized.leftAssignment = first.leftAssignment ∧
      realized.rightAssignment = first.rightAssignment := by
  cases hleft
  cases hright
  exact slabPhysicalPairCanonicalTargetAssignmentsResult_anchor_independent
    K extent leftPhysical₁ rightPhysical₁
    second.leftAssignment second.rightAssignment
    firstLeftAssignment firstRightAssignment
    second.left_mem second.right_mem firstLeft_mem firstRight_mem
    second.leftBounded second.rightBounded target

abbrev reflectedBentGuardGraftObservableChoice
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  (reflectedBentGuardGraftObservableTargetPackage
    D hcutoff hextent state).target

theorem reflectedBentGuardGraftObservableChoice_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftObservableChoice D hcutoff hextent state ∈
      slabObservablePairedStrandRecouplingChoices D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardGraftObservableRecouplingSource
          D hcutoff hextent state) :=
  (reflectedBentGuardGraftObservableTargetPackage
    D hcutoff hextent state).target_mem

/-! ## 4. The same column over the literal, unsealed source -/

theorem reflectedBentGuardGraftRawObservableRecouplingPackages_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftRawObservableRecouplingSource
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftRawObservableRecouplingSource
          D hcutoff hextent state).1.2.1.1 =
      ReflectedBentGuardGraftLinkedPackagesFrom D hextent state
        (boundaryCompleteSlabLinks 5).attach := by
  rw [hextent]
  unfold reflectedBentGuardGraftRawObservableRecouplingSource
    reflectedBentGuardGraftObservableSourcePair
  rw [reflectedBentGuardGraftLeftPositiveEntry_physical,
    reflectedBentGuardGraftRightExpandedEntry_physical]
  rfl

@[irreducible] def reflectedBentGuardGraftRawObservableChoice
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedStrandRecouplingChoice D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftRawObservableRecouplingSource
        D hcutoff hextent state) :=
  (transportedTargetPackage
    (reflectedBentGuardGraftRawObservableRecouplingPackages_eq
      D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFrom
      D hcutoff hextent state
      (boundaryCompleteSlabLinks 5).attach)).target

#print axioms reflectedBentGuardGraftObservableRecouplingPackages_eq
#print axioms reflectedBentGuardGraftReferenceRecouplingPackages_eq
#print axioms reflectedBentGuardGraftObservableTargetPackage
#print axioms reflectedBentGuardGraftRealizedAssignmentsFrom_eq_canonical
#print axioms reflectedBentGuardGraftObservableChoice_mem
#print axioms reflectedBentGuardGraftRawObservableRecouplingPackages_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
