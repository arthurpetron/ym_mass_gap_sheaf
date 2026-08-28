/-
# The aligned target as an actual observable recoupling choice

Embed the concrete connected `11 x 00` source and the complete aligned target
assignment into the existing observable recoupling row.  The local equal-rank
realizer agrees with the explicit component-preserving auxiliary selector at
every link, including the exceptional pivot.

Constructive contract: definitional source identification, finite target
membership, and local target-faithfulness only; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetDisconnection

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetDisconnection
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Concrete source and target in the observable row -/

structure AlignedDiagonalSwitchRecouplingSourcePackage : Type where
  source : SlabObservablePairedStrandRecouplingSource
    alignedDiagonalSwitchPhysicalData
    alignedDiagonalSwitchRootFaceId
    alignedDiagonalSwitchTargetFaceId
  sourcePair : source.1 = alignedDiagonalSwitchSourcePair
  leftPhysical : source.1.1.1.1 = alignedDiagonalSwitchLeftPhysical
  rightPhysical : source.1.2.1.1 = alignedDiagonalSwitchRightPhysical

opaque alignedDiagonalSwitchRecouplingSourcePackage :
    AlignedDiagonalSwitchRecouplingSourcePackage :=
  { source := ⟨alignedDiagonalSwitchSourcePair,
      alignedDiagonalSwitchSourcePair_mem_fourCell⟩
    sourcePair := rfl
    leftPhysical := rfl
    rightPhysical := rfl }

abbrev alignedDiagonalSwitchRecouplingSource :=
  alignedDiagonalSwitchRecouplingSourcePackage.source

theorem alignedDiagonalSwitchRecouplingSource_sourcePair :
    alignedDiagonalSwitchRecouplingSource.1 =
      alignedDiagonalSwitchSourcePair :=
  alignedDiagonalSwitchRecouplingSourcePackage.sourcePair

theorem alignedDiagonalSwitchRecouplingSource_leftPhysical :
    alignedDiagonalSwitchRecouplingSource.1.1.1.1 =
      alignedDiagonalSwitchLeftPhysical := by
  exact alignedDiagonalSwitchRecouplingSourcePackage.leftPhysical

theorem alignedDiagonalSwitchRecouplingSource_rightPhysical :
    alignedDiagonalSwitchRecouplingSource.1.2.1.1 =
      alignedDiagonalSwitchRightPhysical := by
  exact alignedDiagonalSwitchRecouplingSourcePackage.rightPhysical

abbrev AlignedDiagonalSwitchLinkedPackagesFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  linkedList.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink 5
      alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchRightPhysical linked

def alignedDiagonalSwitchPhysicalRecouplingChoiceFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    FiniteBistochasticTargetAssignment
      (AlignedDiagonalSwitchLinkedPackagesFrom linkedList) :=
  alignedDiagonalSwitchTargetAssignmentFrom
    linkedList

theorem alignedDiagonalSwitchRecouplingPackages_eq :
    slabPhysicalPairRecouplingPackages 5
        alignedDiagonalSwitchRecouplingSource.1.1.1.1
        alignedDiagonalSwitchRecouplingSource.1.2.1.1 =
      AlignedDiagonalSwitchLinkedPackagesFrom
        alignedDiagonalSwitchLinkedList := by
  rw [alignedDiagonalSwitchRecouplingSource_leftPhysical,
    alignedDiagonalSwitchRecouplingSource_rightPhysical]
  unfold slabPhysicalPairRecouplingPackages
    alignedDiagonalSwitchLinkedList
  rfl

theorem transportFiniteBistochasticTargetAssignment_mem
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (target : FiniteBistochasticTargetAssignment right)
    (hmem : target ∈ finiteBistochasticTargetAssignments right) :
    transportFiniteBistochasticTargetAssignment hpackages target ∈
      finiteBistochasticTargetAssignments left := by
  cases hpackages
  exact hmem

structure TransportedTargetPackage
    (left right : List FiniteBistochasticQKernelPackage)
    (hpackages : left = right) : Type where
  sourceTarget : FiniteBistochasticTargetAssignment right
  sourceTarget_mem : sourceTarget ∈
    finiteBistochasticTargetAssignments right
  target : FiniteBistochasticTargetAssignment left
  target_mem : target ∈ finiteBistochasticTargetAssignments left
  target_eq : target =
    transportFiniteBistochasticTargetAssignment hpackages sourceTarget

structure TargetMembershipPackage
    (packages : List FiniteBistochasticQKernelPackage) : Type where
  target : FiniteBistochasticTargetAssignment packages
  target_mem : target ∈ finiteBistochasticTargetAssignments packages

def alignedDiagonalSwitchTargetMembershipPackageFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    TargetMembershipPackage
      (AlignedDiagonalSwitchLinkedPackagesFrom linkedList) :=
  { target := alignedDiagonalSwitchPhysicalRecouplingChoiceFrom linkedList
    target_mem := alignedDiagonalSwitchTargetAssignmentFrom_mem linkedList }

theorem alignedDiagonalSwitchTargetMembershipPackageFrom_target
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (alignedDiagonalSwitchTargetMembershipPackageFrom
      linkedList).target =
        alignedDiagonalSwitchPhysicalRecouplingChoiceFrom linkedList := rfl

def transportedTargetPackage
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (source : TargetMembershipPackage right) :
    TransportedTargetPackage left right hpackages := by
  cases hpackages
  exact
    { sourceTarget := source.target
      sourceTarget_mem := source.target_mem
      target := source.target
      target_mem := source.target_mem
      target_eq := rfl }

theorem transportedTargetPackage_sourceTarget
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (source : TargetMembershipPackage right) :
    (transportedTargetPackage hpackages source).sourceTarget =
      source.target := by
  cases hpackages
  rfl

def alignedDiagonalSwitchRecouplingChoicePackage :
    TransportedTargetPackage
      (slabPhysicalPairRecouplingPackages 5
        alignedDiagonalSwitchRecouplingSource.1.1.1.1
        alignedDiagonalSwitchRecouplingSource.1.2.1.1)
      (AlignedDiagonalSwitchLinkedPackagesFrom
        alignedDiagonalSwitchLinkedList)
      alignedDiagonalSwitchRecouplingPackages_eq :=
  transportedTargetPackage
    alignedDiagonalSwitchRecouplingPackages_eq
    (alignedDiagonalSwitchTargetMembershipPackageFrom
      alignedDiagonalSwitchLinkedList)

/-! ## 2. The explicit and canonical local realizers agree -/

def alignedDiagonalSwitchPivotFineAnchor :
    SlabPhysicalPairRecouplingWitnessData 1
      alignedDiagonalSwitchPivotRecouplingData where
  leftAuxiliary := slabFusionWitnessAssignmentAt
    alignedDiagonalSwitchPivot alignedDiagonalSwitchLeftFineWitness.1
  rightAuxiliary := slabFusionWitnessAssignmentAt
    alignedDiagonalSwitchPivot alignedDiagonalSwitchRightFineWitness.1
  left_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    alignedDiagonalSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
    alignedDiagonalSwitchLeftFineWitness.1
    alignedDiagonalSwitchLeftAssignment_mem
    alignedDiagonalSwitchPivot
    alignedDiagonalSwitchPivot_mem_boundaryCompleteSlabLinks
  right_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    alignedDiagonalSwitchRightPhysical (boundaryCompleteSlabLinks 5)
    alignedDiagonalSwitchRightFineWitness.1
    alignedDiagonalSwitchRightAssignment_mem
    alignedDiagonalSwitchPivot
    alignedDiagonalSwitchPivot_mem_boundaryCompleteSlabLinks

theorem alignedDiagonalSwitchRealizedLeftAuxiliary_eq_localRealizedPair
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    alignedDiagonalSwitchRealizedLeftAuxiliary linked =
      (alignedDiagonalSwitchLocalRealizedPair linked).leftAuxiliary := by
  by_cases hpivot : linked.1 = alignedDiagonalSwitchPivot
  · rw [alignedDiagonalSwitchRealizedLeftAuxiliary_eq_pivot linked hpivot]
    cases linked with
    | mk link hlink =>
        dsimp at hpivot
        subst link
        unfold alignedDiagonalSwitchLocalRealizedPair
          alignedDiagonalSwitchLocalTarget
          alignedDiagonalSwitchLocalData
          alignedDiagonalSwitchLocalAnchor
          alignedDiagonalSwitchLocalSource
        have hdegree : 5 =
            (slabIncidentPlaqIds 5
              (⟨alignedDiagonalSwitchPivot, hlink⟩ :
                {link // link ∈ boundaryCompleteSlabLinks 5}).1).length := by
          simpa only using alignedDiagonalSwitchPivot_degree_five.symm
        cases hdegree
        change alignedDiagonalPivotLeftAuxiliary =
          (slabPhysicalPairTargetProductionWitnessPair
            alignedDiagonalSwitchPivotRecouplingData
            alignedDiagonalSwitchPivotFineAnchor
            alignedDiagonalSwitchLeftPhysical_bounded
            alignedDiagonalSwitchRightPhysical_bounded
            (alignedDiagonalSwitchTargetForData 5
              alignedDiagonalSwitchPivotRecouplingData rfl rfl
              (slabPhysicalPairRecouplingProductionSource 5
                alignedDiagonalSwitchPivotRecouplingData
                alignedDiagonalSwitchPivotFineAnchor))).leftAuxiliary
        rw [alignedDiagonalSwitchTargetForPivot_eq]
        exact (alignedDiagonalPivotTargetProduction_leftAuxiliary _).symm
  · unfold alignedDiagonalSwitchRealizedLeftAuxiliary
    rw [if_neg hpivot]

theorem alignedDiagonalSwitchRealizedLeftAssignmentFrom_eq_canonical :
    forall linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks 5},
    alignedDiagonalSwitchRealizedLeftAssignmentFrom linkedList =
      (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
        alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchRightPhysical
        alignedDiagonalSwitchLeftFineWitness.1
        alignedDiagonalSwitchRightFineWitness.1
        alignedDiagonalSwitchLeftAssignment_mem
        alignedDiagonalSwitchRightAssignment_mem
        alignedDiagonalSwitchLeftPhysical_bounded
        alignedDiagonalSwitchRightPhysical_bounded
        linkedList
        (alignedDiagonalSwitchPhysicalRecouplingChoiceFrom
          linkedList)).leftAssignment
  | [] => rfl
  | linked :: rest => by
      change
        (linked.1, alignedDiagonalSwitchRealizedLeftAuxiliary linked) ::
            alignedDiagonalSwitchRealizedLeftAssignmentFrom rest =
          (linked.1,
            (alignedDiagonalSwitchLocalRealizedPair linked).leftAuxiliary) ::
            (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
              alignedDiagonalSwitchLeftPhysical
              alignedDiagonalSwitchRightPhysical
              alignedDiagonalSwitchLeftFineWitness.1
              alignedDiagonalSwitchRightFineWitness.1
              alignedDiagonalSwitchLeftAssignment_mem
              alignedDiagonalSwitchRightAssignment_mem
              alignedDiagonalSwitchLeftPhysical_bounded
              alignedDiagonalSwitchRightPhysical_bounded
              rest
              (alignedDiagonalSwitchPhysicalRecouplingChoiceFrom
                rest)).leftAssignment
      rw [alignedDiagonalSwitchRealizedLeftAuxiliary_eq_localRealizedPair,
        alignedDiagonalSwitchRealizedLeftAssignmentFrom_eq_canonical rest]

#print axioms alignedDiagonalSwitchRecouplingChoicePackage
#print axioms transportedTargetPackage_sourceTarget
#print axioms alignedDiagonalSwitchRealizedLeftAuxiliary_eq_localRealizedPair
#print axioms alignedDiagonalSwitchRealizedLeftAssignmentFrom_eq_canonical

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice
