/-
# The reflected bent target as an observable recoupling choice

Embed the concrete connected `11 x 00` source and the complete reflected
target assignment into the observable recoupling row.  The local equal-rank
realizer agrees with the component-preserving auxiliary selector at every
link, including the exceptional pivot.

Constructive contract: source identification, finite target membership, and
local target faithfulness only; no choice, `Classical`, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetDisconnection

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice

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
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

structure ReflectedBentSwitchRecouplingSourcePackage : Type where
  source : SlabObservablePairedStrandRecouplingSource
    reflectedBentPhysicalData reflectedBentRootFaceId reflectedBentTargetFaceId
  sourcePair : source.1 = reflectedBentSourcePair
  leftPhysical : source.1.1.1.1 = reflectedBentSwitchLeftPhysical
  rightPhysical : source.1.2.1.1 = reflectedBentSwitchRightPhysical

opaque reflectedBentSwitchRecouplingSourcePackage :
    ReflectedBentSwitchRecouplingSourcePackage :=
  { source := ⟨reflectedBentSourcePair,
      reflectedBentSourcePair_mem_fourCell⟩
    sourcePair := rfl
    leftPhysical := rfl
    rightPhysical := rfl }

abbrev reflectedBentSwitchRecouplingSource :=
  reflectedBentSwitchRecouplingSourcePackage.source

theorem reflectedBentSwitchRecouplingSource_sourcePair :
    reflectedBentSwitchRecouplingSource.1 = reflectedBentSourcePair :=
  reflectedBentSwitchRecouplingSourcePackage.sourcePair

theorem reflectedBentSwitchRecouplingSource_leftPhysical :
    reflectedBentSwitchRecouplingSource.1.1.1.1 =
      reflectedBentSwitchLeftPhysical :=
  reflectedBentSwitchRecouplingSourcePackage.leftPhysical

theorem reflectedBentSwitchRecouplingSource_rightPhysical :
    reflectedBentSwitchRecouplingSource.1.2.1.1 =
      reflectedBentSwitchRightPhysical :=
  reflectedBentSwitchRecouplingSourcePackage.rightPhysical

abbrev ReflectedBentSwitchLinkedPackagesFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  linkedList.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink 5
      reflectedBentSwitchLeftPhysical
      reflectedBentSwitchRightPhysical linked

def reflectedBentSwitchPhysicalRecouplingChoiceFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    FiniteBistochasticTargetAssignment
      (ReflectedBentSwitchLinkedPackagesFrom linkedList) :=
  reflectedBentSwitchTargetAssignmentFrom linkedList

theorem reflectedBentSwitchRecouplingPackages_eq :
    slabPhysicalPairRecouplingPackages 5
        reflectedBentSwitchRecouplingSource.1.1.1.1
        reflectedBentSwitchRecouplingSource.1.2.1.1 =
      ReflectedBentSwitchLinkedPackagesFrom reflectedBentSwitchLinkedList := by
  rw [reflectedBentSwitchRecouplingSource_leftPhysical,
    reflectedBentSwitchRecouplingSource_rightPhysical]
  unfold slabPhysicalPairRecouplingPackages reflectedBentSwitchLinkedList
  rfl

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

def reflectedBentSwitchTargetMembershipPackageFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    TargetMembershipPackage
      (ReflectedBentSwitchLinkedPackagesFrom linkedList) :=
  { target := reflectedBentSwitchPhysicalRecouplingChoiceFrom linkedList
    target_mem := reflectedBentSwitchTargetAssignmentFrom_mem linkedList }

theorem reflectedBentSwitchTargetMembershipPackageFrom_target
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (reflectedBentSwitchTargetMembershipPackageFrom linkedList).target =
      reflectedBentSwitchPhysicalRecouplingChoiceFrom linkedList := rfl

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

def reflectedBentSwitchRecouplingChoicePackage :
    TransportedTargetPackage
      (slabPhysicalPairRecouplingPackages 5
        reflectedBentSwitchRecouplingSource.1.1.1.1
        reflectedBentSwitchRecouplingSource.1.2.1.1)
      (ReflectedBentSwitchLinkedPackagesFrom reflectedBentSwitchLinkedList)
      reflectedBentSwitchRecouplingPackages_eq :=
  transportedTargetPackage
    reflectedBentSwitchRecouplingPackages_eq
    (reflectedBentSwitchTargetMembershipPackageFrom
      reflectedBentSwitchLinkedList)

def reflectedBentSwitchPivotFineAnchor :
    SlabPhysicalPairRecouplingWitnessData 1
      reflectedBentSwitchPivotRecouplingData where
  leftAuxiliary := slabFusionWitnessAssignmentAt
    reflectedBentSwitchPivot reflectedBentLeftFineWitness.1
  rightAuxiliary := slabFusionWitnessAssignmentAt
    reflectedBentSwitchPivot reflectedBentRightFineWitness.1
  left_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    reflectedBentSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
    reflectedBentLeftFineWitness.1 reflectedBentSwitchLeftAssignment_mem
    reflectedBentSwitchPivot
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks
  right_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    reflectedBentSwitchRightPhysical (boundaryCompleteSlabLinks 5)
    reflectedBentRightFineWitness.1 reflectedBentSwitchRightAssignment_mem
    reflectedBentSwitchPivot
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks

theorem reflectedBentSwitchRealizedLeftAuxiliary_eq_localRealizedPair
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentSwitchRealizedLeftAuxiliary linked =
      (reflectedBentSwitchLocalRealizedPair linked).leftAuxiliary := by
  by_cases hpivot : linked.1 = reflectedBentSwitchPivot
  · rw [reflectedBentSwitchRealizedLeftAuxiliary_eq_pivot linked hpivot]
    cases linked with
    | mk link hlink =>
        dsimp at hpivot
        subst link
        unfold reflectedBentSwitchLocalRealizedPair
          reflectedBentSwitchLocalTarget
          reflectedBentSwitchLocalData
          reflectedBentSwitchLocalAnchor
          reflectedBentSwitchLocalSource
        have hdegree : 5 =
            (slabIncidentPlaqIds 5
              (⟨reflectedBentSwitchPivot, hlink⟩ :
                {link // link ∈ boundaryCompleteSlabLinks 5}).1).length := by
          simpa only using reflectedBentSwitchPivot_degree_five.symm
        cases hdegree
        change reflectedBentPivotLeftAuxiliary =
          (slabPhysicalPairTargetProductionWitnessPair
            reflectedBentSwitchPivotRecouplingData
            reflectedBentSwitchPivotFineAnchor
            reflectedBentSwitchLeftPhysical_bounded
            reflectedBentSwitchRightPhysical_bounded
            (reflectedBentSwitchTargetForData 5
              reflectedBentSwitchPivotRecouplingData rfl rfl
              (slabPhysicalPairRecouplingProductionSource 5
                reflectedBentSwitchPivotRecouplingData
                reflectedBentSwitchPivotFineAnchor))).leftAuxiliary
        rw [reflectedBentSwitchTargetForPivot_eq]
        exact (reflectedBentPivotTargetProduction_leftAuxiliary _).symm
  · unfold reflectedBentSwitchRealizedLeftAuxiliary
    rw [if_neg hpivot]

theorem reflectedBentSwitchRealizedLeftAssignmentFrom_eq_canonical :
    forall linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks 5},
    reflectedBentSwitchRealizedLeftAssignmentFrom linkedList =
      (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
        reflectedBentLeftFineWitness.1 reflectedBentRightFineWitness.1
        reflectedBentSwitchLeftAssignment_mem
        reflectedBentSwitchRightAssignment_mem
        reflectedBentSwitchLeftPhysical_bounded
        reflectedBentSwitchRightPhysical_bounded linkedList
        (reflectedBentSwitchPhysicalRecouplingChoiceFrom
          linkedList)).leftAssignment
  | [] => rfl
  | linked :: rest => by
      change
        (linked.1, reflectedBentSwitchRealizedLeftAuxiliary linked) ::
            reflectedBentSwitchRealizedLeftAssignmentFrom rest =
          (linked.1,
            (reflectedBentSwitchLocalRealizedPair linked).leftAuxiliary) ::
            (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
              reflectedBentSwitchLeftPhysical
              reflectedBentSwitchRightPhysical
              reflectedBentLeftFineWitness.1 reflectedBentRightFineWitness.1
              reflectedBentSwitchLeftAssignment_mem
              reflectedBentSwitchRightAssignment_mem
              reflectedBentSwitchLeftPhysical_bounded
              reflectedBentSwitchRightPhysical_bounded rest
              (reflectedBentSwitchPhysicalRecouplingChoiceFrom
                rest)).leftAssignment
      rw [reflectedBentSwitchRealizedLeftAuxiliary_eq_localRealizedPair,
        reflectedBentSwitchRealizedLeftAssignmentFrom_eq_canonical rest]

#print axioms reflectedBentSwitchRecouplingChoicePackage
#print axioms transportedTargetPackage_sourceTarget
#print axioms reflectedBentSwitchRealizedLeftAuxiliary_eq_localRealizedPair
#print axioms reflectedBentSwitchRealizedLeftAssignmentFrom_eq_canonical

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
