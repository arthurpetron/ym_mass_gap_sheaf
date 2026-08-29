/-
# The two-pivot repair target as an observable recoupling choice

Embed the concrete connected `11 x 00` source and the complete two-pivot
target assignment into the observable recoupling row.  The generic
equal-rank realizer agrees with the explicitly selected component-preserving
auxiliary at both exceptional pivots and with the ordinary local realizer
everywhere else.

Constructive contract: source identification, finite target membership, and
local target faithfulness only; no choice, `Classical`, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetDisconnection
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabWholeProductPositivity

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabObservableChoice

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotTarget
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetAssignment
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetEdges
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetRealization
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabWholeProductPositivity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice

/-! ## 1. The literal observable source -/

structure OutwardYZCanonicalRepairRecouplingSourcePackage : Type where
  source : SlabObservablePairedStrandRecouplingSource
    outwardYZCanonicalRepairPhysicalData
    outwardYZCanonicalRepairRootFaceId
    outwardYZCanonicalRepairTargetFaceId
  sourcePair : source.1 = outwardYZCanonicalRepairSourcePair
  leftPhysical : source.1.1.1.1 =
    outwardYZCanonicalRepairSwitchLeftPhysical
  rightPhysical : source.1.2.1.1 =
    outwardYZCanonicalRepairSwitchRightPhysical

opaque outwardYZCanonicalRepairRecouplingSourcePackage :
    OutwardYZCanonicalRepairRecouplingSourcePackage :=
  { source := ⟨outwardYZCanonicalRepairSourcePair,
      outwardYZCanonicalRepairSourcePair_mem_fourCell⟩
    sourcePair := rfl
    leftPhysical := rfl
    rightPhysical := rfl }

abbrev outwardYZCanonicalRepairRecouplingSource :=
  outwardYZCanonicalRepairRecouplingSourcePackage.source

theorem outwardYZCanonicalRepairRecouplingSource_sourcePair :
    outwardYZCanonicalRepairRecouplingSource.1 =
      outwardYZCanonicalRepairSourcePair :=
  outwardYZCanonicalRepairRecouplingSourcePackage.sourcePair

theorem outwardYZCanonicalRepairRecouplingSource_leftPhysical :
    outwardYZCanonicalRepairRecouplingSource.1.1.1.1 =
      outwardYZCanonicalRepairSwitchLeftPhysical :=
  outwardYZCanonicalRepairRecouplingSourcePackage.leftPhysical

theorem outwardYZCanonicalRepairRecouplingSource_rightPhysical :
    outwardYZCanonicalRepairRecouplingSource.1.2.1.1 =
      outwardYZCanonicalRepairSwitchRightPhysical :=
  outwardYZCanonicalRepairRecouplingSourcePackage.rightPhysical

/-! ## 2. The finite target package -/

abbrev OutwardYZCanonicalRepairLinkedPackagesFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  linkedList.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked

def outwardYZCanonicalRepairPhysicalRecouplingChoiceFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    FiniteBistochasticTargetAssignment
      (OutwardYZCanonicalRepairLinkedPackagesFrom linkedList) :=
  outwardYZCanonicalRepairTargetAssignmentFrom linkedList

theorem outwardYZCanonicalRepairRecouplingPackages_eq :
    slabPhysicalPairRecouplingPackages 5
        outwardYZCanonicalRepairRecouplingSource.1.1.1.1
        outwardYZCanonicalRepairRecouplingSource.1.2.1.1 =
      OutwardYZCanonicalRepairLinkedPackagesFrom
        outwardYZCanonicalRepairSwitchLinkedList := by
  rw [outwardYZCanonicalRepairRecouplingSource_leftPhysical,
    outwardYZCanonicalRepairRecouplingSource_rightPhysical]
  unfold slabPhysicalPairRecouplingPackages
    outwardYZCanonicalRepairSwitchLinkedList
  rfl

def outwardYZCanonicalRepairTargetMembershipPackageFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    TargetMembershipPackage
      (OutwardYZCanonicalRepairLinkedPackagesFrom linkedList) :=
  { target := outwardYZCanonicalRepairPhysicalRecouplingChoiceFrom linkedList
    target_mem :=
      outwardYZCanonicalRepairTargetAssignmentFrom_mem linkedList }

theorem outwardYZCanonicalRepairTargetMembershipPackageFrom_target
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (outwardYZCanonicalRepairTargetMembershipPackageFrom linkedList).target =
      outwardYZCanonicalRepairPhysicalRecouplingChoiceFrom linkedList := rfl

/-! ## 3. Exact local realization at both pivots -/

def outwardYZCanonicalRepairSpatialFineAnchor :
    SlabPhysicalPairRecouplingWitnessData 1
      outwardYZCanonicalRepairSpatialPivotRecouplingData where
  leftAuxiliary := slabFusionWitnessAssignmentAt
    outwardYZCanonicalRepairSwitchSpatialPivot
    outwardYZCanonicalRepairLeftFineWitness.1
  rightAuxiliary := slabFusionWitnessAssignmentAt
    outwardYZCanonicalRepairSwitchSpatialPivot
    outwardYZCanonicalRepairRightFineWitness.1
  left_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    (boundaryCompleteSlabLinks 5)
    outwardYZCanonicalRepairLeftFineWitness.1
    outwardYZCanonicalRepairSwitchLeftAssignment_mem
    outwardYZCanonicalRepairSwitchSpatialPivot
    outwardYZCanonicalRepairSpatialPivot_mem_boundaryCompleteSlabLinks
  right_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    outwardYZCanonicalRepairSwitchRightPhysical
    (boundaryCompleteSlabLinks 5)
    outwardYZCanonicalRepairRightFineWitness.1
    outwardYZCanonicalRepairSwitchRightAssignment_mem
    outwardYZCanonicalRepairSwitchSpatialPivot
    outwardYZCanonicalRepairSpatialPivot_mem_boundaryCompleteSlabLinks

def outwardYZCanonicalRepairTemporalFineAnchor :
    SlabPhysicalPairRecouplingWitnessData 1
      outwardYZCanonicalRepairTemporalPivotRecouplingData where
  leftAuxiliary := slabFusionWitnessAssignmentAt
    outwardYZCanonicalRepairSwitchTemporalPivot
    outwardYZCanonicalRepairLeftFineWitness.1
  rightAuxiliary := slabFusionWitnessAssignmentAt
    outwardYZCanonicalRepairSwitchTemporalPivot
    outwardYZCanonicalRepairRightFineWitness.1
  left_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    (boundaryCompleteSlabLinks 5)
    outwardYZCanonicalRepairLeftFineWitness.1
    outwardYZCanonicalRepairSwitchLeftAssignment_mem
    outwardYZCanonicalRepairSwitchTemporalPivot
    outwardYZCanonicalRepairTemporalPivot_mem_boundaryCompleteSlabLinks
  right_mem := slabFusionWitnessAssignmentAt_mem_local 1 5
    outwardYZCanonicalRepairSwitchRightPhysical
    (boundaryCompleteSlabLinks 5)
    outwardYZCanonicalRepairRightFineWitness.1
    outwardYZCanonicalRepairSwitchRightAssignment_mem
    outwardYZCanonicalRepairSwitchTemporalPivot
    outwardYZCanonicalRepairTemporalPivot_mem_boundaryCompleteSlabLinks

theorem outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_localRealizedPair
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    outwardYZCanonicalRepairRealizedLeftAuxiliary linked =
      (outwardYZCanonicalRepairLocalRealizedPair linked).leftAuxiliary := by
  by_cases hspatial :
      linked.1 = outwardYZCanonicalRepairSwitchSpatialPivot
  · rw [outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_spatial
      linked hspatial]
    cases linked with
    | mk link hlink =>
        dsimp at hspatial
        subst link
        unfold outwardYZCanonicalRepairLocalRealizedPair
          outwardYZCanonicalRepairLocalTarget
          outwardYZCanonicalRepairLocalData
          outwardYZCanonicalRepairLocalAnchor
          outwardYZCanonicalRepairLocalSource
        have hdegree : 5 =
            (slabIncidentPlaqIds 5
              (⟨outwardYZCanonicalRepairSwitchSpatialPivot, hlink⟩ :
                {link // link ∈ boundaryCompleteSlabLinks 5}).1).length := by
          simpa only using
            outwardYZCanonicalRepairSwitchSpatialPivot_degree_five.symm
        cases hdegree
        change outwardYZCanonicalRepairSpatialLeftAuxiliary =
          (slabPhysicalPairTargetProductionWitnessPair
            outwardYZCanonicalRepairSpatialPivotRecouplingData
            outwardYZCanonicalRepairSpatialFineAnchor
            outwardYZCanonicalRepairSwitchLeftPhysical_bounded
            outwardYZCanonicalRepairSwitchRightPhysical_bounded
            (outwardYZCanonicalRepairTargetForData 5
              outwardYZCanonicalRepairSpatialPivotRecouplingData rfl rfl
              (slabPhysicalPairRecouplingProductionSource 5
                outwardYZCanonicalRepairSpatialPivotRecouplingData
                outwardYZCanonicalRepairSpatialFineAnchor))).leftAuxiliary
        rw [outwardYZCanonicalRepairTargetForSpatialPivot_eq]
        exact
          (outwardYZCanonicalRepairSpatialTargetProduction_leftAuxiliary
            outwardYZCanonicalRepairSpatialFineAnchor
            outwardYZCanonicalRepairSwitchRightPhysical_bounded).symm
  · by_cases htemporal :
        linked.1 = outwardYZCanonicalRepairSwitchTemporalPivot
    · rw [outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_temporal
        linked htemporal]
      cases linked with
      | mk link hlink =>
          dsimp at hspatial htemporal
          subst link
          unfold outwardYZCanonicalRepairLocalRealizedPair
            outwardYZCanonicalRepairLocalTarget
            outwardYZCanonicalRepairLocalData
            outwardYZCanonicalRepairLocalAnchor
            outwardYZCanonicalRepairLocalSource
          have hdegree : 5 =
              (slabIncidentPlaqIds 5
                (⟨outwardYZCanonicalRepairSwitchTemporalPivot, hlink⟩ :
                  {link // link ∈ boundaryCompleteSlabLinks 5}).1).length := by
            simpa only using
              outwardYZCanonicalRepairSwitchTemporalPivot_degree_five.symm
          cases hdegree
          change outwardYZCanonicalRepairTemporalLeftAuxiliary =
            (slabPhysicalPairTargetProductionWitnessPair
              outwardYZCanonicalRepairTemporalPivotRecouplingData
              outwardYZCanonicalRepairTemporalFineAnchor
              outwardYZCanonicalRepairSwitchLeftPhysical_bounded
              outwardYZCanonicalRepairSwitchRightPhysical_bounded
              (outwardYZCanonicalRepairTargetForData 5
                outwardYZCanonicalRepairTemporalPivotRecouplingData rfl rfl
                (slabPhysicalPairRecouplingProductionSource 5
                  outwardYZCanonicalRepairTemporalPivotRecouplingData
                  outwardYZCanonicalRepairTemporalFineAnchor))).leftAuxiliary
          rw [outwardYZCanonicalRepairTargetForTemporalPivot_eq]
          exact
            (outwardYZCanonicalRepairTemporalTargetProduction_leftAuxiliary
              outwardYZCanonicalRepairTemporalFineAnchor
              outwardYZCanonicalRepairSwitchRightPhysical_bounded).symm
    · unfold outwardYZCanonicalRepairRealizedLeftAuxiliary
      rw [if_neg hspatial, if_neg htemporal]

/-! ## 4. Structural agreement with the canonical global realizer -/

theorem outwardYZCanonicalRepairRealizedLeftAssignmentFrom_eq_canonical :
    ∀ linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks 5},
    outwardYZCanonicalRepairRealizedLeftAssignmentFrom linkedList =
      (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchRightPhysical
        outwardYZCanonicalRepairLeftFineWitness.1
        outwardYZCanonicalRepairRightFineWitness.1
        outwardYZCanonicalRepairSwitchLeftAssignment_mem
        outwardYZCanonicalRepairSwitchRightAssignment_mem
        outwardYZCanonicalRepairSwitchLeftPhysical_bounded
        outwardYZCanonicalRepairSwitchRightPhysical_bounded linkedList
        (outwardYZCanonicalRepairPhysicalRecouplingChoiceFrom
          linkedList)).leftAssignment
  | [] => rfl
  | linked :: rest => by
      change
        (linked.1, outwardYZCanonicalRepairRealizedLeftAuxiliary linked) ::
            outwardYZCanonicalRepairRealizedLeftAssignmentFrom rest =
          (linked.1,
            (outwardYZCanonicalRepairLocalRealizedPair linked).leftAuxiliary) ::
            (slabPhysicalPairCanonicalTargetAssignmentsFrom 1 5
              outwardYZCanonicalRepairSwitchLeftPhysical
              outwardYZCanonicalRepairSwitchRightPhysical
              outwardYZCanonicalRepairLeftFineWitness.1
              outwardYZCanonicalRepairRightFineWitness.1
              outwardYZCanonicalRepairSwitchLeftAssignment_mem
              outwardYZCanonicalRepairSwitchRightAssignment_mem
              outwardYZCanonicalRepairSwitchLeftPhysical_bounded
              outwardYZCanonicalRepairSwitchRightPhysical_bounded rest
              (outwardYZCanonicalRepairPhysicalRecouplingChoiceFrom
                rest)).leftAssignment
      rw [outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_localRealizedPair,
        outwardYZCanonicalRepairRealizedLeftAssignmentFrom_eq_canonical rest]

#print axioms outwardYZCanonicalRepairRecouplingSourcePackage
#print axioms outwardYZCanonicalRepairTargetMembershipPackageFrom
#print axioms outwardYZCanonicalRepairRealizedLeftAuxiliary_eq_localRealizedPair
#print axioms outwardYZCanonicalRepairRealizedLeftAssignmentFrom_eq_canonical

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabObservableChoice
