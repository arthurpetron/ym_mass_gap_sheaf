/-
# Compile the reflected target into a retained contraction

The concrete observable source and the support-connected source are the same
underlying `11 x 00` pair.  Transport the successful target and its already
proved exact positive row weight across that source equality, insert the
resulting successful positive channel into the connected row, and feed it to
the existing retained-contraction compiler.

Constructive contract: subtype equality, dependent equality transport, exact
row-weight positivity, and existing retained-fraction compilers only; no
choice, `Classical`, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableReflectedPositiveChannelContraction
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservablePositiveMass

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservableReflectedPositiveChannelContraction
open YMGap.Continuum.CompactDualSlabObservableReflectedPositiveChannelContraction.SlabObservableReflectedPositiveChannel
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservablePositiveMass
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableSuccess
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-! ## 1. The two presentations have the same connected source -/

abbrev reflectedBentConnectedRecouplingSource :=
  YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.SlabObservablePairedConnectedStrandSource.toRecouplingSource
    reflectedBentConnectedStrandSource

theorem reflectedBentSwitchRecouplingSource_eq_connected :
    reflectedBentSwitchRecouplingSource =
      reflectedBentConnectedRecouplingSource := by
  apply Subtype.ext
  exact reflectedBentSwitchRecouplingSource_sourcePair

theorem reflectedBentConnectedSource_leftPhysical :
    reflectedBentConnectedStrandSource.1.1.1.1 =
      reflectedBentSwitchLeftPhysical := by
  change reflectedBentBinaryConnectedCarrier.leftPhysical =
    reflectedBentSwitchLeftPhysical
  exact reflectedBentCarrier_leftPhysical

theorem reflectedBentConnectedSource_rightPhysical :
    reflectedBentConnectedStrandSource.1.2.1.1 =
      reflectedBentSwitchRightPhysical := by
  change reflectedBentBinaryConnectedCarrier.rightPhysical =
    reflectedBentSwitchRightPhysical
  exact reflectedBentCarrier_rightPhysical

/-! ## 2. Transport the hidden positive target across source equality -/

structure ObservableConnectedPositivePackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool) : Type where
  package : ObservableVacuumDisconnectedTargetPackage
    D rootFaceId targetFaceId source
    referenceLeft referenceAssignment
    referenceProjectedEdges referenceVertices referenceAdjacent
  success : ObservableRecouplingSuccessCertificate
    D rootFaceId targetFaceId source
    referenceLeft referenceAssignment
    referenceProjectedEdges referenceVertices referenceAdjacent package
  positive : ObservablePositiveDisconnectionMassCertificate
    D rootFaceId targetFaceId source
    referenceLeft referenceRight referenceAssignment
    referenceProjectedEdges referenceVertices referenceAdjacent
    package success

def transportObservableConnectedPositivePackage
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {first second : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId}
    (hsource : first = second)
    (referenceLeft referenceRight : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (package : ObservableVacuumDisconnectedTargetPackage
      D rootFaceId targetFaceId first
      referenceLeft referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent)
    (success : ObservableRecouplingSuccessCertificate
      D rootFaceId targetFaceId first
      referenceLeft referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent package)
    (positive : ObservablePositiveDisconnectionMassCertificate
      D rootFaceId targetFaceId first
      referenceLeft referenceRight referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent
      package success) :
    ObservableConnectedPositivePackage
      D rootFaceId targetFaceId second
      referenceLeft referenceRight referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent := by
  cases hsource
  exact { package := package, success := success, positive := positive }

def reflectedBentConnectedPositivePackage :
    ObservableConnectedPositivePackage
      reflectedBentPhysicalData
      reflectedBentRootFaceId
      reflectedBentTargetFaceId
      reflectedBentConnectedRecouplingSource
      reflectedBentSwitchLeftPhysical
      reflectedBentSwitchRightPhysical
      reflectedBentTargetMeasureIndexAssignment
      reflectedBentMeasureProjectedFaceEdges
      reflectedBentMeasureFaceVertices
      reflectedBentMeasureFaceAdjacentB :=
  transportObservableConnectedPositivePackage
    reflectedBentSwitchRecouplingSource_eq_connected
    reflectedBentSwitchLeftPhysical
    reflectedBentSwitchRightPhysical
    reflectedBentTargetMeasureIndexAssignment
    reflectedBentMeasureProjectedFaceEdges
    reflectedBentMeasureFaceVertices
    reflectedBentMeasureFaceAdjacentB
    reflectedBentObservableVacuumDisconnectedTargetPackage
    reflectedBentObservableRecouplingSuccessCertificate
    reflectedBentObservablePositiveDisconnectionMassCertificate

/-! ## 3. Positive-row insertion and the retained contraction -/

def observablePairedConnectedPositiveChannelOfPackage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (referenceLeft referenceRight : SlabLabelling)
    (referenceAssignment : SlabFusionWitnessAssignment)
    (referenceProjectedEdges : List SlabProjectedFaceEdge)
    (referenceVertices : List Nat)
    (referenceAdjacent : Nat → Nat → Bool)
    (data : ObservableConnectedPositivePackage
      D rootFaceId targetFaceId source.toRecouplingSource
      referenceLeft referenceRight referenceAssignment
      referenceProjectedEdges referenceVertices referenceAdjacent) :
    SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId := by
  let successful : SlabObservablePairedStrandSuccessfulChoice
      D rootFaceId targetFaceId source.toRecouplingSource :=
    ⟨data.package.realized.choice, data.positive.successful_mem⟩
  refine
    { source := source
      choice := successful
      choice_mem := ?_ }
  unfold slabObservablePairedConnectedStrandChoices
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ successful, ?_⟩
  exact decide_eq_true (by
    simpa only [slabObservablePairedConnectedStrandWeight,
      slabObservablePairedStrandSuccessfulWeight, successful]
      using data.positive.choiceWeight_pos)

def reflectedBentPositiveChannelWitness :
    SlabObservablePairedConnectedPositiveChannelWitness
      reflectedBentPhysicalData
      reflectedBentRootFaceId
      reflectedBentTargetFaceId :=
  observablePairedConnectedPositiveChannelOfPackage
    reflectedBentPhysicalData
    reflectedBentRootFaceId
    reflectedBentTargetFaceId
    reflectedBentConnectedStrandSource
    reflectedBentSwitchLeftPhysical
    reflectedBentSwitchRightPhysical
    reflectedBentTargetMeasureIndexAssignment
    reflectedBentMeasureProjectedFaceEdges
    reflectedBentMeasureFaceVertices
    reflectedBentMeasureFaceAdjacentB
    reflectedBentConnectedPositivePackage

theorem reflectedBentPhysicalData_coupling_pos :
    (0 : Q') < reflectedBentPhysicalData.coupling := by decide

/-! ## 4. Exact reflection closes the same-object typing square -/

def reflectedBentReflectedPositiveChannel :
    SlabObservableReflectedPositiveChannel reflectedBentPhysicalData where
  rootFaceId := reflectedBentRootFaceId
  root_lower := reflectedBentRootFaceId_lower
  coupling_pos := reflectedBentPhysicalData_coupling_pos
  channel := by
    rw [← reflectedBentTargetFaceId_eq_reflect]
    exact reflectedBentPositiveChannelWitness

abbrev reflectedBentSameObjectRetainedFraction : Q' :=
  reflectedBentReflectedPositiveChannel.fraction

abbrev reflectedBentSameObjectContractionFactor : Q' :=
  reflectedBentReflectedPositiveChannel.factor

theorem reflectedBentSameObjectRetainedFraction_pos :
    (0 : Q') < reflectedBentSameObjectRetainedFraction :=
  reflectedBentReflectedPositiveChannel.fraction_pos

theorem reflectedBentSameObjectContractionFactor_nonnegative :
    (0 : Q') ≤ reflectedBentSameObjectContractionFactor :=
  reflectedBentReflectedPositiveChannel.factor_nonnegative

theorem reflectedBentSameObjectContractionFactor_lt_one :
    reflectedBentSameObjectContractionFactor < (1 : Q') :=
  reflectedBentReflectedPositiveChannel.factor_lt_one

theorem reflectedBentSameObjectConnectedMarkovMoment_le_factor :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        reflectedBentPhysicalData reflectedBentRootFaceId ≤
      reflectedBentSameObjectContractionFactor :=
  reflectedBentReflectedPositiveChannel.sameObjectConnectedMarkovMoment_le_factor

theorem reflectedBentSameObjectConnectedMarkovMoment_lt_one :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        reflectedBentPhysicalData reflectedBentRootFaceId < (1 : Q') :=
  reflectedBentReflectedPositiveChannel.sameObjectConnectedMarkovMoment_lt_one

#print axioms reflectedBentSwitchRecouplingSource_eq_connected
#print axioms reflectedBentConnectedPositivePackage
#print axioms reflectedBentPositiveChannelWitness
#print axioms reflectedBentReflectedPositiveChannel
#print axioms reflectedBentSameObjectContractionFactor_lt_one
#print axioms reflectedBentSameObjectConnectedMarkovMoment_le_factor
#print axioms reflectedBentSameObjectConnectedMarkovMoment_lt_one

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction
