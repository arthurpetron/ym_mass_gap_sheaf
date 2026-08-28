/-
# Compile the aligned target into a retained contraction

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

import YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservablePositiveMass

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabRetainedContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableGraphBridge
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservablePositiveMass
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabObservableSuccess
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. The two presentations have the same connected source -/

abbrev alignedDiagonalConnectedRecouplingSource :=
  YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning.SlabObservablePairedConnectedStrandSource.toRecouplingSource
    alignedDiagonalSwitchConnectedStrandSource

theorem alignedDiagonalSwitchRecouplingSource_eq_connected :
    alignedDiagonalSwitchRecouplingSource =
      alignedDiagonalConnectedRecouplingSource := by
  apply Subtype.ext
  exact alignedDiagonalSwitchRecouplingSource_sourcePair

theorem alignedDiagonalConnectedSource_leftPhysical :
    alignedDiagonalSwitchConnectedStrandSource.1.1.1.1 =
      alignedDiagonalSwitchLeftPhysical := by
  change alignedDiagonalBinaryConnectedCarrier.leftPhysical =
    alignedDiagonalSwitchLeftPhysical
  exact alignedDiagonalCarrier_leftPhysical

theorem alignedDiagonalConnectedSource_rightPhysical :
    alignedDiagonalSwitchConnectedStrandSource.1.2.1.1 =
      alignedDiagonalSwitchRightPhysical := by
  change alignedDiagonalBinaryConnectedCarrier.rightPhysical =
    alignedDiagonalSwitchRightPhysical
  exact alignedDiagonalCarrier_rightPhysical

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

def alignedDiagonalConnectedPositivePackage :
    ObservableConnectedPositivePackage
      alignedDiagonalSwitchPhysicalData
      alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId
      alignedDiagonalConnectedRecouplingSource
      alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchRightPhysical
      alignedDiagonalTargetMeasureIndexAssignment
      alignedDiagonalMeasureProjectedFaceEdges
      alignedDiagonalMeasureFaceVertices
      alignedDiagonalMeasureFaceAdjacentB :=
  transportObservableConnectedPositivePackage
    alignedDiagonalSwitchRecouplingSource_eq_connected
    alignedDiagonalSwitchLeftPhysical
    alignedDiagonalSwitchRightPhysical
    alignedDiagonalTargetMeasureIndexAssignment
    alignedDiagonalMeasureProjectedFaceEdges
    alignedDiagonalMeasureFaceVertices
    alignedDiagonalMeasureFaceAdjacentB
    alignedDiagonalObservableVacuumDisconnectedTargetPackage
    alignedDiagonalObservableRecouplingSuccessCertificate
    alignedDiagonalObservablePositiveDisconnectionMassCertificate

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

def alignedDiagonalPositiveChannelWitness :
    SlabObservablePairedConnectedPositiveChannelWitness
      alignedDiagonalSwitchPhysicalData
      alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId :=
  observablePairedConnectedPositiveChannelOfPackage
    alignedDiagonalSwitchPhysicalData
    alignedDiagonalSwitchRootFaceId
    alignedDiagonalSwitchTargetFaceId
    alignedDiagonalSwitchConnectedStrandSource
    alignedDiagonalSwitchLeftPhysical
    alignedDiagonalSwitchRightPhysical
    alignedDiagonalTargetMeasureIndexAssignment
    alignedDiagonalMeasureProjectedFaceEdges
    alignedDiagonalMeasureFaceVertices
    alignedDiagonalMeasureFaceAdjacentB
    alignedDiagonalConnectedPositivePackage

theorem alignedDiagonalSwitchPhysicalData_coupling_pos :
    (0 : Q') < alignedDiagonalSwitchPhysicalData.coupling := by decide

def alignedDiagonalSplitRetainedContraction :=
  slabObservablePairedSplitRetainedContraction
    alignedDiagonalSwitchPhysicalData
    alignedDiagonalSwitchPhysicalData_coupling_pos
    alignedDiagonalSwitchRootFaceId
    alignedDiagonalSwitchTargetFaceId
    alignedDiagonalSwitchTargetFaceId_physical
    alignedDiagonalPositiveChannelWitness

abbrev alignedDiagonalRetainedFraction : Q' :=
  alignedDiagonalSplitRetainedContraction.fraction

abbrev alignedDiagonalContractionFactor : Q' :=
  (1 : Q') + -alignedDiagonalRetainedFraction

theorem alignedDiagonalRetainedFraction_pos :
    (0 : Q') < alignedDiagonalRetainedFraction :=
  alignedDiagonalSplitRetainedContraction.fraction_pos

theorem alignedDiagonalContractionFactor_nonnegative :
    (0 : Q') ≤ alignedDiagonalContractionFactor :=
  alignedDiagonalSplitRetainedContraction.complement_nonnegative

theorem alignedDiagonalContractionFactor_lt_one :
    alignedDiagonalContractionFactor < (1 : Q') :=
  alignedDiagonalSplitRetainedContraction.complement_lt_one

theorem alignedDiagonalFaceBooleanCovariance_le_contractionFactor :
    slabObservableFaceBooleanCovariance
        alignedDiagonalSwitchPhysicalData
        alignedDiagonalSwitchRootFaceId
        alignedDiagonalSwitchTargetFaceId ≤
      alignedDiagonalContractionFactor :=
  alignedDiagonalSplitRetainedContraction.faceBooleanCovariance_le_complement

theorem alignedDiagonalFaceBooleanCovariance_lt_one :
    slabObservableFaceBooleanCovariance
        alignedDiagonalSwitchPhysicalData
        alignedDiagonalSwitchRootFaceId
        alignedDiagonalSwitchTargetFaceId < (1 : Q') :=
  alignedDiagonalSplitRetainedContraction.faceBooleanCovariance_lt_one

/-! ## 4. Honest boundary of this spatial witness -/

theorem alignedDiagonalSwitchRootFaceId_lower :
    alignedDiagonalSwitchRootFaceId ∈
      centralLowerFaceIds alignedDiagonalSwitchPhysicalData.half := by
  decide

theorem alignedDiagonalSwitchTargetFaceId_lower :
    alignedDiagonalSwitchTargetFaceId ∈
      centralLowerFaceIds alignedDiagonalSwitchPhysicalData.half := by
  decide

theorem alignedDiagonalSwitchTargetFaceId_ne_reflected :
    alignedDiagonalSwitchTargetFaceId ≠
      slabFaceReflectId alignedDiagonalSwitchPhysicalData.extent
        alignedDiagonalSwitchRootFaceId := by
  decide

#print axioms alignedDiagonalSwitchRecouplingSource_eq_connected
#print axioms alignedDiagonalConnectedPositivePackage
#print axioms alignedDiagonalPositiveChannelWitness
#print axioms alignedDiagonalSplitRetainedContraction
#print axioms alignedDiagonalContractionFactor_lt_one
#print axioms alignedDiagonalFaceBooleanCovariance_le_contractionFactor
#print axioms alignedDiagonalFaceBooleanCovariance_lt_one
#print axioms alignedDiagonalSwitchRootFaceId_lower
#print axioms alignedDiagonalSwitchTargetFaceId_ne_reflected

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabRetainedContraction
