/-
# Factor saturated receiver coverage through one-replica raw endpoint lifts

The assignment-saturated receiver image forgets accepted coarse auxiliary
assignments, but it still asks whether each physical coarse endpoint occurs
in a strictly positive cutoff-one whole-slab raw row.  This module isolates
that remaining task at one replica.

A `PositiveExpandedRawEndpointCoverage` supplies, for every physical coarse
labelling, one enumerated positive expanded fine source whose literal
whole-slab raw transition to that labelling is strictly positive.  Two such
lifts assemble constructively into each source or opposite four-cell path.
It follows that every assignment-saturated receiver is covered and the
unreachable source-plus-target mass is exactly zero.

The matched-AF adapter consequently removes the unreachable-mass analytic
field entirely, conditional only on this explicit finite raw-support
coverage at every scale.  The separate covered-calibration, spacing, and raw
mismatch estimates remain unchanged and uninhabited.

No endpoint lift is constructed here.  In particular, the existing
fine-to-coarse parity target provides one positive target per fine row, not
the reverse lift for every coarse target required below.  This is a finite
exact reduction, not a cutoff-uniform contraction, continuum construction,
OS/GNS reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: proof-carrying finite members, Boolean support, and
exact rational inequalities only; no choice, `Classical`, `native_decide`,
proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPositiveOccupationQuadraticCost

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance endpointLiftPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

/-! ## 1. One-replica positive raw endpoint coverage -/

/-- One enumerated positive expanded fine source with a strictly positive
literal raw transition to the selected physical coarse endpoint. -/
structure PositiveExpandedRawEndpointLift
    (S : SlabScalePair) (coarseTarget : EdgeLabelling) : Type where
  source : PositiveExpandedPhysicalSource S
  source_mem : source ∈ positiveExpandedPhysicalSources S
  rawWeight_pos :
    (0 : Q') < wholeSlabRecouplingRawWeight
      S source.1.1 coarseTarget

/-- The remaining finite combinatorial coverage target: every physical
coarse labelling has a positive raw preimage in the enumerated fine carrier. -/
structure PositiveExpandedRawEndpointCoverage (S : SlabScalePair) : Type where
  lift : ∀ coarseTarget : EdgeLabelling,
    coarseTarget ∈ S.coarse.physicalLabellings →
      PositiveExpandedRawEndpointLift S coarseTarget

/-! ## 2. Assemble two one-replica lifts into supported four-cell paths -/

private theorem sourceReceiver_physicalPair_mem
    {S : SlabScalePair} {root target : Nat}
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellSourcePairs S.coarse root target) :
    (receiver.1.1.1, receiver.2.1.1) ∈
      pushedFaceRawFourCellSourcePairs (S := S) root target := by
  have hcells := (mem_cartesian_iff _ _ receiver).mp hreceiver
  apply (mem_cartesian_iff _ _
    (receiver.1.1.1, receiver.2.1.1)).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp
      receiver.1.source_mem_expanded).1, ?_⟩
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · unfold slabPhysicalFacePositiveB
      exact decide_eq_true receiver.1.source_positive
    · simpa only [SlabObservablePositiveSourceEntry.facePositiveB,
        slabPhysicalFacePositiveB] using
        (List.mem_filter.mp hcells.1).2
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp receiver.2.2).1, ?_⟩
    simpa only [SlabExpandedFineSourceEntry.facePositiveB,
      slabPhysicalFacePositiveB] using
      (List.mem_filter.mp hcells.2).2

private theorem targetReceiver_swappedPhysicalPair_mem
    {S : SlabScalePair} {root target : Nat}
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellTargetPairs S.coarse root target) :
    (receiver.2.1.1, receiver.1.1.1) ∈
      pushedFaceRawFourCellTargetPairs (S := S) root target := by
  have hcells := (mem_cartesian_iff _ _ receiver).mp hreceiver
  apply (mem_cartesian_iff _ _
    (receiver.2.1.1, receiver.1.1.1)).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp receiver.2.2).1, ?_⟩
    simpa only [SlabExpandedFineSourceEntry.facePositiveB,
      slabPhysicalFacePositiveB, Bool.and_comm] using
      (List.mem_filter.mp hcells.2).2
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp
      receiver.1.source_mem_expanded).1, ?_⟩
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · unfold slabPhysicalFacePositiveB
      exact decide_eq_true receiver.1.source_positive
    · simpa only [SlabObservablePositiveSourceEntry.facePositiveB,
        slabPhysicalFacePositiveB] using
        (List.mem_filter.mp hcells.1).2

/-- Two one-replica endpoint lifts construct an enumerated supported source
path whose physical receiver endpoints are the requested pair. -/
def positiveExpandedFourCellSourceSupportedPathAtReceiver
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellSourcePairs S.coarse root target) :
    {supported : PositiveExpandedFourCellSourceSupportedPath S root target //
      supported ∈ positiveExpandedFourCellSourceSupportedPaths
        S root target} := by
  let leftPhysical := receiver.1.1.1
  let rightPhysical := receiver.2.1.1
  have hphysicalPair := sourceReceiver_physicalPair_mem receiver hreceiver
  have hphysical := (mem_cartesian_iff _ _
    (leftPhysical, rightPhysical)).mp hphysicalPair
  let leftLift := coverage.lift leftPhysical
    (List.mem_filter.mp hphysical.1).1
  let rightLift := coverage.lift rightPhysical
    (List.mem_filter.mp hphysical.2).1
  let path : PositiveExpandedPushedPhysicalTwoReplicaPath S :=
    ((leftPhysical, rightPhysical), (leftLift.source, rightLift.source))
  have hsourcePair : (leftLift.source, rightLift.source) ∈
      positiveExpandedPhysicalSourcePairs S := by
    apply (mem_cartesian_iff _ _ _).mpr
    exact ⟨leftLift.source_mem, rightLift.source_mem⟩
  have hpath : path ∈
      positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target := by
    apply (mem_cartesian_iff _ _ path).mpr
    exact ⟨hphysicalPair, hsourcePair⟩
  have hsupport : positiveExpandedPathRawSupportedB S path = true := by
    unfold positiveExpandedPathRawSupportedB
    apply (Bool.and_eq_true _ _).mpr
    exact ⟨decide_eq_true leftLift.rawWeight_pos,
      decide_eq_true rightLift.rawWeight_pos⟩
  have hfiltered : path ∈
      (positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target).filter (positiveExpandedPathRawSupportedB S) :=
    List.mem_filter.mpr ⟨hpath, hsupport⟩
  let item : {candidate // candidate ∈
      (positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target).filter (positiveExpandedPathRawSupportedB S)} :=
    ⟨path, hfiltered⟩
  let supported := positiveExpandedFourCellSourceSupportedPathOfAttached
    S root target item
  refine ⟨supported, ?_⟩
  unfold positiveExpandedFourCellSourceSupportedPaths
  apply List.mem_map.mpr
  exact ⟨item, List.mem_attach _ _, rfl⟩

/-- The analogous two lifts construct the swapped supported path used by the
opposite target-cell receiver orientation. -/
def positiveExpandedFourCellTargetSupportedPathAtReceiver
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellTargetPairs S.coarse root target) :
    {supported : PositiveExpandedFourCellTargetSupportedPath S root target //
      supported ∈ positiveExpandedFourCellTargetSupportedPaths
        S root target} := by
  let leftPhysical := receiver.2.1.1
  let rightPhysical := receiver.1.1.1
  have hphysicalPair :=
    targetReceiver_swappedPhysicalPair_mem receiver hreceiver
  have hphysical := (mem_cartesian_iff _ _
    (leftPhysical, rightPhysical)).mp hphysicalPair
  let leftLift := coverage.lift leftPhysical
    (List.mem_filter.mp hphysical.1).1
  let rightLift := coverage.lift rightPhysical
    (List.mem_filter.mp hphysical.2).1
  let path : PositiveExpandedPushedPhysicalTwoReplicaPath S :=
    ((leftPhysical, rightPhysical), (leftLift.source, rightLift.source))
  have hsourcePair : (leftLift.source, rightLift.source) ∈
      positiveExpandedPhysicalSourcePairs S := by
    apply (mem_cartesian_iff _ _ _).mpr
    exact ⟨leftLift.source_mem, rightLift.source_mem⟩
  have hpath : path ∈
      positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target := by
    apply (mem_cartesian_iff _ _ path).mpr
    exact ⟨hphysicalPair, hsourcePair⟩
  have hsupport : positiveExpandedPathRawSupportedB S path = true := by
    unfold positiveExpandedPathRawSupportedB
    apply (Bool.and_eq_true _ _).mpr
    exact ⟨decide_eq_true leftLift.rawWeight_pos,
      decide_eq_true rightLift.rawWeight_pos⟩
  have hfiltered : path ∈
      (positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target).filter (positiveExpandedPathRawSupportedB S) :=
    List.mem_filter.mpr ⟨hpath, hsupport⟩
  let item : {candidate // candidate ∈
      (positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target).filter (positiveExpandedPathRawSupportedB S)} :=
    ⟨path, hfiltered⟩
  let supported := positiveExpandedFourCellTargetSupportedPathOfAttached
    S root target item
  refine ⟨supported, ?_⟩
  unfold positiveExpandedFourCellTargetSupportedPaths
  apply List.mem_map.mpr
  exact ⟨item, List.mem_attach _ _, rfl⟩

/-! ## 3. Full assignment-saturated coverage and zero unreachable mass -/

theorem sourceReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellSourcePairs S.coarse root target) :
    receiver ∈
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target := by
  let lift := positiveExpandedFourCellSourceSupportedPathAtReceiver
    coverage receiver hreceiver
  apply
    (mem_positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage_iff_physical
      S root target receiver).mpr
  exact ⟨lift.1, lift.2, rfl, rfl⟩

theorem targetReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellTargetPairs S.coarse root target) :
    receiver ∈
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target := by
  let lift := positiveExpandedFourCellTargetSupportedPathAtReceiver
    coverage receiver hreceiver
  apply
    (mem_positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage_iff_physical
      S root target receiver).mpr
  exact ⟨lift.1, lift.2, rfl, rfl⟩

private theorem complementFilter_eq_nil_of_subset
    {A : Type} [DecidableEq A] (image : List A) :
    ∀ items : List A,
      (∀ item, item ∈ items → item ∈ image) →
      items.filter (fun item => !(decide (item ∈ image))) = []
  | [], _ => rfl
  | head :: tail, hsubset => by
      have hhead : head ∈ image :=
        hsubset head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → item ∈ image :=
        fun item hitem =>
          hsubset item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, decide_eq_true hhead, Bool.not_true,
        Bool.false_eq_true, if_false]
      exact complementFilter_eq_nil_of_subset image tail htail

/-- Universal one-replica raw endpoint lifts make the physical unreachable
receiver mass exactly zero. -/
theorem actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_eqv_zero_of_endpointCoverage
    (S : SlabScalePair) (root target : Nat)
    (coverage : PositiveExpandedRawEndpointCoverage S) :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
        S root target ≈ 0 := by
  have hsource :
      (slabObservableFourCellSourcePairs S.coarse root target).filter
          (fun receiver => !(decide
            (receiver ∈
              positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
                S root target))) = [] :=
    complementFilter_eq_nil_of_subset
      (positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target)
      (slabObservableFourCellSourcePairs S.coarse root target)
      (fun receiver hreceiver =>
        sourceReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
          coverage receiver hreceiver)
  have htarget :
      (slabObservableFourCellTargetPairs S.coarse root target).filter
          (fun receiver => !(decide
            (receiver ∈
              positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
                S root target))) = [] :=
    complementFilter_eq_nil_of_subset
      (positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target)
      (slabObservableFourCellTargetPairs S.coarse root target)
      (fun receiver hreceiver =>
        targetReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
          coverage receiver hreceiver)
  unfold actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
    actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
    actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
  rw [hsource, htarget]
  exact Q'.eqv_of_eq (Q'.zero_add' 0)

theorem actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_of_endpointCoverage
    (S : SlabScalePair) (root target : Nat)
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (budget : Q') (hbudget : (0 : Q') ≤ budget) :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
        S root target ≤ budget := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_eqv_zero_of_endpointCoverage
        S root target coverage))
    hbudget

/-! ## 4. Matched-AF exact-coverage compiler -/

/-- Producer-facing matched-AF inputs when finite endpoint raw-support
coverage has been constructed at every scale. -/
structure MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  coveredVariationQuadraticCeiling : Q'
  coveredVariationQuadraticCeiling_pos :
    (0 : Q') < coveredVariationQuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  coveredVariation_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (coveredVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
  endpointCoverage : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    PositiveExpandedRawEndpointCoverage (schedule.scalePair scale)

namespace MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {C : AFTrajectoryCertificate}
    {coupling : Nat → Q'}
    {coupling_pos : ∀ scale, (0 : Q') < coupling scale}
    {coupling_le_window : ∀ scale, coupling scale ≤ law.g₁}
    {identification : ShiftedAFTrajectoryIdentification C coupling}
    {nested : NestedCutoffOneFaceGeometry}

/-- Exact endpoint coverage supplies a zero unreachable mass; coefficient
one is a harmless positive ceiling required by the downstream interface. -/
def toCoveredVariationUnreachableMassQuadraticCostControl
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  coveredVariationQuadraticCeiling :=
    control.coveredVariationQuadraticCeiling
  coveredVariationQuadraticCeiling_pos :=
    control.coveredVariationQuadraticCeiling_pos
  unreachableMassQuadraticCeiling := 1
  unreachableMassQuadraticCeiling_pos := by decide
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  coveredVariation_quadratic_le := control.coveredVariation_quadratic_le
  unreachableMass_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    apply
      actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_of_endpointCoverage
        S root target (control.endpointCoverage scale hscale)
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt (coupling_pos scale))
          (Q'.le_of_lt (coupling_pos scale))))
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (slabParametricKPhysicalPartition_pos
            S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
        (Q'.le_of_lt
          (slabParametricKPhysicalPartition_pos
            S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)))

def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.toCovarianceRawCrossSeparatedLinearRawTransportTail

def toConnectedSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail

theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl

#print axioms PositiveExpandedRawEndpointCoverage
#print axioms positiveExpandedFourCellSourceSupportedPathAtReceiver
#print axioms positiveExpandedFourCellTargetSupportedPathAtReceiver
#print axioms sourceReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
#print axioms targetReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
#print axioms actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_eqv_zero_of_endpointCoverage
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl.toCoveredVariationUnreachableMassQuadraticCostControl
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
