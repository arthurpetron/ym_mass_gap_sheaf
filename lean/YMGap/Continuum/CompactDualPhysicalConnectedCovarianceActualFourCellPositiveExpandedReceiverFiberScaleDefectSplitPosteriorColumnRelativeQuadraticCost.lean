/-
# Relative receiver-column inputs imply the global posterior quadratic cost

The normalized posterior route needs one global three-term estimate.  A
uniform estimate per receiver column would lose the size of the growing
finite carrier.  This module replaces that global input by local estimates
relative to the actual physical receiver weights.

The connected source carrier and the connected/disconnected target sectors
all sit inside the positive-first-replica product carrier.  Their weight is
therefore bounded without cardinality loss by the coarse physical partition
square.  The connected and disconnected target sectors are complementary, so
their common relative column ceiling is paid only once.  Finally

```text
partitionDensity * Z_coarse^2 = Z_fine^2
```

converts the local relative bounds into precisely the global quadratic input
consumed by the matched-AF posterior bridge.

No local relative estimate, raw-mismatch estimate, or lower physical-spacing
law is inhabited here.  The result is a volume-safe finite reduction, not a
continuum construction, OS/GNS reconstruction, Hamiltonian gap, or Clay
conclusion.

Constructive contract: exact rational finite sums, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCoefficientPosteriorRelativeBound
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnMatchedAFQuadraticCost
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
import YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnRelativeQuadraticCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnMatchedAFQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport.FiniteDependentCoefficientTransport
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance relativeQuadraticPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

local instance relativeQuadraticReceiverDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  splitTransportPairDecidableEq S root

private theorem targetPair_mem_positiveTimesAll
    (D : SlabPhysicalData) (root target : Nat)
    (pair : SlabObservableTwoReplicaPair D root)
    (hpair : pair ∈ slabObservableFourCellTargetPairs D root target) :
    pair ∈ slabObservablePositiveTimesAllPairs D root := by
  have htarget :=
    (mem_cartesian_iff
      (slabObservableRootTargetComplementEntries D root target)
      (slabObservableRootComplementTargetEntries D root target)
      pair).mp hpair
  apply (mem_cartesian_iff
    (slabObservablePositiveSourceEntries D root)
    (slabExpandedFineSourceEntries D) pair).mpr
  exact ⟨(List.mem_filter.mp htarget.1).1,
    (List.mem_filter.mp htarget.2).1⟩

/-- The entire opposite four-cell target carrier has mass at most the
two-replica physical partition. -/
theorem slabObservableFourCellTargetPairs_weight_le_partitionSquare
    (D : SlabPhysicalData) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs D root target) ≤
      D.physicalPartition * D.physicalPartition := by
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs D root target) ≤
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePositiveTimesAllPairs D root) := by
    apply listQSum_le_of_injective
      (slabObservableFourCellTargetPairs D root target)
      (slabObservablePositiveTimesAllPairs D root)
      (slabObservableTwoReplicaPairWeight D)
      (slabObservableTwoReplicaPairWeight D)
      (fun pair => pair)
      (slabObservableFourCellTargetPairs_nodup D root target)
    · intro pair hpair
      exact targetPair_mem_positiveTimesAll D root target pair hpair
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact slabObservableTwoReplicaPairWeight_nonnegative D root pair
  have hpositiveAdd :=
    slabObservablePositiveSourceWeight_add_one_le_partition D root
  have hpositive :
      slabObservablePositiveSourceWeight D root ≤ D.physicalPartition :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        (slabObservablePositiveSourceWeight D root) 1 (by decide))
      hpositiveAdd
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    (slabObservablePositiveSourceWeight D root)
    D.physicalPartition D.physicalPartition hpositive
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (slabObservablePositiveTimesAllPairs_weight_eqv D root))
      hscaled)

/-- The connected source list used by the density transport has total source
weight at most the coarse physical partition square. -/
theorem connectedDensityTransport_sourceWeight_le_coarseSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    let data :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    listQSum data.sourceWeight data.sources ≤
      S.coarse.physicalPartition * S.coarse.physicalPartition := by
  dsimp only
  let data :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have halign :
      listQSum data.sourceWeight data.sources ≈
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            S.coarse root target) := by
    unfold data
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      FiniteDependentCoefficientTransport.replaceCoefficients
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      slabObservablePairedConnectedStrandSources
    exact Q'.eqv_of_eq
      (listQSum_attach
        (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target))
  have hconnected :=
    slabObservablePairedSupportConnected_weight_le_positiveSourceProduct
      S.coarse root target
  have hpositiveAdd :=
    slabObservablePositiveSourceWeight_add_one_le_partition S.coarse root
  have hpositive :
      slabObservablePositiveSourceWeight S.coarse root ≤
        S.coarse.physicalPartition :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        (slabObservablePositiveSourceWeight S.coarse root) 1 (by decide))
      hpositiveAdd
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    (slabObservablePositiveSourceWeight S.coarse root)
    S.coarse.physicalPartition S.coarse.physicalPartition hpositive
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halign)
    (Q'.le_trans' _ _ _ hconnected hscaled)

/-- The connected and disconnected density transports use complementary
target sectors, so their target weights together cost at most one coarse
partition square. -/
theorem splitDensityTransports_targetWeight_le_coarseSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    listQSum connected.targetWeight connected.targets +
        listQSum disconnected.targetWeight disconnected.targets ≤
      S.coarse.physicalPartition * S.coarse.physicalPartition := by
  dsimp only
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have hpartition :=
    slabObservableFourCellTargetPairs_pairedSupport_partition
      S.coarse root target
  have halign :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≈
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellTargetPairs S.coarse root target) := by
    simpa only [connected, disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
      using Q'.eqv_symm hpartition
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halign)
    (slabObservableFourCellTargetPairs_weight_le_partitionSquare
      S.coarse root target)

theorem positiveExpandedReceiverFiberPartitionDensity_pos
    (S : SlabScalePair) :
    (0 : Q') < positiveExpandedReceiverFiberPartitionDensity S := by
  unfold positiveExpandedReceiverFiberPartitionDensity
  exact Q'.divPos_pos _ _ (coarsePhysicalPartitionSquare_pos S)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

private theorem relativeQuadraticBudget_mul_coarseSquare_eqv
    (S : SlabScalePair) (rowCeiling columnCeiling g : Q') :
    (((rowCeiling * (g * g)) *
          positiveExpandedReceiverFiberPartitionDensity S +
        (columnCeiling * (g * g)) *
          positiveExpandedReceiverFiberPartitionDensity S) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)) ≈
      (((rowCeiling + columnCeiling) * (g * g)) *
        coarseSquareCancelledCovarianceDenominator S) := by
  let density := positiveExpandedReceiverFiberPartitionDensity S
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare := S.fine.physicalPartition * S.fine.physicalPartition
  refine Q'.eqv_trans _
    ((((rowCeiling * (g * g)) + (columnCeiling * (g * g))) *
        density) * coarseSquare) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ coarseSquare
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (rowCeiling * (g * g)) (columnCeiling * (g * g)) density))
  refine Q'.eqv_trans _
    ((((rowCeiling + columnCeiling) * (g * g)) * density) *
      coarseSquare) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ coarseSquare
      (Q'.mul_eqv_congr_right _ _ density
        (Q'.eqv_symm
          (Q'.add_mul_eqv rowCeiling columnCeiling (g * g))))
  refine Q'.eqv_trans _
    (((rowCeiling + columnCeiling) * (g * g)) *
      (density * coarseSquare)) _
    (Q'.mul_assoc_eqv
      ((rowCeiling + columnCeiling) * (g * g)) density coarseSquare) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (by
    simpa only [density, coarseSquare, fineSquare,
      coarseSquareCancelledCovarianceDenominator] using
        positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv S)

/-! ## 2. Per-scale relative estimates sum without volume loss -/

/-- Source- and target-relative inputs bound the full dimensionless
three-term posterior budget by the sum of their two relative constants times
the coarse partition square. -/
theorem splitPosteriorColumnBudget_le_relativeWeights
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (rowRelative columnRelative : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrow :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      ∀ source, source ∈ connected.sources →
        Q'.abs
            (connected.sourceCoefficient source *
              ((1 : Q') + -connected.rowMass source)) ≤ rowRelative)
    (hconnectedColumn :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      ∀ target, target ∈ connected.targets →
        Q'.abs
            (connected.transportedSourceCoefficientColumnMass target -
              connected.targetWeight target *
                connected.targetCoefficient target) ≤
          columnRelative * connected.targetWeight target)
    (hdisconnectedColumn :
      let S := schedule.scalePair scale
      let disconnected :=
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      ∀ target, target ∈ disconnected.targets →
        Q'.abs
            (disconnected.transportedSourceCoefficientColumnMass target -
              disconnected.targetWeight target *
                disconnected.targetCoefficient target) ≤
          columnRelative * disconnected.targetWeight target) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      (rowRelative + columnRelative) *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  have hsourceWeight : ∀ source, source ∈ connected.sources →
      (0 : Q') ≤ connected.sourceWeight source := by
    intro source _
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
      using slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root source.1
  have hsourceMass :
      listQSum connected.sourceWeight connected.sources ≤ coarseSquare := by
    simpa only [S, root, target, htarget, connected, coarseSquare] using
      connectedDensityTransport_sourceWeight_le_coarseSquare
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have htargetMass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≤
        coarseSquare := by
    simpa only [S, root, target, htarget, connected, disconnected,
      coarseSquare] using
      splitDensityTransports_targetWeight_le_coarseSquare
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hbudget :
      (Q'.abs connected.rowCoefficientDefect +
          connected.posteriorColumnCoefficientL1) +
        disconnected.posteriorColumnCoefficientL1 ≤
      (rowRelative + columnRelative) * coarseSquare :=
    connected.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap
      disconnected rowRelative columnRelative coarseSquare
      hrowRelative hcolumnRelative hsourceWeight
      (by simpa only [S, root, target, htarget, connected] using hrow)
      (by simpa only [S, root, target, htarget, connected] using
        hconnectedColumn)
      (by simpa only [S, root, target, htarget, disconnected] using
        hdisconnectedColumn)
      hsourceMass htargetMass
  refine Q'.le_trans' _ _ _ ?_ hbudget
  exact Q'.le_of_eqv (by
    unfold actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
    simp only [S, root, target, connected, disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1]
    apply Q'.eqv_of_eq
    congr <;> apply Subsingleton.elim)

/-! ## 3. Matched-AF local inputs compile to the existing global bridge -/

/-- A volume-safe refinement of the matched-AF posterior input.  The global
posterior estimate is replaced by one connected-row relative estimate and one
common target-weight-relative estimate on each complementary target sector. -/
structure MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
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
  rowQuadraticCeiling : Q'
  rowQuadraticCeiling_pos : (0 : Q') < rowQuadraticCeiling
  posteriorQuadraticCeiling : Q'
  posteriorQuadraticCeiling_pos : (0 : Q') < posteriorQuadraticCeiling
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
  connectedRow_relative : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem
    ∀ source, source ∈ connected.sources →
      Q'.abs
          (connected.sourceCoefficient source *
            ((1 : Q') + -connected.rowMass source)) ≤
        (rowQuadraticCeiling * (coupling scale * coupling scale)) *
          positiveExpandedReceiverFiberPartitionDensity S
  connectedColumn_relative : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem
    ∀ target, target ∈ connected.targets →
      Q'.abs
          (connected.transportedSourceCoefficientColumnMass target -
            connected.targetWeight target *
              connected.targetCoefficient target) ≤
        ((posteriorQuadraticCeiling *
            (coupling scale * coupling scale)) *
          positiveExpandedReceiverFiberPartitionDensity S) *
            connected.targetWeight target
  disconnectedColumn_relative : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem
    ∀ target, target ∈ disconnected.targets →
      Q'.abs
          (disconnected.transportedSourceCoefficientColumnMass target -
            disconnected.targetWeight target *
              disconnected.targetCoefficient target) ≤
        ((posteriorQuadraticCeiling *
            (coupling scale * coupling scale)) *
          positiveExpandedReceiverFiberPartitionDensity S) *
            disconnected.targetWeight target

namespace MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl

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

def connectedQuadraticCeiling
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) : Q' :=
  control.rowQuadraticCeiling + control.posteriorQuadraticCeiling

theorem connectedQuadraticCeiling_pos
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    (0 : Q') < control.connectedQuadraticCeiling :=
  Q'.add_pos control.rowQuadraticCeiling_pos
    control.posteriorQuadraticCeiling_pos

/-- Sum the local relative estimates and feed the previously verified global
matched-AF posterior bridge. -/
def toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  connectedQuadraticCeiling := control.connectedQuadraticCeiling
  connectedQuadraticCeiling_pos := control.connectedQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  posteriorColumn_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let g2 := coupling scale * coupling scale
    let density := positiveExpandedReceiverFiberPartitionDensity S
    let rowRelative := (control.rowQuadraticCeiling * g2) * density
    let columnRelative :=
      (control.posteriorQuadraticCeiling * g2) * density
    have hg2 : (0 : Q') ≤ g2 :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt (coupling_pos scale))
        (Q'.le_of_lt (coupling_pos scale))
    have hdensity : (0 : Q') ≤ density :=
      Q'.le_of_lt (positiveExpandedReceiverFiberPartitionDensity_pos S)
    have hrowRelative : (0 : Q') ≤ rowRelative :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt control.rowQuadraticCeiling_pos) hg2)
        hdensity
    have hcolumnRelative : (0 : Q') ≤ columnRelative :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt control.posteriorQuadraticCeiling_pos) hg2)
        hdensity
    have hlocal := splitPosteriorColumnBudget_le_relativeWeights
      schedule scale rowRelative columnRelative
      hrowRelative hcolumnRelative
      (by simpa only [schedule, S, g2, density, rowRelative] using
        control.connectedRow_relative scale hscale)
      (by simpa only [schedule, S, g2, density, columnRelative] using
        control.connectedColumn_relative scale hscale)
      (by simpa only [schedule, S, g2, density, columnRelative] using
        control.disconnectedColumn_relative scale hscale)
    exact Q'.le_trans' _ _ _ hlocal
      (Q'.le_of_eqv (by
        simpa only [schedule, S, g2, density, rowRelative, columnRelative,
          connectedQuadraticCeiling] using
          relativeQuadraticBudget_mul_coarseSquare_eqv
            S control.rowQuadraticCeiling
              control.posteriorQuadraticCeiling (coupling scale)))

theorem fineCovariance_le_anchorRate_add_epsilon
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl

#print axioms slabObservableFourCellTargetPairs_weight_le_partitionSquare
#print axioms connectedDensityTransport_sourceWeight_le_coarseSquare
#print axioms splitDensityTransports_targetWeight_le_coarseSquare
#print axioms positiveExpandedReceiverFiberPartitionDensity_pos
#print axioms splitPosteriorColumnBudget_le_relativeWeights
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.connectedQuadraticCeiling
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.connectedQuadraticCeiling_pos
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnRelativeQuadraticCost
