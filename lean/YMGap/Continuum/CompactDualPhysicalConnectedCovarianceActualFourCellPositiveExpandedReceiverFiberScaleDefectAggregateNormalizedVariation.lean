/-
# Normalize the aggregate receiver coefficient variation on the coarse law

The split posterior budget is already bounded by one full-source plus
full-target density-coefficient `l1` sum.  Its coefficient is measured against

```text
partitionDensity = Z_fine^2 / Z_coarse^2.
```

This module divides the aggregate by that strictly positive density.  Exact
positive-division algebra then proves that its required
`O(g^2 * Z_fine^2)` estimate is equivalent to an `O(g^2 * Z_coarse^2)` bound
on a dimensionless coarse-law variation.  The resulting matched-AF control
has one receiver-side analytic field and compiles to the existing posterior
covariance consumer.

No normalized-variation estimate, raw-mismatch estimate, lower spacing law,
continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Clay conclusion
is supplied here.

Constructive contract: exact rational positive division, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnRelativeQuadraticCost
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierUniformCalibration

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateNormalizedVariation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnRelativeQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierUniformCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

local instance aggregateVariationReceiverDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair S.coarse root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

/-! ## 1. One coarse-normalized aggregate variation -/

/-- The complete source-plus-target density-coefficient `l1` mass which now
controls the connected row and both posterior columns. -/
def actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target +
    actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target

/-- The aggregate coefficient variation divided by the exact positive
fine-to-coarse partition density.  It has the scale of a coarse two-replica
mass and is the natural coarse-law total-variation input. -/
def actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target)
    (positiveExpandedReceiverFiberPartitionDensity S)
    (positiveExpandedReceiverFiberPartitionDensity_pos S)

/-- Multiplying the coarse-normalized variation by the partition density
recovers the literal aggregate coefficient `l1` exactly. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_mul_partitionDensity_eqv
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling root target *
        positiveExpandedReceiverFiberPartitionDensity S ≈
      actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
  exact Q'.divPos_mul_eqv _ _
    (positiveExpandedReceiverFiberPartitionDensity_pos S)

private theorem scaledCoarseSquare_mul_partitionDensity_eqv_scaledFineSquare
    (S : SlabScalePair) (scale : Q') :
    (scale *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) *
        positiveExpandedReceiverFiberPartitionDensity S ≈
      scale *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  refine Q'.eqv_trans _
    (scale *
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        positiveExpandedReceiverFiberPartitionDensity S)) _
    (Q'.mul_assoc_eqv scale
      (S.coarse.physicalPartition * S.coarse.physicalPartition)
      (positiveExpandedReceiverFiberPartitionDensity S)) ?_
  refine Q'.eqv_trans _
    (scale *
      (positiveExpandedReceiverFiberPartitionDensity S *
        (S.coarse.physicalPartition * S.coarse.physicalPartition))) _
    (Q'.mul_eqv_congr_left scale _ _
      (Q'.mul_comm_eqv
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
        (positiveExpandedReceiverFiberPartitionDensity S))) ?_
  exact Q'.mul_eqv_congr_left scale _ _
    (positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv S)

/-- The fine-partition aggregate estimate and the coarse-normalized variation
estimate are constructively equivalent for every ceiling. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_le_iff_fullDensityCoefficientL1_le
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (ceiling : Q') :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling root target ≤
        ceiling *
          (S.coarse.physicalPartition * S.coarse.physicalPartition) ↔
      actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
          S hfineCutoff hcoarseCoupling root target ≤
        ceiling *
          (S.fine.physicalPartition * S.fine.physicalPartition) := by
  let variation :=
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
      S hfineCutoff hcoarseCoupling root target
  let coefficientL1 :=
    actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target
  let density := positiveExpandedReceiverFiberPartitionDensity S
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare := S.fine.physicalPartition * S.fine.physicalPartition
  have hvariation : variation * density ≈ coefficientL1 := by
    simpa only [variation, coefficientL1, density] using
      actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_mul_partitionDensity_eqv
        S hfineCutoff hcoarseCoupling root target
  have hscale :
      (ceiling * coarseSquare) * density ≈ ceiling * fineSquare := by
    simpa only [density, coarseSquare, fineSquare] using
      scaledCoarseSquare_mul_partitionDensity_eqv_scaledFineSquare S ceiling
  constructor
  · intro hnormalized
    have hmul := Q'.mul_le_mul_of_nonneg_right
      variation (ceiling * coarseSquare) density hnormalized
      (Q'.le_of_lt (positiveExpandedReceiverFiberPartitionDensity_pos S))
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hvariation)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hscale))
  · intro hfull
    apply Q'.divPos_le_of_le_mul coefficientL1 density
      (positiveExpandedReceiverFiberPartitionDensity_pos S)
    exact Q'.le_trans' _ _ _ hfull (Q'.ge_of_eqv hscale)

/-! ## 2. Quantitative supported-image decomposition -/

private theorem not_of_not_decide_eq_true_local
    {P : Prop} [Decidable P] (hP : (!decide P) = true) : ¬ P := by
  have hfalse : decide P = false := by
    cases hdecision : decide P with
    | false => rfl
    | true =>
        rw [hdecision] at hP
        cases hP
  exact decide_eq_false_iff_not.mp hfalse

private theorem coefficientL1_eqv_covered_add_density_mul_uncoveredMass
    {A : Type} [DecidableEq A]
    (items image : List A) (weight coefficient : A → Q')
    (density : Q')
    (houtside : ∀ item, item ∉ image → Q'.abs (coefficient item) ≈ density) :
    listQSum (fun item => weight item * Q'.abs (coefficient item)) items ≈
      listQSum (fun item => weight item * Q'.abs (coefficient item))
          (items.filter (fun item => decide (item ∈ image))) +
        density *
          listQSum weight
            (items.filter (fun item => !(decide (item ∈ image)))) := by
  let test : A → Bool := fun item => decide (item ∈ image)
  let term := fun item => weight item * Q'.abs (coefficient item)
  have hpartition := listQSum_filter_partition term test items
  refine Q'.eqv_trans _
    (listQSum term (items.filter test) +
      listQSum term (items.filter (fun item => !(test item)))) _
    hpartition ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _
    (listQSum (fun item => density * weight item)
      (items.filter (fun item => !(test item)))) _ ?_ ?_
  · apply listQSum_congr_on
    intro item hitem
    have hparts := List.mem_filter.mp hitem
    have hnotImage : item ∉ image := by
      apply not_of_not_decide_eq_true_local
      simpa only [test] using hparts.2
    refine Q'.eqv_trans _ (weight item * density) _
      (Q'.mul_eqv_congr_left (weight item) _ _
        (houtside item hnotImage)) ?_
    exact Q'.mul_comm_eqv (weight item) density
  · simpa only [test] using
      (listQSum_mul_left density weight
        (items.filter (fun item => !(test item))))

/-- Receiver pairs hit by at least one supported source path.  Duplicates are
harmless because this list is used only as a finite membership predicate. -/
def positiveExpandedFourCellSourceSupportedReceiverImage
    (S : SlabScalePair) (root target : Nat) :
    List (SlabObservableTwoReplicaPair S.coarse root) :=
  (positiveExpandedFourCellSourceSupportedPaths S root target).map
    (fun supported => supported.receiverPair)

/-- Receiver pairs hit by at least one supported target path. -/
def positiveExpandedFourCellTargetSupportedReceiverImage
    (S : SlabScalePair) (root target : Nat) :
    List (SlabObservableTwoReplicaPair S.coarse root) :=
  (positiveExpandedFourCellTargetSupportedPaths S root target).map
    (fun supported => supported.receiverPair)

/-- Source calibration variation restricted to the supported-path image. -/
def actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredDensityCoefficientL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      slabObservableTwoReplicaPairWeight S.coarse receiver *
        Q'.abs
          (actualPositiveExpandedReceiverFiberSourceDensityCoefficient
            S hfineCutoff hcoarseCoupling root target receiver))
    ((slabObservableFourCellSourcePairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellSourceSupportedReceiverImage
            S root target)))

/-- Physical source-cell mass outside the supported-path image. -/
def actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellSourcePairs S.coarse root target).filter
      (fun receiver => !(decide
        (receiver ∈
          positiveExpandedFourCellSourceSupportedReceiverImage
            S root target))))

/-- Target calibration variation restricted to the supported-path image. -/
def actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredDensityCoefficientL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      slabObservableTwoReplicaPairWeight S.coarse receiver *
        Q'.abs
          (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
            S hfineCutoff hcoarseCoupling root target receiver))
    ((slabObservableFourCellTargetPairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellTargetSupportedReceiverImage
            S root target)))

/-- Physical target-cell mass outside the supported-path image. -/
def actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellTargetPairs S.coarse root target).filter
      (fun receiver => !(decide
        (receiver ∈
          positiveExpandedFourCellTargetSupportedReceiverImage
            S root target))))

/-- The source coefficient variation splits exactly into covered calibration
variation and partition density times uncovered physical mass. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1_eqv_covered_add_uncovered
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredDensityCoefficientL1
          S hfineCutoff hcoarseCoupling root target +
        positiveExpandedReceiverFiberPartitionDensity S *
          actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
            S root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
    actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredDensityCoefficientL1
    actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
  apply coefficientL1_eqv_covered_add_density_mul_uncoveredMass
  intro receiver hnotImage
  apply actualPositiveExpandedReceiverFiberSourceDensityCoefficient_abs_eqv_partitionDensity_of_not_image
  intro supported hsupported heq
  apply hnotImage
  exact List.mem_map.mpr ⟨supported, hsupported, heq.symm⟩

/-- The target coefficient variation has the analogous exact quantitative
coverage split. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1_eqv_covered_add_uncovered
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredDensityCoefficientL1
          S hfineCutoff hcoarseCoupling root target +
        positiveExpandedReceiverFiberPartitionDensity S *
          actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
            S root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
    actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredDensityCoefficientL1
    actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
  apply coefficientL1_eqv_covered_add_density_mul_uncoveredMass
  intro receiver hnotImage
  apply actualPositiveExpandedReceiverFiberTargetDensityCoefficient_abs_eqv_partitionDensity_of_not_image
  intro supported hsupported heq
  apply hnotImage
  exact List.mem_map.mpr ⟨supported, hsupported, heq.symm⟩

/-- Covered source-plus-target calibration variation. -/
def actualPositiveExpandedReceiverFiberScaleDefectCoveredFullDensityCoefficientL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target +
    actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target

/-- Total source-plus-target physical mass missed by the supported paths. -/
def actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
      S root target +
    actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
      S root target

/-- The complete coefficient variation is exactly the covered calibration
variation plus partition density times uncovered receiver mass. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1_eqv_covered_add_uncovered
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedReceiverFiberScaleDefectCoveredFullDensityCoefficientL1
          S hfineCutoff hcoarseCoupling root target +
        positiveExpandedReceiverFiberPartitionDensity S *
          actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
            S root target := by
  let sourceFull :=
    actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target
  let targetFull :=
    actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target
  let sourceCovered :=
    actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target
  let targetCovered :=
    actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target
  let sourceUncovered :=
    actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
      S root target
  let targetUncovered :=
    actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
      S root target
  let density := positiveExpandedReceiverFiberPartitionDensity S
  have hsource :
      sourceFull ≈ sourceCovered + density * sourceUncovered := by
    simpa only [sourceFull, sourceCovered, sourceUncovered, density] using
      (actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1_eqv_covered_add_uncovered
        S hfineCutoff hcoarseCoupling root target)
  have htarget :
      targetFull ≈ targetCovered + density * targetUncovered := by
    simpa only [targetFull, targetCovered, targetUncovered, density] using
      (actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1_eqv_covered_add_uncovered
        S hfineCutoff hcoarseCoupling root target)
  refine Q'.eqv_trans _
    ((sourceCovered + density * sourceUncovered) +
      (targetCovered + density * targetUncovered)) _ ?_ ?_
  · simpa only [actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1,
      sourceFull, targetFull] using Q'.add_eqv_congr' hsource htarget
  refine Q'.eqv_trans _
    ((sourceCovered + targetCovered) +
      (density * sourceUncovered + density * targetUncovered)) _
    (Q'.add_swap_inner sourceCovered (density * sourceUncovered)
      targetCovered (density * targetUncovered)) ?_
  simpa only [actualPositiveExpandedReceiverFiberScaleDefectCoveredFullDensityCoefficientL1,
    actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass,
    sourceCovered, targetCovered, sourceUncovered, targetUncovered, density]
    using
      (Q'.add_eqv_congr_left (sourceCovered + targetCovered) _ _
        (Q'.eqv_symm
          (Q'.mul_add_eqv density sourceUncovered targetUncovered)))

/-- The covered calibration variation normalized to coarse-law units. -/
def actualPositiveExpandedReceiverFiberScaleDefectCoveredCoarseNormalizedVariationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedReceiverFiberScaleDefectCoveredFullDensityCoefficientL1
      S hfineCutoff hcoarseCoupling root target)
    (positiveExpandedReceiverFiberPartitionDensity S)
    (positiveExpandedReceiverFiberPartitionDensity_pos S)

private theorem divPos_eqv_divPos_add_of_eqv_add_mul
    (full covered density uncovered : Q')
    (hdensity : (0 : Q') < density)
    (hfull : full ≈ covered + density * uncovered) :
    Q'.divPos full density hdensity ≈
      Q'.divPos covered density hdensity + uncovered := by
  let fullVariation := Q'.divPos full density hdensity
  let coveredVariation := Q'.divPos covered density hdensity
  have hfullVariation : fullVariation * density ≈ full := by
    exact Q'.divPos_mul_eqv full density hdensity
  have hcoveredVariation : coveredVariation * density ≈ covered := by
    exact Q'.divPos_mul_eqv covered density hdensity
  apply Q'.mul_left_cancel_of_pos hdensity
  refine Q'.eqv_trans _ full _ ?_ ?_
  · exact Q'.eqv_trans _ (fullVariation * density) _
      (Q'.mul_comm_eqv density fullVariation) hfullVariation
  refine Q'.eqv_trans _ (covered + density * uncovered) _ hfull ?_
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (density * coveredVariation + density * uncovered) _
    (Q'.mul_add_eqv density coveredVariation uncovered) ?_
  exact Q'.add_eqv_congr_right _ _ (density * uncovered)
    (Q'.eqv_trans _ (coveredVariation * density) _
      (Q'.mul_comm_eqv density coveredVariation) hcoveredVariation)

/-- The normalized aggregate variation is exactly covered relative variation
plus uncovered physical mass.  Thus literal full coverage is sufficient but
not necessary: a quantitative `O(g^2)` missing-mass estimate also closes the
seam. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_eqv_coveredVariation_add_uncoveredMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedReceiverFiberScaleDefectCoveredCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling root target +
        actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
          S root target := by
  simpa only [
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1,
    actualPositiveExpandedReceiverFiberScaleDefectCoveredCoarseNormalizedVariationL1]
    using
      (divPos_eqv_divPos_add_of_eqv_add_mul
        (actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
          S hfineCutoff hcoarseCoupling root target)
        (actualPositiveExpandedReceiverFiberScaleDefectCoveredFullDensityCoefficientL1
          S hfineCutoff hcoarseCoupling root target)
        (positiveExpandedReceiverFiberPartitionDensity S)
        (actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
          S root target)
        (positiveExpandedReceiverFiberPartitionDensity_pos S)
        (actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1_eqv_covered_add_uncovered
          S hfineCutoff hcoarseCoupling root target))

/-- Separate quadratic estimates on covered variation and uncovered mass add
without a carrier-cardinality factor. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_le_of_covered_and_uncovered
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (coveredCeiling uncoveredCeiling g : Q')
    (hcovered :
      actualPositiveExpandedReceiverFiberScaleDefectCoveredCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling root target ≤
        (coveredCeiling * (g * g)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition))
    (huncovered :
      actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
          S root target ≤
        (uncoveredCeiling * (g * g)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≤
      ((coveredCeiling + uncoveredCeiling) * (g * g)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  have hdecomposition :=
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_eqv_coveredVariation_add_uncoveredMass
      S hfineCutoff hcoarseCoupling root target
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomposition) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hcovered huncovered) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _
    (((coveredCeiling * (g * g)) +
        (uncoveredCeiling * (g * g))) * coarseSquare) _
    (Q'.eqv_symm
      (Q'.add_mul_eqv
        (coveredCeiling * (g * g))
        (uncoveredCeiling * (g * g)) coarseSquare)) ?_)
  exact Q'.mul_eqv_congr_right _ _ coarseSquare
    (Q'.eqv_symm
      (Q'.add_mul_eqv coveredCeiling uncoveredCeiling (g * g)))

/-! ## 3. Matched-AF compiler -/

/-- Preferred matched-AF input after cancelling the exact partition-density
normalization.  Its receiver field is one coarse-law variation estimate. -/
structure MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl
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
  normalizedVariationQuadraticCeiling : Q'
  normalizedVariationQuadraticCeiling_pos :
    (0 : Q') < normalizedVariationQuadraticCeiling
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
  normalizedVariation_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (normalizedVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)

namespace MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl

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

/-- Exact normalization converts the coarse-law variation field to the
aggregate coefficient field of the existing matched-AF compiler. -/
def toMatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl
    (control :
      MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  coefficientL1QuadraticCeiling :=
    control.normalizedVariationQuadraticCeiling
  coefficientL1QuadraticCeiling_pos :=
    control.normalizedVariationQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  fullCoefficientL1_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    have hfull :=
      (actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_le_iff_fullDensityCoefficientL1_le
        S rfl (schedule.effectiveCoupling_pos scale) root target
        (control.normalizedVariationQuadraticCeiling *
          (coupling scale * coupling scale))).mp
        (by simpa only [schedule, S, root, target] using
          control.normalizedVariation_quadratic_le scale hscale)
    simpa only [schedule, S, root, target,
      actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1,
      coarseSquareCancelledCovarianceDenominator] using hfull

/-- Final covariance consumer for the coarse-normalized aggregate route. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toMatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toMatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl

/-! ## 4. Quantitative coverage compiler -/

/-- A producer-facing matched-AF input that separates the two genuine causes
of aggregate receiver variation: calibration on the supported image and
physical mass missed by that image. -/
structure MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
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
  uncoveredMassQuadraticCeiling : Q'
  uncoveredMassQuadraticCeiling_pos :
    (0 : Q') < uncoveredMassQuadraticCeiling
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
    actualPositiveExpandedReceiverFiberScaleDefectCoveredCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (coveredVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
  uncoveredMass_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
          S root target ≤
      (uncoveredMassQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)

namespace MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl

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

def normalizedVariationQuadraticCeiling
    (control :
      MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) : Q' :=
  control.coveredVariationQuadraticCeiling +
    control.uncoveredMassQuadraticCeiling

theorem normalizedVariationQuadraticCeiling_pos
    (control :
      MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    (0 : Q') < control.normalizedVariationQuadraticCeiling :=
  Q'.add_pos control.coveredVariationQuadraticCeiling_pos
    control.uncoveredMassQuadraticCeiling_pos

/-- Quantitative missing-mass control and on-image calibration compile to the
single coarse-normalized variation input. -/
def toMatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl
    (control :
      MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  normalizedVariationQuadraticCeiling :=
    control.normalizedVariationQuadraticCeiling
  normalizedVariationQuadraticCeiling_pos :=
    control.normalizedVariationQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  normalizedVariation_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    exact
      actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_le_of_covered_and_uncovered
        S rfl (schedule.effectiveCoupling_pos scale) root target
        control.coveredVariationQuadraticCeiling
        control.uncoveredMassQuadraticCeiling (coupling scale)
        (by simpa only [schedule, S, root, target] using
          control.coveredVariation_quadratic_le scale hscale)
        (by simpa only [schedule, S, root, target] using
          control.uncoveredMass_quadratic_le scale hscale)

/-- Final covariance consumer for quantitative supported-image coverage. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toMatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toMatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl

#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_mul_partitionDensity_eqv
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_le_iff_fullDensityCoefficientL1_le
#print axioms positiveExpandedFourCellSourceSupportedReceiverImage
#print axioms positiveExpandedFourCellTargetSupportedReceiverImage
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredDensityCoefficientL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredDensityCoefficientL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1_eqv_covered_add_uncovered
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1_eqv_covered_add_uncovered
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoveredFullDensityCoefficientL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullDensityCoefficientL1_eqv_covered_add_uncovered
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoveredCoarseNormalizedVariationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_eqv_coveredVariation_add_uncoveredMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseNormalizedVariationL1_le_of_covered_and_uncovered
#print axioms MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
#print axioms MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
#print axioms MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl.normalizedVariationQuadraticCeiling_pos
#print axioms MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl
#print axioms MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateNormalizedVariation
