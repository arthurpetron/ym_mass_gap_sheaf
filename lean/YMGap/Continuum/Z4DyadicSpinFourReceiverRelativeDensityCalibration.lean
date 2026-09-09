/-
# Relative density calibration for saturated spin-four receivers

The pointwise receiver compiler accepts scale defects in fine-partition-square
units.  This module identifies the exact dimensionless analytic input behind
those defects.  For an assignment-saturated receiver density `rho`,

  Z_fine^2 - rho * Z_coarse^2

is the relative density error

  (Z_fine^2 / Z_coarse^2 - rho) * Z_coarse^2.

Consequently a relative density estimate of size `relative` implies the
pointwise scale-defect estimate `relative * Z_fine^2`, and the existing
cardinality-free compiler yields the full covered receiver variation bound.

No relative density estimate is inhabited here.  In particular this module
does not prove the remaining small-coupling estimate, an all-cutoff
contraction, continuum construction, OS/GNS reconstruction, Hamiltonian gap,
or Yang--Mills mass gap.

Constructive contract: positive rational division, exact finite algebra, and
inequalities only; no choice, `Classical`, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourReceiverPointwiseCalibration
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration

namespace YMGap.Continuum.Z4DyadicSpinFourReceiverRelativeDensityCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicSpinFourMatchedAFCoverage
open YMGap.Continuum.Z4DyadicSpinFourReceiverPointwiseCalibration

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem relative_partitionDensity_mul_coarseSquare_eqv_fineSquare
    (S : SlabScalePair) (relative : Q') :
    (relative * positiveExpandedReceiverFiberPartitionDensity S) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) ≈
      relative *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  refine Q'.eqv_trans _
    (relative *
      (positiveExpandedReceiverFiberPartitionDensity S *
        (S.coarse.physicalPartition * S.coarse.physicalPartition))) _
    (Q'.mul_assoc_eqv relative
      (positiveExpandedReceiverFiberPartitionDensity S)
      (S.coarse.physicalPartition * S.coarse.physicalPartition)) ?_
  exact Q'.mul_eqv_congr_left relative _ _
    (positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv S)

/-! ## 1. Exact saturated calibration factorizations -/

/-- The saturated source defect is exactly the assignment-saturated relative
density error times the coarse physical partition square. -/
theorem positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver ≈
      (positiveExpandedReceiverFiberPartitionDensity S -
        positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  unfold positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
  refine Q'.eqv_trans _
    (positiveExpandedReceiverFiberPartitionDensity S *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) -
      positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.eqv_symm
        (positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv
          S))
      (Q'.eqv_refl _)
  · exact Q'.eqv_symm
      (Q'.sub_mul_eqv
        (positiveExpandedReceiverFiberPartitionDensity S)
        (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver)
        (S.coarse.physicalPartition * S.coarse.physicalPartition))

/-- The saturated target defect has the same exact calibration
factorization. -/
theorem positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver ≈
      (positiveExpandedReceiverFiberPartitionDensity S -
        positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  unfold positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
  refine Q'.eqv_trans _
    (positiveExpandedReceiverFiberPartitionDensity S *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) -
      positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.eqv_symm
        (positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv
          S))
      (Q'.eqv_refl _)
  · exact Q'.eqv_symm
      (Q'.sub_mul_eqv
        (positiveExpandedReceiverFiberPartitionDensity S)
        (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver)
        (S.coarse.physicalPartition * S.coarse.physicalPartition))

/-! ## 2. Relative density error implies pointwise scale-defect error -/

/-- A dimensionless relative source-density estimate gives the exact
fine-square pointwise budget used by the receiver compiler. -/
theorem positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (relative : Q')
    (hcalibration :
      Q'.abs
          (positiveExpandedReceiverFiberPartitionDensity S -
            positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver) ≤
        relative * positiveExpandedReceiverFiberPartitionDensity S) :
    Q'.abs
        (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver) ≤
      relative *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  let densityError :=
    positiveExpandedReceiverFiberPartitionDensity S -
      positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  have hcoarseSquareNonnegative : (0 : Q') ≤ coarseSquare :=
    Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S)
  have habs :
      Q'.abs
          (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≈
        Q'.abs densityError * coarseSquare := by
    refine Q'.eqv_trans _ (Q'.abs (densityError * coarseSquare)) _ ?_ ?_
    · exact Q'.abs_eqv_congr
        (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_eqv_calibration
          S hfineCutoff hcoarseCoupling root target receiver)
    · exact YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        densityError hcoarseSquareNonnegative
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ coarseSquare
        hcalibration hcoarseSquareNonnegative)
      (Q'.le_of_eqv
        (relative_partitionDensity_mul_coarseSquare_eqv_fineSquare
          S relative)))

/-- Target analogue of the relative-density-to-fine-square compiler. -/
theorem positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (relative : Q')
    (hcalibration :
      Q'.abs
          (positiveExpandedReceiverFiberPartitionDensity S -
            positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver) ≤
        relative * positiveExpandedReceiverFiberPartitionDensity S) :
    Q'.abs
        (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver) ≤
      relative *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  let densityError :=
    positiveExpandedReceiverFiberPartitionDensity S -
      positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  have hcoarseSquareNonnegative : (0 : Q') ≤ coarseSquare :=
    Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S)
  have habs :
      Q'.abs
          (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver) ≈
        Q'.abs densityError * coarseSquare := by
    refine Q'.eqv_trans _ (Q'.abs (densityError * coarseSquare)) _ ?_ ?_
    · exact Q'.abs_eqv_congr
        (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_eqv_calibration
          S hfineCutoff hcoarseCoupling root target receiver)
    · exact YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        densityError hcoarseSquareNonnegative
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ coarseSquare
        hcalibration hcoarseSquareNonnegative)
      (Q'.le_of_eqv
        (relative_partitionDensity_mul_coarseSquare_eqv_fineSquare
          S relative)))

/-! ## 3. Named analytic seam and covered-variation handoff -/

/-- The precise dimensionless analytic input still required on all canonical
source and target receivers. -/
def PositiveExpandedAssignmentSaturatedRelativeDensityCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (relative : Q') : Prop :=
  (∀ receiver,
    receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
    Q'.abs
        (positiveExpandedReceiverFiberPartitionDensity S -
          positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver) ≤
      relative * positiveExpandedReceiverFiberPartitionDensity S) ∧
  (∀ receiver,
    receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
    Q'.abs
        (positiveExpandedReceiverFiberPartitionDensity S -
          positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver) ≤
      relative * positiveExpandedReceiverFiberPartitionDensity S)

/-- The named relative calibration seam is sufficient for full normalized
receiver variation, with no receiver-cardinality factor. -/
theorem actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_twice_relative_mul_coarseSquare_of_relativeDensityCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (relative : Q')
    (hrelative : (0 : Q') ≤ relative)
    (hcalibration :
      PositiveExpandedAssignmentSaturatedRelativeDensityCalibration
        S hfineCutoff hcoarseCoupling root target relative) :
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≤
      (relative + relative) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  exact actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_twice_relative_mul_coarseSquare_of_pointwise
    S hfineCutoff hcoarseCoupling root target relative hrelative
    (fun receiver hreceiver =>
      positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
        S hfineCutoff hcoarseCoupling root target receiver relative
        (hcalibration.1 receiver hreceiver))
    (fun receiver hreceiver =>
      positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
        S hfineCutoff hcoarseCoupling root target receiver relative
        (hcalibration.2 receiver hreceiver))

/-- Quadratic relative density calibration feeds the exact endpoint-covered
variation field consumed by the matched-AF receiver producer. -/
theorem actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_relativeDensityCalibration_endpointCoverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (coefficient coupling : Q')
    (hcoefficient : (0 : Q') ≤ coefficient)
    (hcoupling : (0 : Q') ≤ coupling)
    (hcalibration :
      PositiveExpandedAssignmentSaturatedRelativeDensityCalibration
        S hfineCutoff hcoarseCoupling root target
          (coefficient * (coupling * coupling))) :
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≤
      ((coefficient + coefficient) * (coupling * coupling)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  exact actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_pointwise_endpointCoverage
    S hfineCutoff hcoarseCoupling root target coverage coefficient coupling
    hcoefficient hcoupling
    (fun receiver hreceiver =>
      positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
        S hfineCutoff hcoarseCoupling root target receiver
          (coefficient * (coupling * coupling))
          (hcalibration.1 receiver hreceiver))
    (fun receiver hreceiver =>
      positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
        S hfineCutoff hcoarseCoupling root target receiver
          (coefficient * (coupling * coupling))
          (hcalibration.2 receiver hreceiver))

#print axioms positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_eqv_calibration
#print axioms positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_eqv_calibration
#print axioms positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
#print axioms positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_abs_le_relative_mul_fineSquare_of_density
#print axioms PositiveExpandedAssignmentSaturatedRelativeDensityCalibration
#print axioms actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_twice_relative_mul_coarseSquare_of_relativeDensityCalibration
#print axioms actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1_le_quadratic_mul_coarseSquare_of_relativeDensityCalibration_endpointCoverage

end YMGap.Continuum.Z4DyadicSpinFourReceiverRelativeDensityCalibration
