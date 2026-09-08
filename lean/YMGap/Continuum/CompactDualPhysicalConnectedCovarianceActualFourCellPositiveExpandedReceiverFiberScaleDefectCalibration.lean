/-
# Calibrate receiver-fiber scale defects by the partition density

The partition-scaled receiver coefficient

  Z_fine^2 - receiverFiberDensity * Z_coarse^2

is exactly the receiver-density calibration error relative to
`Z_fine^2 / Z_coarse^2`, multiplied by `Z_coarse^2`.  This module proves that
factorization for both source and target coefficients.  It then rewrites the
conditional row and column debts in calibration variables and gives literal
finite `l1` majorants for them.  Together with the edge-variation module, all
three transport debts are now expressed using receiver-fiber density errors.

No calibration-error estimate, transport-kernel construction, refining-scale
bound, continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Clay
conclusion is supplied here.

Constructive contract: positive rational division, finite exact identities,
and inequalities only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectEdgeVariation

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance scaleDefectCalibrationPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem abs_listQSum_le_sum_abs_local {A : Type}
    (value : A → Q') : ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add
          (Q'.le_refl' (Q'.abs (value head)))
          (abs_listQSum_le_sum_abs_local value tail))

/-- The coarse physical partition square is strictly positive. -/
theorem coarsePhysicalPartitionSquare_pos (S : SlabScalePair) :
    (0 : Q') <
      S.coarse.physicalPartition * S.coarse.physicalPartition :=
  Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
    (slabParametricKPhysicalPartition_pos
      S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)

/-- The exact density that would make a receiver scale-defect coefficient
zero. -/
def positiveExpandedReceiverFiberPartitionDensity
    (S : SlabScalePair) : Q' :=
  Q'.divPos
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (S.coarse.physicalPartition * S.coarse.physicalPartition)
    (coarsePhysicalPartitionSquare_pos S)

theorem positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv
    (S : SlabScalePair) :
    positiveExpandedReceiverFiberPartitionDensity S *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) ≈
      S.fine.physicalPartition * S.fine.physicalPartition := by
  unfold positiveExpandedReceiverFiberPartitionDensity
  exact Q'.divPos_mul_eqv _ _ (coarsePhysicalPartitionSquare_pos S)

/-- A source receiver coefficient is exactly its partition-density
calibration error times the coarse partition square. -/
theorem positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    positiveExpandedFourCellSourceReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver ≈
      (positiveExpandedReceiverFiberPartitionDensity S -
        positiveExpandedFourCellSourceReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  unfold positiveExpandedFourCellSourceReceiverFiberScaleDefect
  refine Q'.eqv_trans _
    (positiveExpandedReceiverFiberPartitionDensity S *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) -
      positiveExpandedFourCellSourceReceiverFiberDensity
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
        (positiveExpandedFourCellSourceReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver)
        (S.coarse.physicalPartition * S.coarse.physicalPartition))

/-- A target receiver coefficient is exactly its partition-density
calibration error times the coarse partition square. -/
theorem positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    positiveExpandedFourCellTargetReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver ≈
      (positiveExpandedReceiverFiberPartitionDensity S -
        positiveExpandedFourCellTargetReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  unfold positiveExpandedFourCellTargetReceiverFiberScaleDefect
  refine Q'.eqv_trans _
    (positiveExpandedReceiverFiberPartitionDensity S *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) -
      positiveExpandedFourCellTargetReceiverFiberDensity
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
        (positiveExpandedFourCellTargetReceiverFiberDensity
          S hfineCutoff hcoarseCoupling root target receiver)
        (S.coarse.physicalPartition * S.coarse.physicalPartition))

/-- Literal connected-row `l1` budget for partition-density calibration error
times unretained row mass. -/
def actualPositiveExpandedReceiverFiberScaleDefectRowCalibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) : Q' :=
  listQSum
    (fun source =>
      Q'.abs
        (slabObservableTwoReplicaPairWeight S.coarse source *
          (((positiveExpandedReceiverFiberPartitionDensity S -
                positiveExpandedFourCellSourceReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target source) *
              (S.coarse.physicalPartition *
                S.coarse.physicalPartition)) *
            ((1 : Q') + -data.rowMass source))))
    (slabObservablePairedSupportConnectedFourCellSourcePairs
      S.coarse root target)

/-- The row debt is exactly a connected-sector receiver-density calibration
error paired with the unretained row mass. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectRowDebt
        S hfineCutoff hcoarseCoupling root target data ≈
      listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight S.coarse source *
            (((positiveExpandedReceiverFiberPartitionDensity S -
                  positiveExpandedFourCellSourceReceiverFiberDensity
                    S hfineCutoff hcoarseCoupling root target source) *
                (S.coarse.physicalPartition *
                  S.coarse.physicalPartition)) *
              ((1 : Q') + -data.rowMass source)))
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target) := by
  refine Q'.eqv_trans _ _ _
    (actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_connected
      S hfineCutoff hcoarseCoupling root target data) ?_
  apply listQSum_congr
  intro source
  refine Q'.mul_eqv_congr_left
    (slabObservableTwoReplicaPairWeight S.coarse source) _ _ ?_
  exact Q'.mul_eqv_congr_right _ _ ((1 : Q') + -data.rowMass source)
    (positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
      S hfineCutoff hcoarseCoupling root target source)

theorem actualPositiveExpandedReceiverFiberScaleDefectRowDebt_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectRowDebt
          S hfineCutoff hcoarseCoupling root target data) ≤
      actualPositiveExpandedReceiverFiberScaleDefectRowCalibrationL1
        S hfineCutoff hcoarseCoupling root target data := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_calibration
          S hfineCutoff hcoarseCoupling root target data)))
    (abs_listQSum_le_sum_abs_local _ _)

/-- Literal target-column `l1` budget for the partition-density calibration
error paired with incoming capacity slack. -/
def actualPositiveExpandedReceiverFiberScaleDefectColumnCalibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) : Q' :=
  listQSum
    (fun receiver =>
      Q'.abs
        ((listQSum
              (fun source =>
                slabObservableTwoReplicaPairWeight S.coarse source *
                  dependentKernelPushforwardWeight
                    data.Choice data.choices data.localWeight data.realize
                    source receiver)
              (slabObservableFourCellSourcePairs
                S.coarse root target) -
            slabObservableTwoReplicaPairWeight S.coarse receiver) *
          ((positiveExpandedReceiverFiberPartitionDensity S -
                positiveExpandedFourCellTargetReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver) *
            (S.coarse.physicalPartition *
              S.coarse.physicalPartition))))
    (slabObservableFourCellTargetPairs S.coarse root target)

/-- The column debt is exactly the incoming slack paired with the target
receiver-density calibration error. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
        S hfineCutoff hcoarseCoupling root target data ≈
      listQSum
        (fun receiver =>
          (listQSum
                (fun source =>
                  slabObservableTwoReplicaPairWeight S.coarse source *
                    dependentKernelPushforwardWeight
                      data.Choice data.choices data.localWeight data.realize
                      source receiver)
                (slabObservableFourCellSourcePairs
                  S.coarse root target) -
              slabObservableTwoReplicaPairWeight S.coarse receiver) *
            ((positiveExpandedReceiverFiberPartitionDensity S -
                  positiveExpandedFourCellTargetReceiverFiberDensity
                    S hfineCutoff hcoarseCoupling root target receiver) *
              (S.coarse.physicalPartition *
                S.coarse.physicalPartition)))
        (slabObservableFourCellTargetPairs S.coarse root target) := by
  refine Q'.eqv_trans _ _ _
    (actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_eqv_slack
      S hfineCutoff hcoarseCoupling root target data) ?_
  apply listQSum_congr
  intro receiver
  exact Q'.mul_eqv_congr_left _ _ _
    (positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
      S hfineCutoff hcoarseCoupling root target receiver)

theorem actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
          S hfineCutoff hcoarseCoupling root target data) ≤
      actualPositiveExpandedReceiverFiberScaleDefectColumnCalibrationL1
        S hfineCutoff hcoarseCoupling root target data := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_eqv_calibration
          S hfineCutoff hcoarseCoupling root target data)))
    (abs_listQSum_le_sum_abs_local _ _)

/-- Any outer normalization can be pulled in front of the row calibration
`l1` majorant. -/
theorem actualPositiveExpandedReceiverFiberScaleDefect_scaledRowDebt_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target)
    (factor : Q') :
    Q'.abs
        (factor *
          actualPositiveExpandedReceiverFiberScaleDefectRowDebt
            S hfineCutoff hcoarseCoupling root target data) ≤
      Q'.abs factor *
        actualPositiveExpandedReceiverFiberScaleDefectRowCalibrationL1
          S hfineCutoff hcoarseCoupling root target data := by
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le factor _)
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs factor)
      (actualPositiveExpandedReceiverFiberScaleDefectRowDebt_abs_le_calibrationL1
        S hfineCutoff hcoarseCoupling root target data)
      (Q'.abs_nonneg factor))

/-- Any outer normalization can be pulled in front of the column calibration
`l1` majorant. -/
theorem actualPositiveExpandedReceiverFiberScaleDefect_scaledColumnDebt_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target)
    (factor : Q') :
    Q'.abs
        (factor *
          actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
            S hfineCutoff hcoarseCoupling root target data) ≤
      Q'.abs factor *
        actualPositiveExpandedReceiverFiberScaleDefectColumnCalibrationL1
          S hfineCutoff hcoarseCoupling root target data := by
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le factor _)
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs factor)
      (actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_abs_le_calibrationL1
        S hfineCutoff hcoarseCoupling root target data)
      (Q'.abs_nonneg factor))

#print axioms coarsePhysicalPartitionSquare_pos
#print axioms positiveExpandedReceiverFiberPartitionDensity
#print axioms positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv
#print axioms positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
#print axioms positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
#print axioms actualPositiveExpandedReceiverFiberScaleDefectRowCalibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_calibration
#print axioms actualPositiveExpandedReceiverFiberScaleDefectRowDebt_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectColumnCalibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_eqv_calibration
#print axioms actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefect_scaledRowDebt_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefect_scaledColumnDebt_abs_le_calibrationL1

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
