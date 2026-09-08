/-
# Cancel the coarse partition square from the split density cost

After cancellation of the common coarse--fine partition product, every one of
the five remaining literal calibration/variation budgets still contains the
same positive coarse physical-partition square inside its absolute value.
This module pulls that square through the absolute values and finite sums,
then cancels it from the residual normalized cost.

The exact connected cost is thereby reduced to a sum of five dimensionless
receiver-density defects divided only by the lattice spacing and the fine
physical-partition square.  No asymptotic estimate on that sum is supplied.
In particular, this module proves no uniform normalized-cost bound, physical
gap floor, continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Clay
conclusion.

Constructive contract: finite exact rational algebra and positivity only; no
choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostPartitionCancellation

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostPartitionCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransportCalibration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem move_positive_middle_factor_right
    (left difference factor right : Q') :
    left * ((difference * factor) * right) ≈
      (left * (difference * right)) * factor := by
  refine Q'.eqv_trans _ (left * (difference * (factor * right))) _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.mul_assoc_eqv difference factor right)) ?_
  refine Q'.eqv_trans _ (left * (difference * (right * factor))) _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.mul_eqv_congr_left difference _ _
        (Q'.mul_comm_eqv factor right))) ?_
  refine Q'.eqv_trans _ (left * ((difference * right) * factor)) _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv difference right factor))) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv left (difference * right) factor)

private theorem abs_scaled_eqv_factor_mul_abs_local
    (factor scaled base : Q')
    (hfactor : (0 : Q') ≤ factor)
    (hscaled : scaled ≈ base * factor) :
    Q'.abs scaled ≈ factor * Q'.abs base := by
  refine Q'.eqv_trans _ (Q'.abs (base * factor)) _
    (Q'.abs_eqv_congr hscaled) ?_
  refine Q'.eqv_trans _ (Q'.abs base * factor) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right base hfactor) ?_
  exact Q'.mul_comm_eqv (Q'.abs base) factor

private theorem listQSum_abs_scaled_eqv_factor_mul_local
    {A : Type}
    (factor : Q') (hfactor : (0 : Q') ≤ factor)
    (scaled base : A → Q')
    (hscaled : ∀ item, scaled item ≈ base item * factor)
    (items : List A) :
    listQSum (fun item => Q'.abs (scaled item)) items ≈
      factor * listQSum (fun item => Q'.abs (base item)) items := by
  refine Q'.eqv_trans _
    (listQSum (fun item => factor * Q'.abs (base item)) items) _ ?_ ?_
  · apply listQSum_congr
    intro item
    exact abs_scaled_eqv_factor_mul_abs_local
      factor (scaled item) (base item) hfactor (hscaled item)
  · exact listQSum_mul_left factor (fun item => Q'.abs (base item)) items

private theorem nestedListQSum_abs_scaled_eqv_factor_mul_local
    {A : Type} {B : A → Type}
    (factor : Q') (hfactor : (0 : Q') ≤ factor)
    (choices : (item : A) → List (B item))
    (scaled base : (item : A) → B item → Q')
    (hscaled : ∀ (item : A) (choice : B item),
      scaled item choice ≈ base item choice * factor)
    (items : List A) :
    listQSum
        (fun item =>
          listQSum (fun choice => Q'.abs (scaled item choice))
            (choices item))
        items ≈
      factor *
        listQSum
          (fun item =>
            listQSum (fun choice => Q'.abs (base item choice))
              (choices item))
          items := by
  refine Q'.eqv_trans _
    (listQSum
      (fun item =>
        factor *
          listQSum (fun choice => Q'.abs (base item choice))
            (choices item))
      items) _ ?_ ?_
  · apply listQSum_congr
    intro item
    exact listQSum_abs_scaled_eqv_factor_mul_local
      factor hfactor (scaled item) (base item)
      (hscaled item) (choices item)
  · exact listQSum_mul_left factor
      (fun item =>
        listQSum (fun choice => Q'.abs (base item choice))
          (choices item))
      items

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem divPos_eqv_divPos_of_cross_local
    {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q
      (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul_local hq hcancel

private theorem commonFactorCross_local
    (factor left right : Q') :
    (factor * left) * right ≈ left * (factor * right) := by
  refine Q'.eqv_trans _ (factor * (left * right)) _
    (Q'.mul_assoc_eqv factor left right) ?_
  refine Q'.eqv_trans _ ((left * right) * factor) _
    (Q'.mul_comm_eqv factor (left * right)) ?_
  refine Q'.eqv_trans _ (left * (right * factor)) _
    (Q'.mul_assoc_eqv left right factor) ?_
  exact Q'.mul_eqv_congr_left left _ _
    (Q'.mul_comm_eqv right factor)

private theorem fiveScaledTerms_eqv_factor_mul_sum
    (factor first second third fourth fifth : Q') :
    (((factor * first + factor * second) + factor * third) +
        (factor * fourth + factor * fifth)) ≈
      factor * (((first + second) + third) + (fourth + fifth)) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (factor * ((first + second) + third) +
      factor * (fourth + fifth)) _
    (Q'.mul_add_eqv factor ((first + second) + third)
      (fourth + fifth)) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _
      (factor * (first + second) + factor * third) _
      (Q'.mul_add_eqv factor (first + second) third)
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_add_eqv factor first second)))
    (Q'.mul_add_eqv factor fourth fifth)

/-! ## 1. Dimensionless generic receiver-density budgets -/

def receiverTransportRowDensityDefectL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq)
    (sourceReceiver : Source → Receiver S root) : Q' :=
  listQSum
    (fun source =>
      Q'.abs
        (data.sourceWeight source *
          ((positiveExpandedReceiverFiberPartitionDensity S -
              positiveExpandedFourCellSourceReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target
                (sourceReceiver source)) *
            ((1 : Q') + -data.rowMass source))))
    data.sources

def receiverTransportEdgeDensityDefectL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq)
    (sourceReceiver : Source → Receiver S root) : Q' :=
  listQSum
    (fun source =>
      listQSum
        (fun choice =>
          Q'.abs
            (data.sourceWeight source *
              ((positiveExpandedFourCellTargetReceiverFiberDensity
                    S hfineCutoff hcoarseCoupling root target
                    (data.realize source choice) -
                  positiveExpandedFourCellSourceReceiverFiberDensity
                    S hfineCutoff hcoarseCoupling root target
                    (sourceReceiver source)) *
                data.localWeight source choice)))
        (data.choices source))
    data.sources

def receiverTransportColumnDensityDefectL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq) : Q' :=
  listQSum
    (fun receiver =>
      Q'.abs
        ((listQSum
              (fun source =>
                data.sourceWeight source *
                  dependentKernelPushforwardWeight
                    data.Choice data.choices data.localWeight data.realize
                    source receiver)
              data.sources -
            data.targetWeight receiver) *
          (positiveExpandedReceiverFiberPartitionDensity S -
            positiveExpandedFourCellTargetReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver)))
    data.targets

theorem receiverTransportRowCalibrationL1_eqv_coarseSquare_mul_densityDefectL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq)
    (sourceReceiver : Source → Receiver S root) :
    receiverTransportRowCalibrationL1
        S hfineCutoff hcoarseCoupling root target data sourceReceiver ≈
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        receiverTransportRowDensityDefectL1
          S hfineCutoff hcoarseCoupling root target data sourceReceiver := by
  unfold receiverTransportRowCalibrationL1
    receiverTransportRowDensityDefectL1
  apply listQSum_abs_scaled_eqv_factor_mul_local
  · exact Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S)
  · intro source
    exact move_positive_middle_factor_right _ _ _ _

theorem receiverTransportEdgeDensityVariationL1_eqv_coarseSquare_mul_densityDefectL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq)
    (sourceReceiver : Source → Receiver S root) :
    receiverTransportEdgeDensityVariationL1
        S hfineCutoff hcoarseCoupling root target data sourceReceiver ≈
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        receiverTransportEdgeDensityDefectL1
          S hfineCutoff hcoarseCoupling root target data sourceReceiver := by
  unfold receiverTransportEdgeDensityVariationL1
    receiverTransportEdgeDensityDefectL1
  apply nestedListQSum_abs_scaled_eqv_factor_mul_local
  · exact Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S)
  · intro source choice
    exact move_positive_middle_factor_right _ _ _ _

theorem receiverTransportColumnCalibrationL1_eqv_coarseSquare_mul_densityDefectL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq) :
    receiverTransportColumnCalibrationL1
        S hfineCutoff hcoarseCoupling root target data ≈
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        receiverTransportColumnDensityDefectL1
          S hfineCutoff hcoarseCoupling root target data := by
  unfold receiverTransportColumnCalibrationL1
    receiverTransportColumnDensityDefectL1
  apply listQSum_abs_scaled_eqv_factor_mul_local
  · exact Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S)
  · intro receiver
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-! ## 2. The five specialized dimensionless budgets -/

def actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportRowDensityDefectL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)
    (fun source => source.1)

def actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityDefectL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportEdgeDensityDefectL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)
    (fun source => source.1)

def actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDensityDefectL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportColumnDensityDefectL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityDefectL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportEdgeDensityDefectL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)
    (fun source => source.1)

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDensityDefectL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportColumnDensityDefectL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)

/-- The five literal density defects after removing the common coarse
physical-partition square. -/
def actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  ((actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget +
        actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget) +
      actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDensityDefectL1
        S rfl (schedule.effectiveCoupling_pos scale)
        root target htarget) +
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityDefectL1
        S rfl (schedule.effectiveCoupling_pos scale)
        root target htarget +
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDensityDefectL1
        S rfl (schedule.effectiveCoupling_pos scale)
        root target htarget)

theorem actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget_eqv_coarseSquare_mul_cancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
        schedule scale ≈
      ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityBudget
          schedule scale := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let factor := S.coarse.physicalPartition * S.coarse.physicalPartition
  let first :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let second :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityDefectL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let third :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDensityDefectL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let fourth :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityDefectL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let fifth :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDensityDefectL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hfirst :
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowCalibrationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget ≈ factor * first := by
    simpa only [factor, first,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowCalibrationL1,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1]
      using
        receiverTransportRowCalibrationL1_eqv_coarseSquare_mul_densityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale) root target
          (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
            S rfl (schedule.effectiveCoupling_pos scale) root target htarget)
          (fun source => source.1)
  have hsecond :
      actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityVariationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget ≈ factor * second := by
    simpa only [factor, second,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityVariationL1,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityDefectL1]
      using
        receiverTransportEdgeDensityVariationL1_eqv_coarseSquare_mul_densityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale) root target
          (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
            S rfl (schedule.effectiveCoupling_pos scale) root target htarget)
          (fun source => source.1)
  have hthird :
      actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnCalibrationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget ≈ factor * third := by
    simpa only [factor, third,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnCalibrationL1,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDensityDefectL1]
      using
        receiverTransportColumnCalibrationL1_eqv_coarseSquare_mul_densityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale) root target
          (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
            S rfl (schedule.effectiveCoupling_pos scale) root target htarget)
  have hfourth :
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityVariationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget ≈ factor * fourth := by
    simpa only [factor, fourth,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityVariationL1,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityDefectL1]
      using
        receiverTransportEdgeDensityVariationL1_eqv_coarseSquare_mul_densityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale) root target
          (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
            S rfl (schedule.effectiveCoupling_pos scale) root target htarget)
          (fun source => source.1)
  have hfifth :
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnCalibrationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget ≈ factor * fifth := by
    simpa only [factor, fifth,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnCalibrationL1,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDensityDefectL1]
      using
        receiverTransportColumnCalibrationL1_eqv_coarseSquare_mul_densityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale) root target
          (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
            S rfl (schedule.effectiveCoupling_pos scale) root target htarget)
  refine Q'.eqv_trans _
    (((factor * first + factor * second) + factor * third) +
      (factor * fourth + factor * fifth)) _ ?_ ?_
  · simpa only [S, root, target, htarget, factor, first, second, third,
      fourth, fifth,
      actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget]
      using Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' hfirst hsecond) hthird)
        (Q'.add_eqv_congr' hfourth hfifth)
  · simpa only [S, root, target, htarget, factor, first, second, third,
      fourth, fifth,
      actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityBudget]
      using fiveScaledTerms_eqv_factor_mul_sum
        factor first second third fourth fifth

/-! ## 3. Cancel the coarse square from the normalized cost -/

/-- After both exact cancellations, only the fine physical-partition square
remains from the covariance normalization. -/
def coarseSquareCancelledCovarianceDenominator (S : SlabScalePair) : Q' :=
  S.fine.physicalPartition * S.fine.physicalPartition

theorem coarseSquareCancelledCovarianceDenominator_pos (S : SlabScalePair) :
    (0 : Q') < coarseSquareCancelledCovarianceDenominator S := by
  exact Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)

def coarseSquareCancelledSplitDensityDenominator
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  schedule.spacing.spacing scale *
    coarseSquareCancelledCovarianceDenominator (schedule.scalePair scale)

theorem coarseSquareCancelledSplitDensityDenominator_pos
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    (0 : Q') <
      coarseSquareCancelledSplitDensityDenominator schedule scale := by
  exact Q'.mul_pos (schedule.spacing.spacing_pos scale)
    (coarseSquareCancelledCovarianceDenominator_pos
      (schedule.scalePair scale))

theorem partitionCancelledSplitDensityDenominator_eqv_coarseSquare_mul_cancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    partitionCancelledSplitDensityDenominator schedule scale ≈
      ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) *
        coarseSquareCancelledSplitDensityDenominator schedule scale := by
  let spacing := schedule.spacing.spacing scale
  let coarseSquare :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).coarse.physicalPartition
  let fineSquare :=
    (schedule.scalePair scale).fine.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  change spacing * (coarseSquare * fineSquare) ≈
    coarseSquare * (spacing * fineSquare)
  refine Q'.eqv_trans _ ((spacing * coarseSquare) * fineSquare) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv spacing coarseSquare fineSquare)) ?_
  refine Q'.eqv_trans _ ((coarseSquare * spacing) * fineSquare) _
    (Q'.mul_eqv_congr_right _ _ fineSquare
      (Q'.mul_comm_eqv spacing coarseSquare)) ?_
  exact Q'.mul_assoc_eqv coarseSquare spacing fineSquare

def actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityNormalizedCost
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityBudget
      schedule scale)
    (coarseSquareCancelledSplitDensityDenominator schedule scale)
    (coarseSquareCancelledSplitDensityDenominator_pos schedule scale)

theorem actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost_eqv_coarseSquareCancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
        schedule scale ≈
      actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityNormalizedCost
        schedule scale := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityNormalizedCost
  refine divPos_eqv_divPos_of_cross_local
    (partitionCancelledSplitDensityDenominator_pos schedule scale)
    (coarseSquareCancelledSplitDensityDenominator_pos schedule scale) ?_
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).coarse.physicalPartition
  let reduced :=
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityBudget
      schedule scale
  let denominator :=
    coarseSquareCancelledSplitDensityDenominator schedule scale
  have hbudget :
      actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
          schedule scale ≈ factor * reduced := by
    simpa only [factor, reduced] using
      actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget_eqv_coarseSquare_mul_cancelled
        schedule scale
  have hdenominator :
      partitionCancelledSplitDensityDenominator schedule scale ≈
        factor * denominator := by
    simpa only [factor, denominator] using
      partitionCancelledSplitDensityDenominator_eqv_coarseSquare_mul_cancelled
        schedule scale
  refine Q'.eqv_trans _ ((factor * reduced) * denominator) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ denominator hbudget
  · refine Q'.eqv_trans _ (reduced * (factor * denominator)) _
      (commonFactorCross_local factor reduced denominator) ?_
    exact Q'.mul_eqv_congr_left reduced _ _
      (Q'.eqv_symm hdenominator)

theorem actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_eqv_coarseSquareCancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost
        schedule scale ≈
      actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityNormalizedCost
        schedule scale :=
  Q'.eqv_trans _ _ _
    (actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_eqv_partitionCancelled
      schedule scale)
    (actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost_eqv_coarseSquareCancelled
      schedule scale)

#print axioms receiverTransportRowDensityDefectL1
#print axioms receiverTransportEdgeDensityDefectL1
#print axioms receiverTransportColumnDensityDefectL1
#print axioms receiverTransportRowCalibrationL1_eqv_coarseSquare_mul_densityDefectL1
#print axioms receiverTransportEdgeDensityVariationL1_eqv_coarseSquare_mul_densityDefectL1
#print axioms receiverTransportColumnCalibrationL1_eqv_coarseSquare_mul_densityDefectL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityDefectL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDensityDefectL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityDefectL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDensityDefectL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityBudget
#print axioms actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget_eqv_coarseSquare_mul_cancelled
#print axioms coarseSquareCancelledCovarianceDenominator
#print axioms coarseSquareCancelledCovarianceDenominator_pos
#print axioms coarseSquareCancelledSplitDensityDenominator
#print axioms coarseSquareCancelledSplitDensityDenominator_pos
#print axioms partitionCancelledSplitDensityDenominator_eqv_coarseSquare_mul_cancelled
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitDensityNormalizedCost
#print axioms actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost_eqv_coarseSquareCancelled
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_eqv_coarseSquareCancelled

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation
