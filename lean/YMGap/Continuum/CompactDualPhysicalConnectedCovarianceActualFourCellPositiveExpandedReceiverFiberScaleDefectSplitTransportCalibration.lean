/-
# Calibrate the explicit split-sector receiver transports

The complete receiver scale-defect cross is already transported by two
explicit kernels: the normalized support-disconnected switch and the
first-source-thinned support-connected switch.  This module rewrites the five
surviving debts of that split into literal finite receiver-density budgets.

The connected row is measured against the exact partition density.  Both
edge debts measure source-to-realized-target density variation, and both
column debts measure target calibration against incoming column slack.  A
schedule interface on these five budgets compiles to the posterior-free
split-sector covariance consumer.

No uniform linear-in-spacing estimate is proved.  In particular, this module
does not supply a physical spacing floor, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Clay conclusion.

Constructive contract: finite exact rational identities, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransportCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectEdgeVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

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

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem scaled_abs_le_local
    (factor debt budget : Q')
    (hdebt : Q'.abs debt ≤ budget) :
    Q'.abs (factor * debt) ≤ Q'.abs factor * budget := by
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le factor debt)
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs factor)
      hdebt (Q'.abs_nonneg factor))

/-! ## 1. Generic density budgets for a receiver-valued transport -/

def receiverTransportRowCalibrationL1
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
          (((positiveExpandedReceiverFiberPartitionDensity S -
                positiveExpandedFourCellSourceReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target
                  (sourceReceiver source)) *
              (S.coarse.physicalPartition *
                S.coarse.physicalPartition)) *
            ((1 : Q') + -data.rowMass source))))
    data.sources

def receiverTransportEdgeDensityVariationL1
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
              (((positiveExpandedFourCellTargetReceiverFiberDensity
                        S hfineCutoff hcoarseCoupling root target
                        (data.realize source choice) -
                    positiveExpandedFourCellSourceReceiverFiberDensity
                      S hfineCutoff hcoarseCoupling root target
                      (sourceReceiver source)) *
                  (S.coarse.physicalPartition *
                    S.coarse.physicalPartition)) *
                data.localWeight source choice)))
        (data.choices source))
    data.sources

def receiverTransportColumnCalibrationL1
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
          ((positiveExpandedReceiverFiberPartitionDensity S -
                positiveExpandedFourCellTargetReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver) *
            (S.coarse.physicalPartition *
              S.coarse.physicalPartition))))
    data.targets

theorem receiverTransportRowCoefficientDefect_abs_le_calibrationL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq)
    (sourceReceiver : Source → Receiver S root)
    (hcoefficient : ∀ source,
      data.sourceCoefficient source ≈
        (positiveExpandedReceiverFiberPartitionDensity S -
            positiveExpandedFourCellSourceReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target
              (sourceReceiver source)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) :
    Q'.abs data.rowCoefficientDefect ≤
      receiverTransportRowCalibrationL1
        S hfineCutoff hcoarseCoupling root target data sourceReceiver := by
  have hrow :
      data.rowCoefficientDefect ≈
        listQSum
          (fun source =>
            data.sourceWeight source *
              (((positiveExpandedReceiverFiberPartitionDensity S -
                    positiveExpandedFourCellSourceReceiverFiberDensity
                      S hfineCutoff hcoarseCoupling root target
                      (sourceReceiver source)) *
                  (S.coarse.physicalPartition *
                    S.coarse.physicalPartition)) *
                ((1 : Q') + -data.rowMass source)))
          data.sources := by
    refine Q'.eqv_trans _ _ _ data.rowCoefficientDefect_eqv_unretained ?_
    apply listQSum_congr
    intro source
    refine Q'.mul_eqv_congr_left (data.sourceWeight source) _ _ ?_
    exact Q'.mul_eqv_congr_right _ _ ((1 : Q') + -data.rowMass source)
      (hcoefficient source)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hrow))
    (by
      unfold receiverTransportRowCalibrationL1
      exact abs_listQSum_le_sum_abs_local _ _)

theorem receiverTransportEdgeCoefficientDefect_abs_le_densityVariationL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq)
    (sourceReceiver : Source → Receiver S root)
    (hvariation : ∀ source choice,
      data.sourceCoefficient source -
          data.targetCoefficient (data.realize source choice) ≈
        (positiveExpandedFourCellTargetReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target
              (data.realize source choice) -
            positiveExpandedFourCellSourceReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target
              (sourceReceiver source)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) :
    Q'.abs data.edgeCoefficientDefect ≤
      receiverTransportEdgeDensityVariationL1
        S hfineCutoff hcoarseCoupling root target data sourceReceiver := by
  let term := fun source choice =>
    data.sourceWeight source *
      (((positiveExpandedFourCellTargetReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target
                (data.realize source choice) -
              positiveExpandedFourCellSourceReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target
                (sourceReceiver source)) *
            (S.coarse.physicalPartition * S.coarse.physicalPartition)) *
        data.localWeight source choice)
  have hedge :
      data.edgeCoefficientDefect ≈
        listQSum
          (fun source => listQSum (term source) (data.choices source))
          data.sources := by
    refine Q'.eqv_trans _ _ _ data.edgeCoefficientDefect_eqv_variation ?_
    apply listQSum_congr
    intro source
    refine Q'.eqv_trans _
      (data.sourceWeight source *
        listQSum
          (fun choice =>
            ((positiveExpandedFourCellTargetReceiverFiberDensity
                    S hfineCutoff hcoarseCoupling root target
                    (data.realize source choice) -
                positiveExpandedFourCellSourceReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target
                  (sourceReceiver source)) *
              (S.coarse.physicalPartition *
                S.coarse.physicalPartition)) *
              data.localWeight source choice)
          (data.choices source)) _ ?_ ?_
    · refine Q'.mul_eqv_congr_left (data.sourceWeight source) _ _ ?_
      apply listQSum_congr
      intro choice
      exact Q'.mul_eqv_congr_right _ _ (data.localWeight source choice)
        (hvariation source choice)
    · exact Q'.eqv_symm
        (listQSum_mul_left
          (data.sourceWeight source)
          (fun choice =>
            ((positiveExpandedFourCellTargetReceiverFiberDensity
                    S hfineCutoff hcoarseCoupling root target
                    (data.realize source choice) -
                positiveExpandedFourCellSourceReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target
                  (sourceReceiver source)) *
              (S.coarse.physicalPartition *
                S.coarse.physicalPartition)) *
              data.localWeight source choice)
          (data.choices source))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hedge)) ?_
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local
      (fun source => listQSum (term source) (data.choices source))
      data.sources) ?_
  unfold receiverTransportEdgeDensityVariationL1
  apply listQSum_le_termwise_local
  intro source _
  exact abs_listQSum_le_sum_abs_local
    (term source) (data.choices source)

theorem receiverTransportColumnCoefficientDefect_abs_le_calibrationL1
    {Source : Type}
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    {receiverDecidableEq : DecidableEq (Receiver S root)}
    (data : @FiniteDependentCoefficientTransport Source (Receiver S root)
      receiverDecidableEq)
    (htargetCoefficient : ∀ receiver,
      data.targetCoefficient receiver ≈
        (positiveExpandedReceiverFiberPartitionDensity S -
            positiveExpandedFourCellTargetReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) :
    Q'.abs data.columnCoefficientDefect ≤
      receiverTransportColumnCalibrationL1
        S hfineCutoff hcoarseCoupling root target data := by
  have hcolumn :
      data.columnCoefficientDefect ≈
        listQSum
          (fun receiver =>
            (listQSum
                  (fun source =>
                    data.sourceWeight source *
                      dependentKernelPushforwardWeight
                        data.Choice data.choices data.localWeight data.realize
                        source receiver)
                  data.sources -
                data.targetWeight receiver) *
              ((positiveExpandedReceiverFiberPartitionDensity S -
                    positiveExpandedFourCellTargetReceiverFiberDensity
                      S hfineCutoff hcoarseCoupling root target receiver) *
                (S.coarse.physicalPartition *
                  S.coarse.physicalPartition)))
          data.targets := by
    refine Q'.eqv_trans _ _ _ data.columnCoefficientDefect_eqv_slack ?_
    apply listQSum_congr
    intro receiver
    exact Q'.mul_eqv_congr_left _ _ _
      (htargetCoefficient receiver)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hcolumn))
    (by
      unfold receiverTransportColumnCalibrationL1
      exact abs_listQSum_le_sum_abs_local _ _)

/-! ## 2. The five explicit split-sector density budgets -/

def actualPositiveExpandedReceiverFiberScaleDefectConnectedRowCalibrationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportRowCalibrationL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)
    (fun source => source.1)

def actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityVariationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportEdgeDensityVariationL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)
    (fun source => source.1)

def actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnCalibrationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportColumnCalibrationL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityVariationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportEdgeDensityVariationL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)
    (fun source => source.1)

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnCalibrationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  receiverTransportColumnCalibrationL1
    S hfineCutoff hcoarseCoupling root target
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget)

theorem actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_abs_le_calibrationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
          S hfineCutoff hcoarseCoupling root target htarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowCalibrationL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  apply receiverTransportRowCoefficientDefect_abs_le_calibrationL1
  intro source
  exact positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
    S hfineCutoff hcoarseCoupling root target source.1

theorem actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt_abs_le_densityVariationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
          S hfineCutoff hcoarseCoupling root target htarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityVariationL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  apply receiverTransportEdgeCoefficientDefect_abs_le_densityVariationL1
  intro source choice
  exact positiveExpandedFourCellScaleDefect_edgeDifference_eqv_densityVariation
    S hfineCutoff hcoarseCoupling root target source.1
    (slabObservablePairedConnectedStrandRealize
      S.coarse root target htarget source choice)

theorem actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt_abs_le_calibrationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnCalibrationL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  apply receiverTransportColumnCoefficientDefect_abs_le_calibrationL1
  intro receiver
  exact positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
    S hfineCutoff hcoarseCoupling root target receiver

theorem actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt_abs_le_densityVariationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
          S hfineCutoff hcoarseCoupling root target htarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityVariationL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  apply receiverTransportEdgeCoefficientDefect_abs_le_densityVariationL1
  intro source choice
  exact positiveExpandedFourCellScaleDefect_edgeDifference_eqv_densityVariation
    S hfineCutoff hcoarseCoupling root target source.1
    (slabObservablePairedSupportRecoupledTargetPair
      S.coarse root target htarget source choice)

theorem actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt_abs_le_calibrationL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnCalibrationL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  apply receiverTransportColumnCoefficientDefect_abs_le_calibrationL1
  intro receiver
  exact positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
    S hfineCutoff hcoarseCoupling root target receiver

/-! ## 3. Schedule producer stated only on literal density budgets -/

namespace PhysicalObservableRefinementSchedule

structure ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedRowCeiling : Q'
  connectedRowCeiling_pos : (0 : Q') < connectedRowCeiling
  connectedEdgeCeiling : Q'
  connectedEdgeCeiling_pos : (0 : Q') < connectedEdgeCeiling
  connectedColumnCeiling : Q'
  connectedColumnCeiling_pos : (0 : Q') < connectedColumnCeiling
  disconnectedEdgeCeiling : Q'
  disconnectedEdgeCeiling_pos : (0 : Q') < disconnectedEdgeCeiling
  disconnectedColumnCeiling : Q'
  disconnectedColumnCeiling_pos : (0 : Q') < disconnectedColumnCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  connectedRowCalibrationL1_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectConnectedRowCalibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem ≤
      (connectedRowCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  connectedEdgeDensityVariationL1_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityVariationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem ≤
      (connectedEdgeCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  connectedColumnCalibrationL1_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnCalibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem ≤
      (connectedColumnCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  disconnectedEdgeDensityVariationL1_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityVariationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem ≤
      (disconnectedEdgeCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  disconnectedColumnCalibrationL1_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnCalibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem ≤
      (disconnectedColumnCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)

namespace ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

def toSplitFiveDebtLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail
        schedule) :
    ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
      schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedRowCeiling := tail.connectedRowCeiling
  connectedRowCeiling_pos := tail.connectedRowCeiling_pos
  connectedEdgeCeiling := tail.connectedEdgeCeiling
  connectedEdgeCeiling_pos := tail.connectedEdgeCeiling_pos
  connectedColumnCeiling := tail.connectedColumnCeiling
  connectedColumnCeiling_pos := tail.connectedColumnCeiling_pos
  disconnectedEdgeCeiling := tail.disconnectedEdgeCeiling
  disconnectedEdgeCeiling_pos := tail.disconnectedEdgeCeiling_pos
  disconnectedColumnCeiling := tail.disconnectedColumnCeiling
  disconnectedColumnCeiling_pos := tail.disconnectedColumnCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedRowDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (scaled_abs_le_local factor _ _
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_abs_le_calibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem))
      (by simpa only [factor] using
        tail.connectedRowCalibrationL1_le scale hscale)
  connectedEdgeDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (scaled_abs_le_local factor _ _
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt_abs_le_densityVariationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem))
      (by simpa only [factor] using
        tail.connectedEdgeDensityVariationL1_le scale hscale)
  connectedColumnDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (scaled_abs_le_local factor _ _
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt_abs_le_calibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem))
      (by simpa only [factor] using
        tail.connectedColumnCalibrationL1_le scale hscale)
  disconnectedEdgeDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (scaled_abs_le_local factor _ _
        (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt_abs_le_densityVariationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem))
      (by simpa only [factor] using
        tail.disconnectedEdgeDensityVariationL1_le scale hscale)
  disconnectedColumnDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (scaled_abs_le_local factor _ _
        (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt_abs_le_calibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem))
      (by simpa only [factor] using
        tail.disconnectedColumnCalibrationL1_le scale hscale)

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toSplitFiveDebtLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling +
        (((tail.connectedRowCeiling + tail.connectedEdgeCeiling) +
            tail.connectedColumnCeiling) +
          (tail.disconnectedEdgeCeiling +
            tail.disconnectedColumnCeiling)) :=
  rfl

theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms receiverTransportRowCalibrationL1
#print axioms receiverTransportEdgeDensityVariationL1
#print axioms receiverTransportColumnCalibrationL1
#print axioms receiverTransportRowCoefficientDefect_abs_le_calibrationL1
#print axioms receiverTransportEdgeCoefficientDefect_abs_le_densityVariationL1
#print axioms receiverTransportColumnCoefficientDefect_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt_abs_le_densityVariationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt_abs_le_densityVariationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt_abs_le_calibrationL1
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail.toSplitFiveDebtLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitCalibratedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransportCalibration
