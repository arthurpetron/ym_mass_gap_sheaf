/-
# Cancel the common partition term on receiver-transport edges

The source and target receiver-fiber scale-defect coefficients both contain
the same fine-partition square.  Their difference therefore cancels that term
exactly.  What remains on a successful transport edge is the coarse-partition
square times the difference of the target and source receiver-fiber densities.

This module records that cancellation, rewrites the complete conditional edge
debt in those density variables, and bounds its absolute value by a literal
finite `l1` density-variation budget.  It does not construct the transport
kernel or prove that the budget is `O(a)`.

Constructive contract: finite exact rational identities and inequalities only;
no choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectEdgeVariation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem sub_sub_common_left_eqv
    (common left right : Q') :
    (common - left) - (common - right) ≈ right - left := by
  change (common + -left) + -(common + -right) ≈ right + -left
  have hneg :
      -(common + -right) ≈ (-common) + right := by
    refine Q'.eqv_trans _ ((-common) + -(-right)) _
      (Q'.neg_add_eqv common (-right)) ?_
    exact Q'.add_eqv_congr_left (-common) _ _
      (Q'.neg_neg_eqv right)
  have hremove :
      (common + -left) + -common ≈ -left := by
    refine Q'.eqv_trans _ (common + ((-left) + -common)) _
      (Q'.add_assoc_eqv common (-left) (-common)) ?_
    refine Q'.eqv_trans _ (common + ((-common) + -left)) _
      (Q'.add_eqv_congr_left common _ _
        (Q'.add_comm_eqv (-left) (-common))) ?_
    refine Q'.eqv_trans _ ((common + -common) + -left) _
      (Q'.eqv_symm (Q'.add_assoc_eqv common (-common) (-left))) ?_
    refine Q'.eqv_trans _ (0 + -left) _
      (Q'.add_eqv_congr_right (common + -common) 0 (-left)
        (Q'.add_neg_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-left))
  refine Q'.eqv_trans _
    ((common + -left) + ((-common) + right)) _
    (Q'.add_eqv_congr_left (common + -left) _ _ hneg) ?_
  refine Q'.eqv_trans _
    (((common + -left) + -common) + right) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (common + -left) (-common) right)) ?_
  refine Q'.eqv_trans _ ((-left) + right) _
    (Q'.add_eqv_congr_right _ _ right hremove) ?_
  exact Q'.add_comm_eqv (-left) right

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

/-- The common fine-partition square cancels on every source-to-target
coefficient edge. -/
theorem positiveExpandedFourCellScaleDefect_edgeDifference_eqv_densityVariation
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (source receiver : SlabObservableTwoReplicaPair S.coarse root) :
    positiveExpandedFourCellSourceReceiverFiberScaleDefect
          S hfineCutoff hcoarseCoupling root target source -
        positiveExpandedFourCellTargetReceiverFiberScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver ≈
      (positiveExpandedFourCellTargetReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver -
          positiveExpandedFourCellSourceReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target source) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  unfold positiveExpandedFourCellSourceReceiverFiberScaleDefect
    positiveExpandedFourCellTargetReceiverFiberScaleDefect
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let sourceDensity :=
    positiveExpandedFourCellSourceReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target source
  let targetDensity :=
    positiveExpandedFourCellTargetReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target receiver
  exact Q'.eqv_trans _
    (targetDensity * coarseSquare - sourceDensity * coarseSquare) _
    (sub_sub_common_left_eqv fineSquare
      (sourceDensity * coarseSquare) (targetDensity * coarseSquare))
    (Q'.eqv_symm
      (Q'.sub_mul_eqv targetDensity sourceDensity coarseSquare))

/-- Absolute edge variation is controlled solely by the receiver-density
variation and the coarse-partition square; the fine-partition term is absent. -/
theorem positiveExpandedFourCellScaleDefect_edgeDifference_abs_le_densityVariation
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (source receiver : SlabObservableTwoReplicaPair S.coarse root) :
    Q'.abs
        (positiveExpandedFourCellSourceReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target source -
          positiveExpandedFourCellTargetReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver) ≤
      Q'.abs
          (positiveExpandedFourCellTargetReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target receiver -
            positiveExpandedFourCellSourceReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target source) *
        Q'.abs
          (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (positiveExpandedFourCellScaleDefect_edgeDifference_eqv_densityVariation
          S hfineCutoff hcoarseCoupling root target source receiver)))
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le _ _)

/-- Literal double-list `l1` budget for the density variation transported by
the supplied complete-cell kernel. -/
def actualPositiveExpandedReceiverFiberScaleDefectEdgeDensityVariationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) : Q' :=
  listQSum
    (fun source =>
      listQSum
        (fun choice =>
          Q'.abs
            (slabObservableTwoReplicaPairWeight S.coarse source *
              (((positiveExpandedFourCellTargetReceiverFiberDensity
                      S hfineCutoff hcoarseCoupling root target
                      (data.realize source choice) -
                    positiveExpandedFourCellSourceReceiverFiberDensity
                      S hfineCutoff hcoarseCoupling root target source) *
                  (S.coarse.physicalPartition *
                    S.coarse.physicalPartition)) *
                data.localWeight source choice)))
        (data.choices source))
    (slabObservableFourCellSourcePairs S.coarse root target)

/-- The conditional edge debt is exactly the coarse-partition-scaled density
variation summed over the literal dependent choices. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_eqv_densityVariation
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
        S hfineCutoff hcoarseCoupling root target data ≈
      listQSum
        (fun source =>
          listQSum
            (fun choice =>
              slabObservableTwoReplicaPairWeight S.coarse source *
                (((positiveExpandedFourCellTargetReceiverFiberDensity
                        S hfineCutoff hcoarseCoupling root target
                        (data.realize source choice) -
                      positiveExpandedFourCellSourceReceiverFiberDensity
                        S hfineCutoff hcoarseCoupling root target source) *
                    (S.coarse.physicalPartition *
                      S.coarse.physicalPartition)) *
                  data.localWeight source choice))
            (data.choices source))
        (slabObservableFourCellSourcePairs S.coarse root target) := by
  refine Q'.eqv_trans _ _ _
    (actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_eqv_variation
      S hfineCutoff hcoarseCoupling root target data) ?_
  apply listQSum_congr
  intro source
  refine Q'.eqv_trans _
    (slabObservableTwoReplicaPairWeight S.coarse source *
      listQSum
        (fun choice =>
          ((positiveExpandedFourCellTargetReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target
                  (data.realize source choice) -
              positiveExpandedFourCellSourceReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target source) *
            (S.coarse.physicalPartition * S.coarse.physicalPartition)) *
              data.localWeight source choice)
        (data.choices source)) _ ?_ ?_
  · refine Q'.mul_eqv_congr_left
      (slabObservableTwoReplicaPairWeight S.coarse source) _ _ ?_
    apply listQSum_congr
    intro choice
    exact Q'.mul_eqv_congr_right _ _ (data.localWeight source choice)
      (positiveExpandedFourCellScaleDefect_edgeDifference_eqv_densityVariation
        S hfineCutoff hcoarseCoupling root target source
        (data.realize source choice))
  · exact Q'.eqv_symm
      (listQSum_mul_left
        (slabObservableTwoReplicaPairWeight S.coarse source)
        (fun choice =>
          ((positiveExpandedFourCellTargetReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target
                  (data.realize source choice) -
              positiveExpandedFourCellSourceReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target source) *
            (S.coarse.physicalPartition * S.coarse.physicalPartition)) *
              data.localWeight source choice)
        (data.choices source))

/-- The exact edge debt is bounded by the finite density-variation `l1`
budget.  Proving that displayed budget is `O(a)` is the remaining edge
regularity obligation. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_abs_le_densityVariationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
          S hfineCutoff hcoarseCoupling root target data) ≤
      actualPositiveExpandedReceiverFiberScaleDefectEdgeDensityVariationL1
        S hfineCutoff hcoarseCoupling root target data := by
  let term := fun source choice =>
    slabObservableTwoReplicaPairWeight S.coarse source *
      (((positiveExpandedFourCellTargetReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target
              (data.realize source choice) -
            positiveExpandedFourCellSourceReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target source) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) *
        data.localWeight source choice)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_eqv_densityVariation
          S hfineCutoff hcoarseCoupling root target data))) ?_
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local
      (fun source => listQSum (term source) (data.choices source))
      (slabObservableFourCellSourcePairs S.coarse root target)) ?_
  unfold actualPositiveExpandedReceiverFiberScaleDefectEdgeDensityVariationL1
  apply listQSum_le_termwise_local
  intro source _
  exact abs_listQSum_le_sum_abs_local
    (term source) (data.choices source)

/-- Multiplying the edge debt by any outer normalization costs exactly the
absolute outer factor before the density-variation `l1` budget. -/
theorem actualPositiveExpandedReceiverFiberScaleDefect_scaledEdgeDebt_abs_le_densityVariationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target)
    (factor : Q') :
    Q'.abs
        (factor *
          actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
            S hfineCutoff hcoarseCoupling root target data) ≤
      Q'.abs factor *
        actualPositiveExpandedReceiverFiberScaleDefectEdgeDensityVariationL1
          S hfineCutoff hcoarseCoupling root target data := by
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le factor
      (actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
        S hfineCutoff hcoarseCoupling root target data))
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs factor)
      (actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_abs_le_densityVariationL1
        S hfineCutoff hcoarseCoupling root target data)
      (Q'.abs_nonneg factor))

#print axioms positiveExpandedFourCellScaleDefect_edgeDifference_eqv_densityVariation
#print axioms positiveExpandedFourCellScaleDefect_edgeDifference_abs_le_densityVariation
#print axioms actualPositiveExpandedReceiverFiberScaleDefectEdgeDensityVariationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_eqv_densityVariation
#print axioms actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_abs_le_densityVariationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefect_scaledEdgeDebt_abs_le_densityVariationL1

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectEdgeVariation
