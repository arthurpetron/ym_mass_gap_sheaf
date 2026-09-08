/-
# Partition-scaled defect for assignment-saturated receiver densities

The assignment-saturated receiver densities preserve the positive
raw-supported source and target masses, but the connected covariance defect
compares those masses with a coarse receiver cross in different partition
units.  This module introduces the corresponding pointwise coefficient

  Z_fine^2 - saturatedDensity * Z_coarse^2

on the complete source and target receiver cells.  Exact finite algebra
factors the actual connected raw-cross defect through the signed sum of these
coefficients.  A direct triangle inequality then bounds it by one explicit
source-plus-target calibration `l1` budget.

This is the exact adapter needed before normalizing the new density and
splitting its calibration into saturated-image and physically unreachable
endpoint terms.  No smallness estimate, continuum measure, OS/GNS
reconstruction, or Yang--Mills mass gap is proved here.

Constructive contract: exact rational finite sums and inequalities only; no
choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem listQSum_neg_local {A : Type}
    (value : A → Q') (items : List A) :
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items) := by
  induction items with
  | nil =>
      change (0 : Q') ≈ -(0 : Q')
      decide
  | cons head tail ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail)))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_neg_local right items)

private theorem scaledDensityWeight_reorder_local
    (density scale weight : Q') :
    (density * scale) * weight ≈
      scale * (density * weight) := by
  ring_qeqv

private theorem subtractScaledCrosses_local
    (massScale loadScale sourceMass targetMass sourceLoad targetLoad : Q') :
    (massScale * sourceMass + -(loadScale * sourceLoad)) +
        -(massScale * targetMass + -(loadScale * targetLoad)) ≈
      massScale * (sourceMass + -targetMass) +
        -(loadScale * (sourceLoad + -targetLoad)) := by
  ring_qeqv

private theorem factorPartitionScaledCrosses_local
    (coarseCross saturatedCross coarsePartition finePartition : Q') :
    (coarseCross * coarsePartition) *
          (finePartition * (finePartition * finePartition)) +
        -((saturatedCross * finePartition) *
          (coarsePartition * (coarsePartition * coarsePartition))) ≈
      (coarsePartition * finePartition) *
        ((finePartition * finePartition) * coarseCross +
          -((coarsePartition * coarsePartition) * saturatedCross)) := by
  ring_qeqv

private theorem listQSum_scaledDensityDefect_local
    {A : Type} (fineSquare coarseSquare : Q')
    (density weight : A → Q') (items : List A) :
    listQSum
        (fun item =>
          (fineSquare - density item * coarseSquare) * weight item)
        items ≈
      fineSquare * listQSum weight items -
        coarseSquare *
          listQSum (fun item => density item * weight item) items := by
  refine Q'.eqv_trans _
    (listQSum
        (fun item => fineSquare * weight item -
          (density item * coarseSquare) * weight item)
        items) _ ?_ ?_
  · apply listQSum_congr
    intro item
    exact Q'.sub_mul_eqv
      fineSquare (density item * coarseSquare) (weight item)
  refine Q'.eqv_trans _
    (listQSum (fun item => fineSquare * weight item) items -
      listQSum
        (fun item => (density item * coarseSquare) * weight item)
        items) _
    (listQSum_sub_local _ _ items) ?_
  exact sub_eqv_both_local
    (listQSum_mul_left fineSquare weight items)
    (Q'.eqv_trans _
      (listQSum
        (fun item => coarseSquare * (density item * weight item)) items) _
      (listQSum_congr_on _ _ items
        (fun item _ =>
          scaledDensityWeight_reorder_local
            (density item) coarseSquare (weight item)))
      (listQSum_mul_left coarseSquare
        (fun item => density item * weight item) items))

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

/-! ## 1. Saturated pointwise and aggregate scale defects -/

def positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  S.fine.physicalPartition * S.fine.physicalPartition -
    positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver *
      (S.coarse.physicalPartition * S.coarse.physicalPartition)

def positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  S.fine.physicalPartition * S.fine.physicalPartition -
    positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver *
      (S.coarse.physicalPartition * S.coarse.physicalPartition)

def positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver)
    (slabObservableFourCellSourcePairs S.coarse root target)

def positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver)
    (slabObservableFourCellTargetPairs S.coarse root target)

theorem positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellSourcePairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellSourcePairs S.coarse root target) := by
  unfold positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass
    positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
  exact listQSum_scaledDensityDefect_local
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (S.coarse.physicalPartition * S.coarse.physicalPartition)
    (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target)
    (slabObservableTwoReplicaPairWeight S.coarse)
    (slabObservableFourCellSourcePairs S.coarse root target)

theorem positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellTargetPairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellTargetPairs S.coarse root target) := by
  unfold positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass
    positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
  exact listQSum_scaledDensityDefect_local
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (S.coarse.physicalPartition * S.coarse.physicalPartition)
    (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target)
    (slabObservableTwoReplicaPairWeight S.coarse)
    (slabObservableFourCellTargetPairs S.coarse root target)

def actualPositiveExpandedAssignmentSaturatedScaleDefectCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass
      S hfineCutoff hcoarseCoupling root target -
    positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass
      S hfineCutoff hcoarseCoupling root target

theorem actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedAssignmentSaturatedScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          physicalReceiverPairFourCellCross S.coarse root target -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          actualPositiveExpandedSaturatedReceiverFiberWeightedFaceRawFourCellPathCross
            S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedAssignmentSaturatedScaleDefectCross
    physicalReceiverPairFourCellCross
    actualPositiveExpandedSaturatedReceiverFiberWeightedFaceRawFourCellPathCross
  refine Q'.eqv_trans _
    (((S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellSourcePairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellSourcePairs S.coarse root target)) -
      ((S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellTargetPairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellTargetPairs S.coarse root target))) _ ?_ ?_
  · exact sub_eqv_both_local
      (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass_eqv
        S hfineCutoff hcoarseCoupling root target)
      (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass_eqv
        S hfineCutoff hcoarseCoupling root target)
  · exact subtractScaledCrosses_local
      (S.fine.physicalPartition * S.fine.physicalPartition)
      (S.coarse.physicalPartition * S.coarse.physicalPartition)
      (listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellSourcePairs S.coarse root target))
      (listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellTargetPairs S.coarse root target))
      (listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellSourcePairs S.coarse root target))
      (listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellTargetPairs S.coarse root target))

/-! ## 2. Exact factorization of the actual raw-cross defect -/

theorem physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect_eqv_scaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      (S.coarse.physicalPartition * S.fine.physicalPartition) *
        actualPositiveExpandedAssignmentSaturatedScaleDefectCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget := by
  let coarseCross :=
    physicalReceiverPairFourCellCross
      S.coarse M.coarseRoot M.coarseTarget
  let saturatedCross :=
    actualPositiveExpandedSaturatedReceiverFiberWeightedFaceRawFourCellPathCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  have hcoarse :=
    physicalFaceRawFourCellCross_eqv_receiverPairCross
      S.coarse M.coarseRoot M.coarseTarget
  have hscale :=
    actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  unfold physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
    rawCovarianceDenominator
  refine Q'.eqv_trans _
    ((coarseCross * S.coarse.physicalPartition) *
          (S.fine.physicalPartition *
            (S.fine.physicalPartition * S.fine.physicalPartition)) -
      (saturatedCross * S.fine.physicalPartition) *
          (S.coarse.physicalPartition *
            (S.coarse.physicalPartition * S.coarse.physicalPartition))) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ S.coarse.physicalPartition hcoarse))
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    ((S.coarse.physicalPartition * S.fine.physicalPartition) *
      ((S.fine.physicalPartition * S.fine.physicalPartition) * coarseCross -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          saturatedCross)) _ ?_ ?_
  · exact factorPartitionScaledCrosses_local
      coarseCross saturatedCross
      S.coarse.physicalPartition S.fine.physicalPartition
  · exact Q'.mul_eqv_congr_left
      (S.coarse.physicalPartition * S.fine.physicalPartition) _ _
      (Q'.eqv_symm hscale)

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturatedScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      (S.coarse.physicalPartition * S.fine.physicalPartition) *
        actualPositiveExpandedAssignmentSaturatedScaleDefectCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturated
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect_eqv_scaleDefect
      S hfineCutoff hcoarseCoupling M)

/-! ## 3. Direct saturated calibration majorant -/

def actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      Q'.abs
        (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver))
    (slabObservableFourCellSourcePairs S.coarse root target)

def actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      Q'.abs
        (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver))
    (slabObservableFourCellTargetPairs S.coarse root target)

def actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1
      S hfineCutoff hcoarseCoupling root target +
    actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1
      S hfineCutoff hcoarseCoupling root target

theorem actualPositiveExpandedAssignmentSaturatedScaleDefectCross_abs_le_fullL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    Q'.abs
        (actualPositiveExpandedAssignmentSaturatedScaleDefectCross
          S hfineCutoff hcoarseCoupling root target) ≤
      actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedAssignmentSaturatedScaleDefectCross
    actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
    positiveExpandedFourCellSourceAssignmentSaturatedScaleDefectMass
    positiveExpandedFourCellTargetAssignmentSaturatedScaleDefectMass
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellSourcePairs S.coarse root target))
      (-listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellTargetPairs S.coarse root target)))
    (Q'.add_le_add
      (abs_listQSum_le_sum_abs_local _ _)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_neg'
            (listQSum
              (fun receiver =>
                positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
                    S hfineCutoff hcoarseCoupling root target receiver *
                  slabObservableTwoReplicaPairWeight S.coarse receiver)
              (slabObservableFourCellTargetPairs
                S.coarse root target))))
        (abs_listQSum_le_sum_abs_local _ _)))

theorem physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect_abs_le_fullScaleDefectL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    Q'.abs
        (physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
          S hfineCutoff hcoarseCoupling M) ≤
      Q'.abs
          (S.coarse.physicalPartition * S.fine.physicalPartition) *
        actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect_eqv_scaleDefect
          S hfineCutoff hcoarseCoupling M)))
    (Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        (S.coarse.physicalPartition * S.fine.physicalPartition)
        (actualPositiveExpandedAssignmentSaturatedScaleDefectCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget))
      (Q'.mul_le_mul_of_nonneg_left _ _
        (Q'.abs
          (S.coarse.physicalPartition * S.fine.physicalPartition))
        (actualPositiveExpandedAssignmentSaturatedScaleDefectCross_abs_le_fullL1
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)
        (Q'.abs_nonneg _)))

#print axioms positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
#print axioms positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
#print axioms actualPositiveExpandedAssignmentSaturatedScaleDefectCross
#print axioms actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv
#print axioms physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect_eqv_scaleDefect
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturatedScaleDefect
#print axioms actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
#print axioms actualPositiveExpandedAssignmentSaturatedScaleDefectCross_abs_le_fullL1
#print axioms physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect_abs_le_fullScaleDefectL1

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
