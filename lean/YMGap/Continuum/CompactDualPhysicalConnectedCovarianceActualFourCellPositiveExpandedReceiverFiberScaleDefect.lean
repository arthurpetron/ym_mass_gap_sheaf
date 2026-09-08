/-
# Partition-scaled receiver-fiber coefficient defect

The supported covariance paths have been aggregated into exact density loads
on the complete coarse receiver source and target carriers.  The connected
raw-cross defect, however, compares a coarse two-replica cross of scale
`Z_coarse^2` with a pushed cross of scale `Z_fine^2`.  A receiver-column
comparison must therefore transport the partition-scaled coefficient

  Z_fine^2 - receiverFiberDensity * Z_coarse^2,

not the unscaled density alone.

This module first identifies the physical coarse four-cell cross with the
same complete receiver-pair source-minus-target cross used by the path
orientation.  It then packages the correctly scaled coefficient field and
factors the complete connected raw-cross defect through it.

No estimate for that coefficient field is asserted.  In particular this
module proves no `O(a)` bound, continuum measure, OS/GNS reconstruction, or
physical mass gap.

Constructive contract: exact finite rational disintegration and polynomial
identities only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
import YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-! ## 1. The coarse physical cross on the receiver-pair carrier -/

def physicalReceiverPairFourCellCross
    (D : SlabPhysicalData) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservableFourCellSourcePairs D root target) -
    listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservableFourCellTargetPairs D root target)

/-- The physical-labelling four-cell determinant is exactly the difference
of the complete receiver source- and target-pair masses. -/
theorem physicalFaceRawFourCellCross_eqv_receiverPairCross
    (D : SlabPhysicalData) (root target : Nat) :
    physicalFaceRawFourCellCross D root target ≈
      physicalReceiverPairFourCellCross D root target := by
  let physicalStates := D.physicalLabellings
  let physicalWeight := D.physicalTerm
  let physicalRoot := slabPhysicalFacePositiveB root
  let physicalTarget := slabPhysicalFacePositiveB target
  let expandedStates := slabExpandedFineSources D
  let expandedWeight := slabExpandedFineSourceWeight D
  let expandedRoot := slabObservableRawFacePositiveB root
  let expandedTarget := slabObservableRawFacePositiveB target
  have htt :
      finiteWeightedTT expandedStates expandedWeight
          expandedRoot expandedTarget ≈
        finiteWeightedTT physicalStates physicalWeight
          physicalRoot physicalTarget := by
    simpa only [finiteWeightedTT, expandedStates, expandedWeight,
        expandedRoot, expandedTarget, physicalStates, physicalWeight,
        physicalRoot, physicalTarget, slabObservableRawFacePositiveB,
        slabPhysicalFacePositiveB] using
      (slabExpandedPhysicalEventMass_eqv D
        (fun physical =>
          slabPhysicalFacePositiveB root physical &&
            slabPhysicalFacePositiveB target physical))
  have htf :
      finiteWeightedTF expandedStates expandedWeight
          expandedRoot expandedTarget ≈
        finiteWeightedTF physicalStates physicalWeight
          physicalRoot physicalTarget := by
    simpa only [finiteWeightedTF, expandedStates, expandedWeight,
        expandedRoot, expandedTarget, physicalStates, physicalWeight,
        physicalRoot, physicalTarget, slabObservableRawFacePositiveB,
        slabPhysicalFacePositiveB] using
      (slabExpandedPhysicalEventMass_eqv D
        (fun physical =>
          slabPhysicalFacePositiveB root physical &&
            !(slabPhysicalFacePositiveB target physical)))
  have hft :
      finiteWeightedFT expandedStates expandedWeight
          expandedRoot expandedTarget ≈
        finiteWeightedFT physicalStates physicalWeight
          physicalRoot physicalTarget := by
    simpa only [finiteWeightedFT, expandedStates, expandedWeight,
        expandedRoot, expandedTarget, physicalStates, physicalWeight,
        physicalRoot, physicalTarget, slabObservableRawFacePositiveB,
        slabPhysicalFacePositiveB] using
      (slabExpandedPhysicalEventMass_eqv D
        (fun physical =>
          !(slabPhysicalFacePositiveB root physical) &&
            slabPhysicalFacePositiveB target physical))
  have hff :
      finiteWeightedFF expandedStates expandedWeight
          expandedRoot expandedTarget ≈
        finiteWeightedFF physicalStates physicalWeight
          physicalRoot physicalTarget := by
    simpa only [finiteWeightedFF, expandedStates, expandedWeight,
        expandedRoot, expandedTarget, physicalStates, physicalWeight,
        physicalRoot, physicalTarget, slabObservableRawFacePositiveB,
        slabPhysicalFacePositiveB] using
      (slabExpandedPhysicalEventMass_eqv D
        (fun physical =>
          !(slabPhysicalFacePositiveB root physical) &&
            !(slabPhysicalFacePositiveB target physical)))
  have hphysicalExpanded :
      physicalFaceRawFourCellCross D root target ≈
        finiteWeightedFourCellCrossNumerator
          expandedStates expandedWeight expandedRoot expandedTarget := by
    unfold physicalFaceRawFourCellCross
      finiteWeightedFourCellCrossNumerator
    exact sub_eqv_both_local
      (mul_eqv_both_local (Q'.eqv_symm htt) (Q'.eqv_symm hff))
      (mul_eqv_both_local (Q'.eqv_symm hft) (Q'.eqv_symm htf))
  have httEntries :=
    slabObservableRootTargetEntries_weight_eqv_TT D root target
  have htfEntries :=
    slabObservableRootTargetComplementEntries_weight_eqv_TF D root target
  have hftEntries :=
    slabObservableRootComplementTargetEntries_weight_eqv_FT D root target
  have hffEntries :=
    slabObservableRootComplementTargetComplementEntries_weight_eqv_FF
      D root target
  have hexpandedEntries :
      finiteWeightedFourCellCrossNumerator
          expandedStates expandedWeight expandedRoot expandedTarget ≈
        listQSum (slabObservablePositiveEntryWeight D)
              (slabObservableRootTargetEntries D root target) *
            listQSum (slabExpandedFineEntryWeight D)
              (slabObservableRootComplementTargetComplementEntries
                D root target) -
          listQSum (slabObservablePositiveEntryWeight D)
              (slabObservableRootTargetComplementEntries D root target) *
            listQSum (slabExpandedFineEntryWeight D)
              (slabObservableRootComplementTargetEntries D root target) := by
    unfold finiteWeightedFourCellCrossNumerator
    exact sub_eqv_both_local
      (mul_eqv_both_local
        (Q'.eqv_symm httEntries) (Q'.eqv_symm hffEntries))
      (Q'.eqv_trans _ _ _
        (mul_eqv_both_local
          (Q'.eqv_symm hftEntries) (Q'.eqv_symm htfEntries))
        (Q'.mul_comm_eqv _ _))
  have hsource :=
    slabObservableFourCellSourcePairs_weight_product D root target
  have htarget :=
    slabObservableFourCellTargetPairs_weight_product D root target
  exact Q'.eqv_trans _ _ _ hphysicalExpanded
    (Q'.eqv_trans _ _ _ hexpandedEntries
      (Q'.eqv_trans _ _ _
        (sub_eqv_both_local (Q'.eqv_symm hsource) (Q'.eqv_symm htarget))
        (Q'.eqv_refl _)))

/-! ## 2. The correctly partition-scaled receiver coefficients -/

/-- Coefficient mismatch carried by one source-cell receiver pair after both
two-replica crosses are put in the same partition units. -/
def positiveExpandedFourCellSourceReceiverFiberScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  S.fine.physicalPartition * S.fine.physicalPartition -
    positiveExpandedFourCellSourceReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver *
      (S.coarse.physicalPartition * S.coarse.physicalPartition)

/-- Coefficient mismatch carried by one target-cell receiver pair. -/
def positiveExpandedFourCellTargetReceiverFiberScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  S.fine.physicalPartition * S.fine.physicalPartition -
    positiveExpandedFourCellTargetReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver *
      (S.coarse.physicalPartition * S.coarse.physicalPartition)

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

private theorem scaledDensityWeight_reorder
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
    (coarseCross fiberCross coarsePartition finePartition : Q') :
    (coarseCross * coarsePartition) *
          (finePartition * (finePartition * finePartition)) +
        -(
        (fiberCross * finePartition) *
          (coarsePartition * (coarsePartition * coarsePartition))) ≈
      (coarsePartition * finePartition) *
        ((finePartition * finePartition) * coarseCross +
          -((coarsePartition * coarsePartition) * fiberCross)) := by
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
          scaledDensityWeight_reorder
            (density item) coarseSquare (weight item)))
      (listQSum_mul_left coarseSquare
        (fun item => density item * weight item) items))

/-- The complete source-cell contribution of the scaled coefficient field. -/
def positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      positiveExpandedFourCellSourceReceiverFiberScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver)
    (slabObservableFourCellSourcePairs S.coarse root target)

theorem positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellSourcePairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellSourceReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellSourcePairs S.coarse root target) := by
  unfold positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
    positiveExpandedFourCellSourceReceiverFiberScaleDefect
  exact listQSum_scaledDensityDefect_local
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (S.coarse.physicalPartition * S.coarse.physicalPartition)
    (positiveExpandedFourCellSourceReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target)
    (slabObservableTwoReplicaPairWeight S.coarse)
    (slabObservableFourCellSourcePairs S.coarse root target)

/-- The complete target-cell contribution of the scaled coefficient field. -/
def positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      positiveExpandedFourCellTargetReceiverFiberScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver)
    (slabObservableFourCellTargetPairs S.coarse root target)

theorem positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellTargetPairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellTargetReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellTargetPairs S.coarse root target) := by
  unfold positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
    positiveExpandedFourCellTargetReceiverFiberScaleDefect
  exact listQSum_scaledDensityDefect_local
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (S.coarse.physicalPartition * S.coarse.physicalPartition)
    (positiveExpandedFourCellTargetReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target)
    (slabObservableTwoReplicaPairWeight S.coarse)
    (slabObservableFourCellTargetPairs S.coarse root target)

/-! ## 3. The complete scaled coefficient cross -/

def actualPositiveExpandedReceiverFiberScaleDefectCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
      S hfineCutoff hcoarseCoupling root target -
    positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
      S hfineCutoff hcoarseCoupling root target

theorem actualPositiveExpandedReceiverFiberScaleDefectCross_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          physicalReceiverPairFourCellCross S.coarse root target -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
            S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectCross
    physicalReceiverPairFourCellCross
    actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
  refine Q'.eqv_trans _
    (((S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellSourcePairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellSourceReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellSourcePairs S.coarse root target)) -
      ((S.fine.physicalPartition * S.fine.physicalPartition) *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellTargetPairs S.coarse root target) -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          listQSum
            (fun receiver =>
              positiveExpandedFourCellTargetReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver *
                slabObservableTwoReplicaPairWeight S.coarse receiver)
            (slabObservableFourCellTargetPairs S.coarse root target))) _ ?_ ?_
  · exact sub_eqv_both_local
      (positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_eqv
        S hfineCutoff hcoarseCoupling root target)
      (positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_eqv
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
          positiveExpandedFourCellSourceReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellSourcePairs S.coarse root target))
      (listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellTargetPairs S.coarse root target))

/-- The full connected raw-cross defect is the common positive partition
factor `Z_coarse * Z_fine` times the receiver-fiber scaled coefficient cross. -/
theorem physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect_eqv_scaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      (S.coarse.physicalPartition * S.fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget := by
  let coarseCross :=
    physicalReceiverPairFourCellCross
      S.coarse M.coarseRoot M.coarseTarget
  let fiberCross :=
    actualPositiveExpandedReceiverFiberWeightedFaceRawFourCellPathCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  have hcoarse :=
    physicalFaceRawFourCellCross_eqv_receiverPairCross
      S.coarse M.coarseRoot M.coarseTarget
  have hscale :=
    actualPositiveExpandedReceiverFiberScaleDefectCross_eqv
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  unfold physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect
    rawCovarianceDenominator
  refine Q'.eqv_trans _
    ((coarseCross * S.coarse.physicalPartition) *
          (S.fine.physicalPartition *
            (S.fine.physicalPartition * S.fine.physicalPartition)) -
      (fiberCross * S.fine.physicalPartition) *
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
          fiberCross)) _ ?_ ?_
  · exact factorPartitionScaledCrosses_local
      coarseCross fiberCross
      S.coarse.physicalPartition S.fine.physicalPartition
  · exact Q'.mul_eqv_congr_left
      (S.coarse.physicalPartition * S.fine.physicalPartition) _ _
      (Q'.eqv_symm hscale)

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverFiberScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      (S.coarse.physicalPartition * S.fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverFiberWeighted
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect_eqv_scaleDefect
      S hfineCutoff hcoarseCoupling M)

#print axioms physicalReceiverPairFourCellCross
#print axioms physicalFaceRawFourCellCross_eqv_receiverPairCross
#print axioms positiveExpandedFourCellSourceReceiverFiberScaleDefect
#print axioms positiveExpandedFourCellTargetReceiverFiberScaleDefect
#print axioms positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
#print axioms positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_eqv
#print axioms positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
#print axioms positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_eqv
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross_eqv
#print axioms physicalConnectedCovariancePositiveExpandedReceiverFiberWeightedRawCrossDefect_eqv_scaleDefect
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverFiberScaleDefect

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
