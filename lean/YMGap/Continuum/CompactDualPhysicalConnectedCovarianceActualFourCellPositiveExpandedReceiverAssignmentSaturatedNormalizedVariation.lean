/-
# Normalize the assignment-saturated receiver variation

The assignment-saturated scale-defect cross is controlled by a source-plus-
target `l1` sum in the exact units `Z_fine^2`.  This module divides that sum
by the strictly positive fine partition square and proves the useful exact
decomposition

  normalized saturated variation
    ~= covered saturated calibration
         + physically unreachable endpoint mass.

Outside the saturated image, finite zero extension makes the density exactly
zero.  The scale-defect coefficient there is therefore exactly `Z_fine^2`,
so positive division removes it without a receiver-cardinality factor.  By
the preceding physical-image theorem, this uncovered term refers only to
coarse physical endpoint pairs and not to auxiliary intertwiner assignments.

No covered calibration estimate, endpoint-reachability estimate, `O(g^2)`
bound, continuum measure, OS/GNS reconstruction, or Yang--Mills mass gap is
proved here.

Constructive contract: exact finite zero extension, rational division, and
finite sums only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance assignmentSaturatedVariationReceiverDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair S.coarse root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem not_of_not_decide_eq_true_local
    {P : Prop} [Decidable P] (hP : (!decide P) = true) : ¬ P := by
  have hfalse : decide P = false := by
    cases hdecision : decide P with
    | false => rfl
    | true =>
        rw [hdecision] at hP
        cases hP
  exact decide_eq_false_iff_not.mp hfalse

private theorem listQSum_eqv_covered_add_scale_mul_uncovered_local
    {A : Type} [DecidableEq A]
    (items image : List A) (term weight : A → Q') (scale : Q')
    (houtside : ∀ item, item ∉ image → term item ≈ scale * weight item) :
    listQSum term items ≈
      listQSum term
          (items.filter (fun item => decide (item ∈ image))) +
        scale * listQSum weight
          (items.filter (fun item => !(decide (item ∈ image)))) := by
  let test : A → Bool := fun item => decide (item ∈ image)
  have hpartition := listQSum_filter_partition term test items
  refine Q'.eqv_trans _
    (listQSum term (items.filter test) +
      listQSum term (items.filter (fun item => !(test item)))) _
    hpartition ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _
    (listQSum (fun item => scale * weight item)
      (items.filter (fun item => !(test item)))) _ ?_ ?_
  · apply listQSum_congr_on
    intro item hitem
    have hparts := List.mem_filter.mp hitem
    have hnotImage : item ∉ image := by
      apply not_of_not_decide_eq_true_local
      simpa only [test] using hparts.2
    exact houtside item hnotImage
  · simpa only [test] using
      (listQSum_mul_left scale weight
        (items.filter (fun item => !(test item))))

private theorem divPos_eqv_divPos_add_of_eqv_add_mul_local
    (full covered scale uncovered : Q')
    (hscale : (0 : Q') < scale)
    (hfull : full ≈ covered + scale * uncovered) :
    Q'.divPos full scale hscale ≈
      Q'.divPos covered scale hscale + uncovered := by
  let fullVariation := Q'.divPos full scale hscale
  let coveredVariation := Q'.divPos covered scale hscale
  have hfullVariation : fullVariation * scale ≈ full :=
    Q'.divPos_mul_eqv full scale hscale
  have hcoveredVariation : coveredVariation * scale ≈ covered :=
    Q'.divPos_mul_eqv covered scale hscale
  apply Q'.mul_left_cancel_of_pos hscale
  refine Q'.eqv_trans _ full _ ?_ ?_
  · exact Q'.eqv_trans _ (fullVariation * scale) _
      (Q'.mul_comm_eqv scale fullVariation) hfullVariation
  refine Q'.eqv_trans _ (covered + scale * uncovered) _ hfull ?_
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (scale * coveredVariation + scale * uncovered) _
    (Q'.mul_add_eqv scale coveredVariation uncovered) ?_
  exact Q'.add_eqv_congr_right _ _ (scale * uncovered)
    (Q'.eqv_trans _ (coveredVariation * scale) _
      (Q'.mul_comm_eqv scale coveredVariation) hcoveredVariation)

/-! ## 1. Zero extension vanishes off the physical saturated image -/

theorem positiveExpandedFourCellSourceSaturatedReceiverLift_receiver_mem_image
    (S : SlabScalePair) (root target : Nat)
    (lift : PositiveExpandedFourCellSourceSaturatedReceiverLift
      S root target)
    (hlift : lift ∈
      positiveExpandedFourCellSourceSaturatedReceiverLifts
        S root target) :
    lift.receiver ∈
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target := by
  unfold positiveExpandedFourCellSourceSaturatedReceiverLifts at hlift
  obtain ⟨supported, hsupported, hlocal⟩ := List.mem_flatMap.mp hlift
  obtain ⟨receiver, _, heq⟩ := List.mem_map.mp hlocal
  unfold positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
  apply List.mem_flatMap.mpr
  refine ⟨supported, hsupported, ?_⟩
  rw [← heq]
  exact receiver.2

theorem positiveExpandedFourCellTargetSaturatedReceiverLift_receiver_mem_image
    (S : SlabScalePair) (root target : Nat)
    (lift : PositiveExpandedFourCellTargetSaturatedReceiverLift
      S root target)
    (hlift : lift ∈
      positiveExpandedFourCellTargetSaturatedReceiverLifts
        S root target) :
    lift.receiver ∈
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target := by
  unfold positiveExpandedFourCellTargetSaturatedReceiverLifts at hlift
  obtain ⟨supported, hsupported, hlocal⟩ := List.mem_flatMap.mp hlift
  obtain ⟨receiver, _, heq⟩ := List.mem_map.mp hlocal
  unfold positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
  apply List.mem_flatMap.mpr
  refine ⟨supported, hsupported, ?_⟩
  rw [← heq]
  exact receiver.2

theorem positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_eqv_zero_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : receiver ∉
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target) :
    positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver ≈ 0 := by
  unfold positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
  apply finiteCoefficientZeroExtension_eqv_zero_of_not_image
  intro lift hlift heq
  apply houtside
  rw [heq]
  exact
    positiveExpandedFourCellSourceSaturatedReceiverLift_receiver_mem_image
      S root target lift hlift

theorem positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_eqv_zero_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : receiver ∉
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target) :
    positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
        S hfineCutoff hcoarseCoupling root target receiver ≈ 0 := by
  unfold positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
  apply finiteCoefficientZeroExtension_eqv_zero_of_not_image
  intro lift hlift heq
  apply houtside
  rw [heq]
  exact
    positiveExpandedFourCellTargetSaturatedReceiverLift_receiver_mem_image
      S root target lift hlift

/-! ## 2. Off-image scale defects equal the fine partition square -/

theorem finePhysicalPartitionSquare_pos (S : SlabScalePair) :
    (0 : Q') <
      S.fine.physicalPartition * S.fine.physicalPartition :=
  Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)

theorem positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_eqv_fineSquare_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : receiver ∉
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target) :
    positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver ≈
      S.fine.physicalPartition * S.fine.physicalPartition := by
  unfold positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) -
      (0 : Q') *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_right _ _ _
        (positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_eqv_zero_of_not_image
          S hfineCutoff hcoarseCoupling root target receiver houtside))
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) - 0) _
    (sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.zero_mul_eqv _)) ?_
  exact Q'.eqv_of_eq
    (Q'.sub_zero'
      (S.fine.physicalPartition * S.fine.physicalPartition))

theorem positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_eqv_fineSquare_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : receiver ∉
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target) :
    positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver ≈
      S.fine.physicalPartition * S.fine.physicalPartition := by
  unfold positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) -
      (0 : Q') *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_right _ _ _
        (positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_eqv_zero_of_not_image
          S hfineCutoff hcoarseCoupling root target receiver houtside))
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) - 0) _
    (sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.zero_mul_eqv _)) ?_
  exact Q'.eqv_of_eq
    (Q'.sub_zero'
      (S.fine.physicalPartition * S.fine.physicalPartition))

private theorem sourceScaleDefectAbsTerm_eqv_fineSquare_mul_weight_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : receiver ∉
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target) :
    Q'.abs
        (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver) ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
        slabObservableTwoReplicaPairWeight S.coarse receiver := by
  refine Q'.eqv_trans _
    (Q'.abs
      ((S.fine.physicalPartition * S.fine.physicalPartition) *
        slabObservableTwoReplicaPairWeight S.coarse receiver)) _ ?_ ?_
  · exact Q'.abs_eqv_congr
      (Q'.mul_eqv_congr_right _ _ _
        (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_eqv_fineSquare_of_not_image
          S hfineCutoff hcoarseCoupling root target receiver houtside))
  exact YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt (finePhysicalPartitionSquare_pos S))
      (slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root receiver))

private theorem targetScaleDefectAbsTerm_eqv_fineSquare_mul_weight_of_not_image
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (houtside : receiver ∉
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target) :
    Q'.abs
        (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver) ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
        slabObservableTwoReplicaPairWeight S.coarse receiver := by
  refine Q'.eqv_trans _
    (Q'.abs
      ((S.fine.physicalPartition * S.fine.physicalPartition) *
        slabObservableTwoReplicaPairWeight S.coarse receiver)) _ ?_ ?_
  · exact Q'.abs_eqv_congr
      (Q'.mul_eqv_congr_right _ _ _
        (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_eqv_fineSquare_of_not_image
          S hfineCutoff hcoarseCoupling root target receiver houtside))
  exact YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt (finePhysicalPartitionSquare_pos S))
      (slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root receiver))

/-! ## 3. Exact normalized covered/unreachable decomposition -/

def actualPositiveExpandedAssignmentSaturatedSourceCoveredScaleDefectL1
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
    ((slabObservableFourCellSourcePairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
            S root target)))

def actualPositiveExpandedAssignmentSaturatedTargetCoveredScaleDefectL1
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
    ((slabObservableFourCellTargetPairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
            S root target)))

def actualPositiveExpandedAssignmentSaturatedCoveredFullScaleDefectL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  actualPositiveExpandedAssignmentSaturatedSourceCoveredScaleDefectL1
      S hfineCutoff hcoarseCoupling root target +
    actualPositiveExpandedAssignmentSaturatedTargetCoveredScaleDefectL1
      S hfineCutoff hcoarseCoupling root target

theorem actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1_eqv_covered_add_fineSquare_mul_unreachable
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedAssignmentSaturatedCoveredFullScaleDefectL1
          S hfineCutoff hcoarseCoupling root target +
        (S.fine.physicalPartition * S.fine.physicalPartition) *
          actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
            S root target := by
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let sourceTerm := fun receiver :
      SlabObservableTwoReplicaPair S.coarse root =>
    Q'.abs
      (positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver)
  let targetTerm := fun receiver :
      SlabObservableTwoReplicaPair S.coarse root =>
    Q'.abs
      (positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling root target receiver *
        slabObservableTwoReplicaPairWeight S.coarse receiver)
  have hsource :=
    listQSum_eqv_covered_add_scale_mul_uncovered_local
      (slabObservableFourCellSourcePairs S.coarse root target)
      (positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target)
      sourceTerm (slabObservableTwoReplicaPairWeight S.coarse) fineSquare
      (fun receiver houtside => by
        simpa only [sourceTerm, fineSquare] using
          sourceScaleDefectAbsTerm_eqv_fineSquare_mul_weight_of_not_image
            S hfineCutoff hcoarseCoupling root target receiver houtside)
  have htarget :=
    listQSum_eqv_covered_add_scale_mul_uncovered_local
      (slabObservableFourCellTargetPairs S.coarse root target)
      (positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target)
      targetTerm (slabObservableTwoReplicaPairWeight S.coarse) fineSquare
      (fun receiver houtside => by
        simpa only [targetTerm, fineSquare] using
          targetScaleDefectAbsTerm_eqv_fineSquare_mul_weight_of_not_image
            S hfineCutoff hcoarseCoupling root target receiver houtside)
  refine Q'.eqv_trans _
    ((actualPositiveExpandedAssignmentSaturatedSourceCoveredScaleDefectL1
          S hfineCutoff hcoarseCoupling root target +
        fineSquare *
          actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
            S root target) +
      (actualPositiveExpandedAssignmentSaturatedTargetCoveredScaleDefectL1
          S hfineCutoff hcoarseCoupling root target +
        fineSquare *
          actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
            S root target)) _ ?_ ?_
  · simpa only [
      actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1,
      actualPositiveExpandedAssignmentSaturatedSourceScaleDefectL1,
      actualPositiveExpandedAssignmentSaturatedTargetScaleDefectL1,
      actualPositiveExpandedAssignmentSaturatedSourceCoveredScaleDefectL1,
      actualPositiveExpandedAssignmentSaturatedTargetCoveredScaleDefectL1,
      actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass,
      actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass,
      sourceTerm, targetTerm, fineSquare] using
        Q'.add_eqv_congr' hsource htarget
  refine Q'.eqv_trans _
    ((actualPositiveExpandedAssignmentSaturatedSourceCoveredScaleDefectL1
          S hfineCutoff hcoarseCoupling root target +
        actualPositiveExpandedAssignmentSaturatedTargetCoveredScaleDefectL1
          S hfineCutoff hcoarseCoupling root target) +
      (fineSquare *
          actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
            S root target +
        fineSquare *
          actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
            S root target)) _ ?_ ?_
  · exact Q'.add_swap_inner _ _ _ _
  simpa only [
    actualPositiveExpandedAssignmentSaturatedCoveredFullScaleDefectL1,
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass,
    fineSquare] using
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.mul_add_eqv fineSquare
            (actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
              S root target)
            (actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
              S root target))))

def actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
      S hfineCutoff hcoarseCoupling root target)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

def actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedAssignmentSaturatedCoveredFullScaleDefectL1
      S hfineCutoff hcoarseCoupling root target)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

theorem actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_eqv_covered_add_unreachable
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling root target +
        actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
          S root target := by
  simpa only [
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1,
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1]
    using
      (divPos_eqv_divPos_add_of_eqv_add_mul_local
        (actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
          S hfineCutoff hcoarseCoupling root target)
        (actualPositiveExpandedAssignmentSaturatedCoveredFullScaleDefectL1
          S hfineCutoff hcoarseCoupling root target)
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
          S root target)
        (finePhysicalPartitionSquare_pos S)
        (actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1_eqv_covered_add_fineSquare_mul_unreachable
          S hfineCutoff hcoarseCoupling root target))

theorem actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_of_covered_and_unreachable
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (coveredBudget unreachableBudget : Q')
    (hcovered :
      actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling root target ≤ coveredBudget)
    (hunreachable :
      actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
          S root target ≤ unreachableBudget) :
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
        S hfineCutoff hcoarseCoupling root target ≤
      coveredBudget + unreachableBudget := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_eqv_covered_add_unreachable
        S hfineCutoff hcoarseCoupling root target))
    (Q'.add_le_add hcovered hunreachable)

#print axioms positiveExpandedFourCellSourceSaturatedReceiverFiberDensity_eqv_zero_of_not_image
#print axioms positiveExpandedFourCellTargetSaturatedReceiverFiberDensity_eqv_zero_of_not_image
#print axioms positiveExpandedFourCellSourceAssignmentSaturatedScaleDefect_eqv_fineSquare_of_not_image
#print axioms positiveExpandedFourCellTargetAssignmentSaturatedScaleDefect_eqv_fineSquare_of_not_image
#print axioms actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1_eqv_covered_add_fineSquare_mul_unreachable
#print axioms actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
#print axioms actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
#print axioms actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_eqv_covered_add_unreachable
#print axioms actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_of_covered_and_unreachable

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
