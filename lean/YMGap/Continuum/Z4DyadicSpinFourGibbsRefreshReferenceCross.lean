/-
# The coarse Gibbs refresh as a concrete normalization-preserving reference

The normalization-preserving interface becomes concrete if every fine source
uses the same target row: the normalized physical coarse Gibbs law.  The
generic finite proportional-kernel theorem proves constructively that this
row is nonnegative and normalized, and that pushing the actual fine raw law
through it gives

  refreshRawMass(y) = (Z_f / Z_c) * coarsePhysicalTerm(y).

Hence its four-cell determinant is `(Z_f / Z_c)^2` times the literal coarse
four-cell determinant.  After the `Z_c^2` scale factor is restored, the
reference blocking defect is exactly zero.  The full raw-column scale defect
therefore becomes

  Z_c^2 * (refreshCross - physicalKernelCross).

This removes both the global coupling-one partition drift and the separate
reference-blocking calibration.  It leaves one honest signed-cross estimate
between a concrete rank-one Gibbs refresh and the production physical kernel.

The refresh is deliberately not packaged as `FiniteSlabKernel`: that type
requires source dependence, whereas this ideal comparison row is rank one.
All statements below are nevertheless on the literal physical
`EdgeLabelling` carriers and include row normalization and reflection
intertwining.  No quadratic estimate, volume uniformity, all-cutoff
persistence, continuum measure, OS/GNS construction, Hamiltonian gap, or
Yang--Mills mass gap is asserted here.

Constructive contract: finite rational sums, positive rational division,
and exact rational algebra only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.FiniteWeightedProportionalKernel
import YMGap.Continuum.Z4DyadicSpinFourNormalizationPreservingReferenceKernel

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteWeightedProportionalKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect
open YMGap.Continuum.Z4DyadicSpinFourNormalizationPreservingReferenceKernel
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

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

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_four_regroup_local (A B C D : Q') :
    (A * B) * (C * D) ≈ (A * C) * (B * D) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem mul_sub_eqv_local (scale left right : Q') :
    scale * (left - right) ≈ scale * left - scale * right := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv scale left (-right)) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv scale right)

private theorem finiteWeightedFourCellCrossNumerator_eqv_of_weight_eqv
    {A : Type} (states : List A) (left right : A → Q')
    (hweight : ∀ state, left state ≈ right state)
    (first second : A → Bool) :
    finiteWeightedFourCellCrossNumerator states left first second ≈
      finiteWeightedFourCellCrossNumerator states right first second := by
  have htt :
      finiteWeightedTT states left first second ≈
        finiteWeightedTT states right first second := by
    unfold finiteWeightedTT finiteWeightedEventMass
    exact listQSum_congr hweight _
  have htf :
      finiteWeightedTF states left first second ≈
        finiteWeightedTF states right first second := by
    unfold finiteWeightedTF finiteWeightedEventMass
    exact listQSum_congr hweight _
  have hft :
      finiteWeightedFT states left first second ≈
        finiteWeightedFT states right first second := by
    unfold finiteWeightedFT finiteWeightedEventMass
    exact listQSum_congr hweight _
  have hff :
      finiteWeightedFF states left first second ≈
        finiteWeightedFF states right first second := by
    unfold finiteWeightedFF finiteWeightedEventMass
    exact listQSum_congr hweight _
  unfold finiteWeightedFourCellCrossNumerator
  exact sub_eqv_both_local
    (mul_eqv_both_local htt hff)
    (mul_eqv_both_local hft htf)

private theorem finiteWeightedFourCellCrossNumerator_scale_left
    {A : Type} (states : List A) (weight : A → Q')
    (scale : Q') (first second : A → Bool) :
    finiteWeightedFourCellCrossNumerator states
        (fun state => scale * weight state) first second ≈
      (scale * scale) *
        finiteWeightedFourCellCrossNumerator
          states weight first second := by
  let tt := finiteWeightedTT states weight first second
  let tf := finiteWeightedTF states weight first second
  let ft := finiteWeightedFT states weight first second
  let ff := finiteWeightedFF states weight first second
  have htt :
      finiteWeightedTT states (fun state => scale * weight state)
          first second ≈ scale * tt := by
    unfold finiteWeightedTT finiteWeightedEventMass tt
    exact listQSum_mul_left scale weight _
  have htf :
      finiteWeightedTF states (fun state => scale * weight state)
          first second ≈ scale * tf := by
    unfold finiteWeightedTF finiteWeightedEventMass tf
    exact listQSum_mul_left scale weight _
  have hft :
      finiteWeightedFT states (fun state => scale * weight state)
          first second ≈ scale * ft := by
    unfold finiteWeightedFT finiteWeightedEventMass ft
    exact listQSum_mul_left scale weight _
  have hff :
      finiteWeightedFF states (fun state => scale * weight state)
          first second ≈ scale * ff := by
    unfold finiteWeightedFF finiteWeightedEventMass ff
    exact listQSum_mul_left scale weight _
  refine Q'.eqv_trans _
    ((scale * tt) * (scale * ff) -
      (scale * ft) * (scale * tf)) _ ?_ ?_
  · unfold finiteWeightedFourCellCrossNumerator
    exact sub_eqv_both_local
      (mul_eqv_both_local htt hff)
      (mul_eqv_both_local hft htf)
  · change
      (scale * tt) * (scale * ff) - (scale * ft) * (scale * tf) ≈
        (scale * scale) * (tt * ff - ft * tf)
    refine Q'.eqv_trans _
      ((scale * scale) * (tt * ff) -
        (scale * scale) * (ft * tf)) _ ?_ ?_
    · exact sub_eqv_both_local
        (mul_four_regroup_local scale tt scale ff)
        (mul_four_regroup_local scale ft scale tf)
    · exact Q'.eqv_symm
        (mul_sub_eqv_local (scale * scale) (tt * ff) (ft * tf))

private theorem physicalPartitionSquare_nonnegative
    (D : SlabPhysicalData) :
    (0 : Q') ≤ D.physicalPartition * D.physicalPartition :=
  Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

/-! ## 1. The concrete proportional Gibbs row -/

theorem coarsePhysicalTermTotal_pos (S : SlabScalePair) :
    (0 : Q') <
      listQSum S.coarse.physicalTerm S.coarse.physicalLabellings := by
  change (0 : Q') < S.coarse.physicalPartition
  exact slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent

/-- Ratio of actual fine raw mass to actual coarse raw mass. -/
def fineToCoarsePhysicalPartitionRatio (S : SlabScalePair) : Q' :=
  Q'.divPos
    (listQSum S.fine.physicalTerm S.fine.physicalLabellings)
    (listQSum S.coarse.physicalTerm S.coarse.physicalLabellings)
    (coarsePhysicalTermTotal_pos S)

/-- The ideal reference row: the normalized coarse physical Gibbs law,
independent of the fine source. -/
def coarseGibbsRefreshKernel
    (S : SlabScalePair) (_source target : EdgeLabelling) : Q' :=
  normalizedTargetWeight
    S.coarse.physicalTerm S.coarse.physicalLabellings
    (coarsePhysicalTermTotal_pos S) target

theorem coarseGibbsRefreshKernel_nonnegative
    (S : SlabScalePair) (source target : EdgeLabelling) :
    (0 : Q') ≤ coarseGibbsRefreshKernel S source target := by
  unfold coarseGibbsRefreshKernel
  exact normalizedTargetWeight_nonnegative
    S.coarse.physicalTerm S.coarse.physicalLabellings
    (coarsePhysicalTermTotal_pos S)
    (fun state => slabParametricKPhysicalTerm_nonnegative
      S.coarse.coupling_nonnegative S.coarse.cutoff
      S.coarse.extent state)
    target

theorem coarseGibbsRefreshKernel_row_normalized
    (S : SlabScalePair) (source : EdgeLabelling) :
    listQSum (coarseGibbsRefreshKernel S source)
        S.coarse.physicalLabellings ≈ 1 := by
  unfold coarseGibbsRefreshKernel
  exact normalizedTargetWeight_total_one
    S.coarse.physicalTerm S.coarse.physicalLabellings
    (coarsePhysicalTermTotal_pos S)

theorem coarseGibbsRefreshKernel_reflection_intertwines
    (S : SlabScalePair) (source target : EdgeLabelling)
    (_hsource : source ∈ S.fine.physicalLabellings)
    (htarget : target ∈ S.coarse.physicalLabellings) :
    coarseGibbsRefreshKernel S
        (S.fine.reflectLabelling source)
        (S.coarse.reflectLabelling target) ≈
      coarseGibbsRefreshKernel S source target := by
  unfold coarseGibbsRefreshKernel normalizedTargetWeight
  exact Q'.mul_eqv_congr_left _ _ _
    (S.coarse.physicalTerm_reflection htarget)

/-! ## 2. Exact pushed law and four-cell determinant -/

/-- Unnormalized target mass obtained by pushing the actual fine Gibbs raw
law through the coarse Gibbs refresh row. -/
def coarseGibbsRefreshPushedRawMass
    (S : SlabScalePair) (target : EdgeLabelling) : Q' :=
  listQSum
    (fun source =>
      S.fine.physicalTerm source *
        coarseGibbsRefreshKernel S source target)
    S.fine.physicalLabellings

/-- Each refresh column is exactly the fine/coarse partition ratio times the
literal coarse physical term. -/
theorem coarseGibbsRefreshPushedRawMass_eqv_ratio_mul_coarseTerm
    (S : SlabScalePair) (target : EdgeLabelling) :
    coarseGibbsRefreshPushedRawMass S target ≈
      fineToCoarsePhysicalPartitionRatio S *
        S.coarse.physicalTerm target := by
  unfold coarseGibbsRefreshPushedRawMass coarseGibbsRefreshKernel
    fineToCoarsePhysicalPartitionRatio
  exact proportionalWeightedColumn_eqv
    S.fine.physicalLabellings S.fine.physicalTerm
    S.coarse.physicalLabellings S.coarse.physicalTerm
    (coarsePhysicalTermTotal_pos S) target

/-- The refresh pushforward retains exactly the actual fine physical
partition, without a coupling-one or other reference partition. -/
theorem coarseGibbsRefreshPushedRawMass_total_eqv_actualFinePartition
    (S : SlabScalePair) :
    listQSum (coarseGibbsRefreshPushedRawMass S)
        S.coarse.physicalLabellings ≈
      S.fine.physicalPartition := by
  let ratio := fineToCoarsePhysicalPartitionRatio S
  have hcolumns :
      listQSum (coarseGibbsRefreshPushedRawMass S)
          S.coarse.physicalLabellings ≈
        listQSum (fun target => ratio * S.coarse.physicalTerm target)
          S.coarse.physicalLabellings :=
    listQSum_congr
      (fun target => by
        simpa only [ratio] using
          (coarseGibbsRefreshPushedRawMass_eqv_ratio_mul_coarseTerm
            S target)) _
  refine Q'.eqv_trans _
    (ratio *
      listQSum S.coarse.physicalTerm S.coarse.physicalLabellings) _
    (Q'.eqv_trans _ _ _ hcolumns
      (listQSum_mul_left ratio S.coarse.physicalTerm
        S.coarse.physicalLabellings)) ?_
  simpa only [ratio, fineToCoarsePhysicalPartitionRatio,
      SlabPhysicalData.physicalPartition] using
    (Q'.divPos_mul_eqv
      (listQSum S.fine.physicalTerm S.fine.physicalLabellings)
      (listQSum S.coarse.physicalTerm S.coarse.physicalLabellings)
      (coarsePhysicalTermTotal_pos S))

/-- Signed four-cell cross of the concrete refresh pushforward. -/
def coarseGibbsRefreshPushedRawFourCellCross
    (S : SlabScalePair) (root target : Nat) : Q' :=
  finiteWeightedFourCellCrossNumerator
    S.coarse.physicalLabellings
    (coarseGibbsRefreshPushedRawMass S)
    (slabPhysicalFacePositiveB root)
    (slabPhysicalFacePositiveB target)

/-- The refresh cross is the square partition ratio times the literal coarse
physical four-cell cross. -/
theorem coarseGibbsRefreshPushedRawFourCellCross_eqv_ratioSquare_mul_coarsePhysicalCross
    (S : SlabScalePair) (root target : Nat) :
    coarseGibbsRefreshPushedRawFourCellCross S root target ≈
      (fineToCoarsePhysicalPartitionRatio S *
          fineToCoarsePhysicalPartitionRatio S) *
        physicalFaceRawFourCellCross S.coarse root target := by
  let ratio := fineToCoarsePhysicalPartitionRatio S
  refine Q'.eqv_trans _
    (finiteWeightedFourCellCrossNumerator
      S.coarse.physicalLabellings
      (fun state => ratio * S.coarse.physicalTerm state)
      (slabPhysicalFacePositiveB root)
      (slabPhysicalFacePositiveB target)) _ ?_ ?_
  · unfold coarseGibbsRefreshPushedRawFourCellCross
    exact finiteWeightedFourCellCrossNumerator_eqv_of_weight_eqv
      S.coarse.physicalLabellings
      (coarseGibbsRefreshPushedRawMass S)
      (fun state => ratio * S.coarse.physicalTerm state)
      (fun state => by
        simpa only [ratio] using
          (coarseGibbsRefreshPushedRawMass_eqv_ratio_mul_coarseTerm
            S state))
      (slabPhysicalFacePositiveB root)
      (slabPhysicalFacePositiveB target)
  · simpa only [ratio, physicalFaceRawFourCellCross] using
      (finiteWeightedFourCellCrossNumerator_scale_left
        S.coarse.physicalLabellings S.coarse.physicalTerm ratio
        (slabPhysicalFacePositiveB root)
        (slabPhysicalFacePositiveB target))

/-! ## 3. Vanishing reference defect and one-input compiler -/

/-- Restoring the coarse partition square cancels the refresh denominator
exactly and gives fine-partition-square times the literal coarse cross. -/
theorem coarsePartitionSquare_mul_refreshCross_eqv_finePartitionSquare_mul_coarseCross
    (S : SlabScalePair) (root target : Nat) :
    (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        coarseGibbsRefreshPushedRawFourCellCross S root target ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
        coarseObservableFourCellRawColumnCross S root target := by
  let fineZ := S.fine.physicalPartition
  let coarseZ := S.coarse.physicalPartition
  let ratio := fineToCoarsePhysicalPartitionRatio S
  let physicalCross := physicalFaceRawFourCellCross S.coarse root target
  let coarseCross := coarseObservableFourCellRawColumnCross S root target
  have hrefresh :
      coarseGibbsRefreshPushedRawFourCellCross S root target ≈
        (ratio * ratio) * physicalCross := by
    simpa only [ratio, physicalCross] using
      (coarseGibbsRefreshPushedRawFourCellCross_eqv_ratioSquare_mul_coarsePhysicalCross
        S root target)
  have hratio : ratio * coarseZ ≈ fineZ := by
    simpa only [ratio, fineZ, coarseZ,
        fineToCoarsePhysicalPartitionRatio,
        SlabPhysicalData.physicalPartition] using
      (Q'.divPos_mul_eqv
        (listQSum S.fine.physicalTerm S.fine.physicalLabellings)
        (listQSum S.coarse.physicalTerm S.coarse.physicalLabellings)
        (coarsePhysicalTermTotal_pos S))
  have hcross : physicalCross ≈ coarseCross := by
    refine Q'.eqv_trans _
      (physicalReceiverPairFourCellCross S.coarse root target) _ ?_ ?_
    · simpa only [physicalCross] using
        (physicalFaceRawFourCellCross_eqv_receiverPairCross
          S.coarse root target)
    · simp only [physicalReceiverPairFourCellCross,
        coarseObservableFourCellRawColumnCross, coarseCross]
      exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    ((coarseZ * coarseZ) * ((ratio * ratio) * physicalCross)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (coarseZ * coarseZ) _ _ hrefresh
  refine Q'.eqv_trans _
    (((ratio * coarseZ) * (ratio * coarseZ)) * physicalCross) _
    (by ring_qeqv) ?_
  exact mul_eqv_both_local
    (mul_eqv_both_local hratio hratio) hcross

/-- The concrete refresh reference blocking defect is exactly zero. -/
theorem coarseGibbsRefreshRawColumnScaleDefect_eqv_zero
    (S : SlabScalePair) (root target : Nat) :
    (S.fine.physicalPartition * S.fine.physicalPartition) *
          coarseObservableFourCellRawColumnCross S root target -
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          coarseGibbsRefreshPushedRawFourCellCross S root target ≈
      0 := by
  have hscaled :=
    coarsePartitionSquare_mul_refreshCross_eqv_finePartitionSquare_mul_coarseCross
      S root target
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) *
          coarseObservableFourCellRawColumnCross S root target -
      (S.fine.physicalPartition * S.fine.physicalPartition) *
          coarseObservableFourCellRawColumnCross S root target) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _) hscaled
  · exact Q'.add_neg_self_eqv _

/-- The full raw-column scale defect is exactly the coarse partition square
times the refresh-versus-production signed-cross discrepancy. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_refresh_sub_physicalKernel
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (coarseGibbsRefreshPushedRawFourCellCross S root target -
          pushedFaceRawFourCellCross
            (physicalKernel S hfineCutoff hcoarseCoupling)
            root target) := by
  let fineSquare := S.fine.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let coarseCross := coarseObservableFourCellRawColumnCross S root target
  let receiverCross :=
    positiveExpandedAssignmentSaturatedReceiverRawColumnCross
      S hfineCutoff hcoarseCoupling root target
  let actualCross :=
    pushedFaceRawFourCellCross
      (physicalKernel S hfineCutoff hcoarseCoupling) root target
  let refreshCross := coarseGibbsRefreshPushedRawFourCellCross S root target
  have hbase :
      positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
          S hfineCutoff hcoarseCoupling root target ≈
        fineSquare * coarseCross - coarseSquare * receiverCross := by
    simpa only [fineSquare, coarseSquare, coarseCross, receiverCross] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_crosses
        S hfineCutoff hcoarseCoupling root target)
  have hreceiver : receiverCross ≈ actualCross := by
    simpa only [receiverCross, actualCross] using
      (receiverRawColumnCross_eqv_physicalKernelPushedCross
        S hfineCutoff hcoarseCoupling root target)
  have hrefresh : coarseSquare * refreshCross ≈ fineSquare * coarseCross := by
    simpa only [coarseSquare, refreshCross, fineSquare, coarseCross] using
      (coarsePartitionSquare_mul_refreshCross_eqv_finePartitionSquare_mul_coarseCross
        S root target)
  refine Q'.eqv_trans _
    (fineSquare * coarseCross - coarseSquare * receiverCross) _ hbase ?_
  refine Q'.eqv_trans _
    (fineSquare * coarseCross - coarseSquare * actualCross) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left coarseSquare _ _ hreceiver)
  refine Q'.eqv_trans _
    (coarseSquare * refreshCross - coarseSquare * actualCross) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_symm hrefresh) (Q'.eqv_refl _)
  · change
      coarseSquare * refreshCross + -(coarseSquare * actualCross) ≈
        coarseSquare * (refreshCross + -actualCross)
    refine Q'.eqv_trans _
      (coarseSquare * refreshCross + coarseSquare * (-actualCross)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.mul_neg_eqv coarseSquare actualCross))
    · exact Q'.eqv_symm
        (Q'.mul_add_eqv coarseSquare refreshCross (-actualCross))

/-- The sole remaining analytic input on the Gibbs-refresh branch. -/
def CoarseGibbsRefreshPhysicalKernelCrossCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (coarseGibbsRefreshPushedRawFourCellCross S root target -
        pushedFaceRawFourCellCross
          (physicalKernel S hfineCutoff hcoarseCoupling) root target) ≤
    (kernelCeiling * (g * g)) *
      (S.fine.physicalPartition * S.fine.physicalPartition)

/-- A quadratic signed-cross comparison with the concrete Gibbs refresh
directly inhabits the aggregate raw-column calibration. -/
theorem positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefresh
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (g kernelCeiling : Q')
    (hkernel :
      CoarseGibbsRefreshPhysicalKernelCrossCalibration
        S hfineCutoff hcoarseCoupling root target g kernelCeiling) :
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
      S hfineCutoff hcoarseCoupling root target
        (kernelCeiling * (g * g)) := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let discrepancy :=
    coarseGibbsRefreshPushedRawFourCellCross S root target -
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target
  have heq :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_refresh_sub_physicalKernel
      S hfineCutoff hcoarseCoupling root target
  have habs :
      Q'.abs
          (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
            S hfineCutoff hcoarseCoupling root target) ≤
        coarseSquare * Q'.abs discrepancy := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr
        (by simpa only [coarseSquare, discrepancy] using heq)))
      (Q'.le_trans' _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
          coarseSquare discrepancy) ?_)
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
          (by
            simpa only [coarseSquare] using
              (physicalPartitionSquare_nonnegative S.coarse))))
  have hscaled :
      coarseSquare * Q'.abs discrepancy ≤
        coarseSquare *
          ((kernelCeiling * (g * g)) * fineSquare) :=
    Q'.mul_le_mul_of_nonneg_left _ _ coarseSquare
      (by simpa only [CoarseGibbsRefreshPhysicalKernelCrossCalibration,
          discrepancy, fineSquare] using hkernel)
      (by
        simpa only [coarseSquare] using
          (physicalPartitionSquare_nonnegative S.coarse))
  refine Q'.le_trans' _ _ _ habs
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
  simp only [coarseSquare, fineSquare]
  ring_qeqv

#print axioms coarsePhysicalTermTotal_pos
#print axioms fineToCoarsePhysicalPartitionRatio
#print axioms coarseGibbsRefreshKernel
#print axioms coarseGibbsRefreshKernel_nonnegative
#print axioms coarseGibbsRefreshKernel_row_normalized
#print axioms coarseGibbsRefreshKernel_reflection_intertwines
#print axioms coarseGibbsRefreshPushedRawMass
#print axioms coarseGibbsRefreshPushedRawMass_eqv_ratio_mul_coarseTerm
#print axioms coarseGibbsRefreshPushedRawMass_total_eqv_actualFinePartition
#print axioms coarseGibbsRefreshPushedRawFourCellCross
#print axioms coarseGibbsRefreshPushedRawFourCellCross_eqv_ratioSquare_mul_coarsePhysicalCross
#print axioms coarsePartitionSquare_mul_refreshCross_eqv_finePartitionSquare_mul_coarseCross
#print axioms coarseGibbsRefreshRawColumnScaleDefect_eqv_zero
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_refresh_sub_physicalKernel
#print axioms CoarseGibbsRefreshPhysicalKernelCrossCalibration
#print axioms positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefresh

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross
