/-
# The connected Gibbs remainder as a selected-observable row action

The normalized connected remainder is now exposed at the source-row level.
For each fine physical source, compare the production physical-kernel action
on the established pointwise-unit-bounded connected observable with the
source-independent coarse Gibbs refresh action.  Averaging that signed row
action against the normalized fine Gibbs law is exactly the centered cylinder
remainder.

This is a strictly more local analytic interface than the full pushforward
remainder `L1`: a proof may estimate only the one selected observable and may
retain cancellation across coarse targets.  The module also records two
successively stronger sufficient inputs: the fine-weighted sum of absolute
row actions, and a pointwise row-action bound.  A full kernel-row `L1` bound
remains available as a conservative fallback.

No quadratic estimate is manufactured here.  Cutoff/volume uniformity,
continuum persistence, OS/GNS reconstruction, the Hamiltonian gap, and the
Yang--Mills mass gap remain open.

Constructive contract: finite rational Fubini, triangle inequalities, and
the existing exact physical kernels only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.FiniteRefreshSpectralComparison
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRefreshSpectralComparison
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteWeightedProportionalKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _) (listQSum_neg_local right items)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈
      factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _ ?_ ?_
  · exact Q'.mul_add_eqv factor left (-right)
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

private theorem abs_listQSum_le_sum_abs_local
    {A : Type} (value : A → Q') : ∀ items : List A,
    Q'.abs (listQSum value items) ≤
      listQSum (fun item => Q'.abs (value item)) items
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail => by
      change
        Q'.abs (value head + listQSum value tail) ≤
          Q'.abs (value head) +
            listQSum (fun item => Q'.abs (value item)) tail
      exact Q'.le_trans' _ _ _
        (abs_add_le (value head) (listQSum value tail))
        (Q'.add_le_add_left _ _ _
          (abs_listQSum_le_sum_abs_local value tail))

private theorem abs_mul_nonnegative_left_eqv_local
    (factor value : Q') (hfactor : (0 : Q') ≤ factor) :
    Q'.abs (factor * value) ≈ factor * Q'.abs value := by
  refine Q'.eqv_trans _ (Q'.abs (value * factor)) _
    (Q'.abs_eqv_congr (Q'.mul_comm_eqv factor value)) ?_
  refine Q'.eqv_trans _ (Q'.abs value * factor) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right value hfactor) ?_
  exact Q'.mul_comm_eqv (Q'.abs value) factor

/-! ## 1. The literal refresh row and generic finite Fubini -/

/-- The proportional refresh row is exactly the already normalized physical
coarse Gibbs mass.  Its apparent difference is only multiplication order in
the positive rational normalization. -/
theorem coarseGibbsRefreshKernel_eqv_coarseNormalizedMass
    (S : SlabScalePair) (source target : EdgeLabelling) :
    coarseGibbsRefreshKernel S source target ≈
      S.coarse.normalizedMass target := by
  unfold coarseGibbsRefreshKernel normalizedTargetWeight
    SlabPhysicalData.normalizedMass Q'.divPos
  exact Q'.mul_comm_eqv _ _

private theorem finiteKernelDifferenceAction_eqv_sub_actions
    {Source Target : Type}
    (targets : List Target)
    (kernel reference : Source → Target → Q')
    (observable : Target → Q') (source : Source) :
    finiteKernelDifferenceAction
        targets kernel reference observable source ≈
      finiteObservableAction targets kernel observable source -
        finiteObservableAction targets reference observable source := by
  unfold finiteKernelDifferenceAction finiteObservableAction
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        kernel source target * observable target +
          -(reference source target * observable target))
      targets) _ ?_ ?_
  · apply listQSum_congr
    intro target
    refine Q'.eqv_trans _
      (kernel source target * observable target +
        (-reference source target) * observable target) _ ?_ ?_
    · exact Q'.add_mul_eqv
        (kernel source target) (-reference source target)
        (observable target)
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_mul_eqv (reference source target) (observable target))
  refine Q'.eqv_trans _
    (listQSum
        (fun target => kernel source target * observable target) targets +
      listQSum
        (fun target => -(reference source target * observable target))
        targets) _ ?_ ?_
  · exact listQSum_add _ _ targets
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _)
    (listQSum_neg_local
      (fun target => reference source target * observable target) targets)

private theorem weightedFiniteObservableAction_fubini
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (sourceWeight : Source → Q')
    (kernel : Source → Target → Q')
    (observable : Target → Q') :
    listQSum
        (fun source =>
          sourceWeight source *
            finiteObservableAction targets kernel observable source)
        sources ≈
      listQSum
        (fun target =>
          listQSum
              (fun source => sourceWeight source * kernel source target)
              sources *
            observable target)
        targets := by
  unfold finiteObservableAction
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            sourceWeight source *
              (kernel source target * observable target))
          targets)
      sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact Q'.eqv_symm
      (listQSum_mul_left
        (sourceWeight source)
        (fun target => kernel source target * observable target)
        targets)
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            (sourceWeight source * kernel source target) *
              observable target)
          targets)
      sources) _ ?_ ?_
  · apply listQSum_congr
    intro source
    apply listQSum_congr
    intro target
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (sourceWeight source)
        (kernel source target) (observable target))
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun source =>
            (sourceWeight source * kernel source target) *
              observable target)
          sources)
      targets) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun source target =>
          (sourceWeight source * kernel source target) *
            observable target)
        sources targets)
  apply listQSum_congr
  intro target
  exact listQSum_mul_right
    (fun source => sourceWeight source * kernel source target)
    (observable target) sources

private theorem fineNormalizedAverage_finiteObservableAction_eqv_blocked
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : EdgeLabelling → Q') :
    listQSum
        (fun source =>
          S.fine.normalizedMass source *
            finiteObservableAction S.coarse.physicalLabellings
              K.kernel observable source)
        S.fine.physicalLabellings ≈
      observableExpectation K.blockedMass
        S.coarse.physicalLabellings observable := by
  unfold observableExpectation SlabScalePair.FiniteSlabKernel.blockedMass
  exact weightedFiniteObservableAction_fubini
    S.fine.physicalLabellings S.coarse.physicalLabellings
    S.fine.normalizedMass K.kernel observable

private theorem fineNormalizedAverage_constant_eqv
    {S : SlabScalePair} (value : Q') :
    listQSum
        (fun source => S.fine.normalizedMass source * value)
        S.fine.physicalLabellings ≈
      value := by
  refine Q'.eqv_trans _
    (listQSum S.fine.normalizedMass S.fine.physicalLabellings * value) _
    (listQSum_mul_right S.fine.normalizedMass value
      S.fine.physicalLabellings) ?_
  refine Q'.eqv_trans _ ((1 : Q') * value) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ value S.fine.normalizedMass_total
  exact Q'.one_mul_eqv value

private theorem fineNormalizedAverage_kernelDifferenceAction_eqv
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (reference : EdgeLabelling → Q')
    (observable : EdgeLabelling → Q') :
    listQSum
        (fun source =>
          S.fine.normalizedMass source *
            finiteKernelDifferenceAction
              S.coarse.physicalLabellings K.kernel
              (fun _ target => reference target) observable source)
        S.fine.physicalLabellings ≈
      observableExpectation K.blockedMass
          S.coarse.physicalLabellings observable -
        observableExpectation reference
          S.coarse.physicalLabellings observable := by
  let candidateAction := fun source =>
    finiteObservableAction S.coarse.physicalLabellings
      K.kernel observable source
  let referenceValue :=
    observableExpectation reference
      S.coarse.physicalLabellings observable
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        S.fine.normalizedMass source *
          (candidateAction source - referenceValue))
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro source
    apply Q'.mul_eqv_congr_left
    unfold candidateAction referenceValue observableExpectation
    exact finiteKernelDifferenceAction_eqv_sub_actions
      S.coarse.physicalLabellings K.kernel
      (fun _ target => reference target) observable source
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        S.fine.normalizedMass source * candidateAction source -
          S.fine.normalizedMass source * referenceValue)
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact mul_sub_expand_local
      (S.fine.normalizedMass source)
      (candidateAction source) referenceValue
  refine Q'.eqv_trans _
    (listQSum
        (fun source =>
          S.fine.normalizedMass source * candidateAction source)
        S.fine.physicalLabellings -
      listQSum
        (fun source =>
          S.fine.normalizedMass source * referenceValue)
        S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_sub_local _ _ S.fine.physicalLabellings
  exact sub_eqv_both_local
    (by
      unfold candidateAction
      exact fineNormalizedAverage_finiteObservableAction_eqv_blocked
        K observable)
    (fineNormalizedAverage_constant_eqv referenceValue)

/-! ## 2. The selected connected row action -/

/-- Production-minus-refresh action on the one connected observable that
exactly represents the selected centered cylinder remainder. -/
def coarseGibbsRefreshConnectedRowAction
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (source : EdgeLabelling) : Q' :=
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  finiteKernelDifferenceAction
    S.coarse.physicalLabellings K.kernel
    (coarseGibbsRefreshKernel S)
    (connectedRemainderObservable K M) source

/-- Fine Gibbs average of the signed connected row action. -/
def coarseGibbsRefreshConnectedSignedSourceAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (fun source =>
      S.fine.normalizedMass source *
        coarseGibbsRefreshConnectedRowAction
          S hfineCutoff hcoarseCoupling M source)
    S.fine.physicalLabellings

/-- The fine-source signed average is exactly the existing centered cylinder
remainder.  This is the local row-action form of the Gibbs-refresh seam. -/
theorem coarseGibbsRefreshConnectedSignedSourceAverage_eqv_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    coarseGibbsRefreshConnectedSignedSourceAverage
        S hfineCutoff hcoarseCoupling M ≈
      centeredCylinderRemainder
        (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let observable := connectedRemainderObservable K M
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        S.fine.normalizedMass source *
          finiteKernelDifferenceAction
            S.coarse.physicalLabellings K.kernel
            (fun _ target => S.coarse.normalizedMass target)
            observable source)
      S.fine.physicalLabellings) _ ?_ ?_
  · unfold coarseGibbsRefreshConnectedSignedSourceAverage
      coarseGibbsRefreshConnectedRowAction
    apply listQSum_congr
    intro source
    apply Q'.mul_eqv_congr_left
    unfold finiteKernelDifferenceAction
    apply listQSum_congr
    intro target
    apply Q'.mul_eqv_congr_right
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (coarseGibbsRefreshKernel_eqv_coarseNormalizedMass
          S source target))
  refine Q'.eqv_trans _
    (observableExpectation K.blockedMass
        S.coarse.physicalLabellings observable -
      observableExpectation S.coarse.normalizedMass
        S.coarse.physicalLabellings observable) _ ?_ ?_
  · exact fineNormalizedAverage_kernelDifferenceAction_eqv
      K S.coarse.normalizedMass observable
  refine Q'.eqv_trans _
    (remainderObservableExpectation K observable) _ ?_ ?_
  · exact blocked_sub_coarseObservableExpectation_eqv_remainder
      K observable
  exact connectedRemainderExpectation_eqv_centeredCylinderRemainder K M

/-! ## 3. Quantitative interfaces at the source-row seam -/

/-- Fine-weighted `L1` norm of the selected signed row action.  The absolute
value is taken after summing over coarse targets but before averaging fine
sources, so target cancellation is retained. -/
def coarseGibbsRefreshConnectedSourceL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (fun source =>
      S.fine.normalizedMass source *
        Q'.abs
          (coarseGibbsRefreshConnectedRowAction
            S hfineCutoff hcoarseCoupling M source))
    S.fine.physicalLabellings

/-- Triangle inequality only across fine sources.  Cancellation inside every
coarse-target row action remains untouched. -/
theorem coarseGibbsRefreshConnectedSignedSourceAverage_abs_le_sourceL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    Q'.abs
        (coarseGibbsRefreshConnectedSignedSourceAverage
          S hfineCutoff hcoarseCoupling M) ≤
      coarseGibbsRefreshConnectedSourceL1
        S hfineCutoff hcoarseCoupling M := by
  unfold coarseGibbsRefreshConnectedSignedSourceAverage
    coarseGibbsRefreshConnectedSourceL1
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local _ S.fine.physicalLabellings) ?_
  exact Q'.le_of_eqv
    (listQSum_congr
      (fun source =>
        abs_mul_nonnegative_left_eqv_local
          (S.fine.normalizedMass source)
          (coarseGibbsRefreshConnectedRowAction
            S hfineCutoff hcoarseCoupling M source)
          (S.fine.normalizedMass_nonnegative source))
      S.fine.physicalLabellings)

/-- Direct cancellation-preserving quadratic input on the signed fine-source
average. -/
def CoarseGibbsRefreshConnectedSignedSourceAverageCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (coarseGibbsRefreshConnectedSignedSourceAverage
        S hfineCutoff hcoarseCoupling M) ≤
    kernelCeiling * (g * g)

/-- Fine-source `L1` quadratic input for the selected observable row action. -/
def CoarseGibbsRefreshConnectedSourceL1Calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  coarseGibbsRefreshConnectedSourceL1
      S hfineCutoff hcoarseCoupling M ≤
    kernelCeiling * (g * g)

/-- Pointwise-in-source quadratic input for the selected observable row
action.  This is stronger than the weighted source `L1` premise but is the
natural endpoint for a local recoupling or posterior-contraction proof. -/
def CoarseGibbsRefreshConnectedPointwiseRowCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  ∀ source, source ∈ S.fine.physicalLabellings →
    Q'.abs
        (coarseGibbsRefreshConnectedRowAction
          S hfineCutoff hcoarseCoupling M source) ≤
      kernelCeiling * (g * g)

/-- The signed-average premise and the existing centered-remainder premise
are exactly equivalent. -/
theorem connectedSignedSourceAverageCalibration_iff_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    CoarseGibbsRefreshConnectedSignedSourceAverageCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      CoarseGibbsRefreshConnectedRemainderCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold CoarseGibbsRefreshConnectedSignedSourceAverageCalibration
    CoarseGibbsRefreshConnectedRemainderCalibration
  have hexact :=
    coarseGibbsRefreshConnectedSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (Q'.eqv_symm hexact))) h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hexact)) h

/-- The selected source-`L1` estimate compiles to the existing normalized
connected remainder with no coefficient loss. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_sourceL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hsourceL1 :
      CoarseGibbsRefreshConnectedSourceL1Calibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold CoarseGibbsRefreshConnectedRemainderCalibration
  have hexact :=
    coarseGibbsRefreshConnectedSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (Q'.eqv_symm hexact)))
    (Q'.le_trans' _ _ _
      (coarseGibbsRefreshConnectedSignedSourceAverage_abs_le_sourceL1
        S hfineCutoff hcoarseCoupling M)
      (by
        simpa only [CoarseGibbsRefreshConnectedSourceL1Calibration] using
          hsourceL1))

/-- A pointwise selected-row estimate averages to the source-`L1`
calibration because the actual fine Gibbs weights are nonnegative and sum to
one. -/
theorem coarseGibbsRefreshConnectedSourceL1Calibration_of_pointwiseRow
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hpointwise :
      CoarseGibbsRefreshConnectedPointwiseRowCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedSourceL1Calibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold CoarseGibbsRefreshConnectedSourceL1Calibration
    coarseGibbsRefreshConnectedSourceL1
  let budget := kernelCeiling * (g * g)
  have hsum :
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              Q'.abs
                (coarseGibbsRefreshConnectedRowAction
                  S hfineCutoff hcoarseCoupling M source))
          S.fine.physicalLabellings ≤
        listQSum
          (fun source => S.fine.normalizedMass source * budget)
          S.fine.physicalLabellings := by
    apply listQSum_mono
    intro source hsource
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (by
        unfold CoarseGibbsRefreshConnectedPointwiseRowCalibration at hpointwise
        simpa only [budget] using hpointwise source hsource)
      (S.fine.normalizedMass_nonnegative source)
  refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
  exact fineNormalizedAverage_constant_eqv budget

/-- The pointwise selected-row estimate therefore compiles directly to the
existing normalized connected remainder. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_pointwiseRow
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hpointwise :
      CoarseGibbsRefreshConnectedPointwiseRowCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact coarseGibbsRefreshConnectedRemainderCalibration_of_sourceL1
    S hfineCutoff hcoarseCoupling M g kernelCeiling
    (coarseGibbsRefreshConnectedSourceL1Calibration_of_pointwiseRow
      S hfineCutoff hcoarseCoupling M g kernelCeiling hpointwise)

/-- Conservative fallback: a pointwise full kernel-row `L1` estimate bounds
the selected connected row action because the observable is pointwise bounded
by one. -/
theorem coarseGibbsRefreshConnectedPointwiseRowCalibration_of_kernelRowL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hrowL1 : ∀ source, source ∈ S.fine.physicalLabellings →
      finiteRowL1Defect S.coarse.physicalLabellings
          (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          (coarseGibbsRefreshKernel S) source ≤
        kernelCeiling * (g * g)) :
    CoarseGibbsRefreshConnectedPointwiseRowCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  intro source hsource
  unfold coarseGibbsRefreshConnectedRowAction
  have hbound := finiteKernelDifferenceAction_abs_le
    S.coarse.physicalLabellings
    (physicalKernel S hfineCutoff hcoarseCoupling).kernel
    (coarseGibbsRefreshKernel S)
    (connectedRemainderObservable
      (physicalKernel S hfineCutoff hcoarseCoupling) M)
    source 1 (kernelCeiling * (g * g))
    (by decide)
    (fun target _ =>
      connectedRemainderObservable_abs_le_one
        (physicalKernel S hfineCutoff hcoarseCoupling) M target)
    (hrowL1 source hsource)
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv (Q'.mul_one_eqv (kernelCeiling * (g * g))))

#print axioms coarseGibbsRefreshKernel_eqv_coarseNormalizedMass
#print axioms coarseGibbsRefreshConnectedRowAction
#print axioms coarseGibbsRefreshConnectedSignedSourceAverage
#print axioms coarseGibbsRefreshConnectedSignedSourceAverage_eqv_centeredRemainder
#print axioms coarseGibbsRefreshConnectedSourceL1
#print axioms coarseGibbsRefreshConnectedSignedSourceAverage_abs_le_sourceL1
#print axioms CoarseGibbsRefreshConnectedSignedSourceAverageCalibration
#print axioms CoarseGibbsRefreshConnectedSourceL1Calibration
#print axioms CoarseGibbsRefreshConnectedPointwiseRowCalibration
#print axioms connectedSignedSourceAverageCalibration_iff_centeredRemainder
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_sourceL1
#print axioms coarseGibbsRefreshConnectedSourceL1Calibration_of_pointwiseRow
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_pointwiseRow
#print axioms coarseGibbsRefreshConnectedPointwiseRowCalibration_of_kernelRowL1

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction
