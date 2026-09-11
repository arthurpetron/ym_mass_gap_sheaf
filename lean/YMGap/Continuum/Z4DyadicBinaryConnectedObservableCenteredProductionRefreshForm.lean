/-
# The connected posterior variance is the centered production/refresh form

For the physical cutoff-one kernel, the normalized tilted-Gibbs connected
response is exactly the production-row expectation of the connected
remainder observable.  The existing Gibbs-refresh row action subtracts the
coarse Gibbs expectation, a constant in the fine source.  After subtracting
the fine-source mean of that row action, the coarse constant cancels and the
result is exactly the centered connected response.

This file makes that cancellation literal and proves that the normalized
quadratic form of the vacuum-centered physical production-minus-refresh row
is exactly the posterior variance constructed previously.  Hence, at the
named SU(2) anchor, the physical centered form obeys the same strict bound

  `centeredProductionRefreshForm <= 1449/1700 < 1`.

The uncentered row action also contains the squared global bias and is not
claimed equal to posterior variance.  No dense-sector spanning theorem,
operator spectral gap, completed gap, thermodynamic limit, continuum theory,
or Clay theorem is asserted here.

Constructive contract: exact finite rational sums, positive-denominator
normalization, and the previously proved SU(2)-specific posterior estimate;
no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, enlarged heartbeat budget, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservablePosteriorVarianceFraction
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableCenteredProductionRefreshForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRefreshSpectralComparison
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservablePosteriorVarianceFraction
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem listQSum_neg_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      simp only [listQSum]
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
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

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈ factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _ ?_ ?_
  · exact Q'.mul_add_eqv factor left (-right)
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

private theorem sub_mul_expand_local (left right factor : Q') :
    (left - right) * factor ≈ left * factor - right * factor := by
  refine Q'.eqv_trans _ (factor * (left - right)) _
    (Q'.mul_comm_eqv (left - right) factor) ?_
  refine Q'.eqv_trans _ (factor * left - factor * right) _
    (mul_sub_expand_local factor left right) ?_
  exact sub_eqv_both_local
    (Q'.mul_comm_eqv factor left) (Q'.mul_comm_eqv factor right)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem centered_difference_eqv_original
    (left right center : Q') :
    (left - center) + -(right - center) ≈ left + -right := by
  change (left + -center) + -(right + -center) ≈ left + -right
  refine Q'.eqv_trans _
    ((left + -center) + ((-right) + center)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (left + -center) _ _
      (Q'.eqv_trans _ ((-right) + -(-center)) _
        (Q'.neg_add_eqv right (-center))
        (Q'.add_eqv_congr_left (-right) _ _
          (Q'.neg_neg_eqv center)))
  refine Q'.eqv_trans _
    ((left + -right) + ((-center) + center)) _
    (Q'.add_swap_inner left (-center) (-right) center) ?_
  refine Q'.eqv_trans _ ((left + -right) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (left + -right) _ _
      (Q'.neg_add_self_eqv center)
  · exact Q'.eqv_of_eq (Q'.add_zero' (left + -right))

private theorem common_reference_cancels_after_centering
    (value mean reference : Q') :
    (value - reference) - (mean - reference) ≈ value - mean := by
  change (value - reference) + -(mean - reference) ≈ value + -mean
  exact centered_difference_eqv_original value mean reference

private theorem finiteKernelDifferenceAction_eqv_expectation_sub_local
    {Source Target : Type} (targets : List Target)
    (kernel reference : Source → Target → Q')
    (observable : Target → Q') (source : Source) :
    finiteKernelDifferenceAction
        targets kernel reference observable source ≈
      listQSum
          (fun target => kernel source target * observable target)
          targets -
        listQSum
          (fun target => reference source target * observable target)
          targets := by
  unfold finiteKernelDifferenceAction
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        kernel source target * observable target -
          reference source target * observable target)
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
  exact listQSum_sub_local _ _ targets

private theorem mul_swap_last_local (first second third : Q') :
    (first * second) * third ≈ (first * third) * second := by
  refine Q'.eqv_trans _ (first * (second * third)) _
    (Q'.mul_assoc_eqv first second third) ?_
  refine Q'.eqv_trans _ (first * (third * second)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left first _ _
      (Q'.mul_comm_eqv second third)
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv first third second)

private theorem finePhysicalPartition_pos (S : SlabScalePair) :
    (0 : Q') < S.fine.physicalPartition :=
  slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent

private theorem finePhysicalPartitionSquare_pos (S : SlabScalePair) :
    (0 : Q') < S.fine.physicalPartition * S.fine.physicalPartition :=
  Q'.mul_pos (finePhysicalPartition_pos S) (finePhysicalPartition_pos S)

/-! ## 1. The tilted response is the physical production-row action -/

/-- On a positive physical fine source, the normalized tilted-Gibbs response
is exactly the physical production-kernel expectation of the connected
observable. -/
theorem positivePhysicalSourceTiltedGibbsConnectedResponse_eqv_physicalKernelExpectation
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (source : PositivePhysicalSource S) :
    positivePhysicalSourceTiltedGibbsConnectedResponse
        (physicalKernel S hfineCutoff hcoarseCoupling)
        hfineCutoff hcoarseCoupling M source ≈
      observableExpectation
        ((physicalKernel S hfineCutoff hcoarseCoupling).kernel source.1)
        S.coarse.physicalLabellings
        (connectedRemainderObservable
          (physicalKernel S hfineCutoff hcoarseCoupling) M) := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let observable := connectedRemainderObservable K M
  let rawWeight := positivePhysicalSourceTiltedGibbsFullRawWeight S source
  let rowMass := positivePhysicalSourceTiltedGibbsRowMass S source
  let hrowMass := positivePhysicalSourceTiltedGibbsRowMass_pos
    S hfineCutoff hcoarseCoupling source
  let reciprocal := Q'.recipPos rowMass hrowMass
  change
    listQSum (fun target => rawWeight target * observable target)
        S.coarse.physicalLabellings * reciprocal ≈
      listQSum (fun target => K.kernel source.1 target * observable target)
        S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun target => (rawWeight target * observable target) * reciprocal)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_mul_right
        (fun target => rawWeight target * observable target)
        reciprocal S.coarse.physicalLabellings)
  apply listQSum_congr_on
  intro target htarget
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      ((rawWeight target * reciprocal) * observable target) _
      (Q'.mul_eqv_congr_right _ _ (observable target)
        (physicalKernel_positivePhysicalSource_eqv_tiltedGibbs
          S hfineCutoff hcoarseCoupling source target htarget))
      (mul_swap_last_local
        (rawWeight target) reciprocal (observable target)))

/-- On a positive source, the existing physical production-minus-refresh row
action is the tilted connected response minus the source-independent coarse
Gibbs expectation. -/
theorem coarseGibbsRefreshConnectedRowAction_positive_eqv_response_sub_refresh
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (source : PositivePhysicalSource S) :
    coarseGibbsRefreshConnectedRowAction
        S hfineCutoff hcoarseCoupling M source.1 ≈
      positivePhysicalSourceTiltedGibbsConnectedResponse
          (physicalKernel S hfineCutoff hcoarseCoupling)
          hfineCutoff hcoarseCoupling M source -
        observableExpectation S.coarse.normalizedMass
          S.coarse.physicalLabellings
          (connectedRemainderObservable
            (physicalKernel S hfineCutoff hcoarseCoupling) M) := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let observable := connectedRemainderObservable K M
  let production := observableExpectation (K.kernel source.1)
    S.coarse.physicalLabellings observable
  let refresh := observableExpectation (coarseGibbsRefreshKernel S source.1)
    S.coarse.physicalLabellings observable
  let coarse := observableExpectation S.coarse.normalizedMass
    S.coarse.physicalLabellings observable
  refine Q'.eqv_trans _ (production - refresh) _ ?_ ?_
  · unfold coarseGibbsRefreshConnectedRowAction production refresh
    exact finiteKernelDifferenceAction_eqv_expectation_sub_local
      S.coarse.physicalLabellings K.kernel
      (coarseGibbsRefreshKernel S) observable source.1
  apply sub_eqv_both_local
  · exact Q'.eqv_symm
      (positivePhysicalSourceTiltedGibbsConnectedResponse_eqv_physicalKernelExpectation
        S hfineCutoff hcoarseCoupling M source)
  · unfold refresh observableExpectation
    apply listQSum_congr
    intro target
    exact Q'.mul_eqv_congr_right _ _ (observable target)
      (coarseGibbsRefreshKernel_eqv_coarseNormalizedMass
        S source.1 target)

/-! ## 2. Exact centering on the physical fine-source law -/

def finePacketPhysicalConnectedResponseMeanFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.divPos
    (finePacketTiltedGibbsConnectedResponseMeanMass
      (physicalKernel S hfineCutoff hcoarseCoupling)
      hfineCutoff hcoarseCoupling M)
    S.fine.physicalPartition
    (finePhysicalPartition_pos S)

def positivePhysicalCenteredConnectedResponse
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (source : PositivePhysicalSource S) : Q' :=
  positivePhysicalSourceTiltedGibbsConnectedResponse
      (physicalKernel S hfineCutoff hcoarseCoupling)
      hfineCutoff hcoarseCoupling M source -
    finePacketPhysicalConnectedResponseMeanFraction
      S hfineCutoff hcoarseCoupling M

/-- The centered connected response has exact zero raw fine-source mean. -/
theorem positivePhysicalCenteredConnectedResponse_weightedMean_eqv_zero
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finiteListWeightedMean
        (positivePhysicalSources S)
        (fun source => S.fine.physicalTerm source.1)
        (positivePhysicalCenteredConnectedResponse
          S hfineCutoff hcoarseCoupling M) ≈ 0 := by
  let states := positivePhysicalSources S
  let weight := fun source : PositivePhysicalSource S =>
    S.fine.physicalTerm source.1
  let response := positivePhysicalSourceTiltedGibbsConnectedResponse
    (physicalKernel S hfineCutoff hcoarseCoupling)
    hfineCutoff hcoarseCoupling M
  let mean := finiteListWeightedMean states weight response
  let normalization := S.fine.physicalPartition
  let meanFraction := Q'.divPos mean normalization
    (finePhysicalPartition_pos S)
  have hmass : listQSum weight states ≈ normalization :=
    finePositivePhysicalSources_weight_total S
  change
    listQSum (fun source => (response source - meanFraction) * weight source)
      states ≈ 0
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        response source * weight source - meanFraction * weight source)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact sub_mul_expand_local
      (response source) meanFraction (weight source)
  refine Q'.eqv_trans _
    (listQSum (fun source => response source * weight source) states -
      listQSum (fun source => meanFraction * weight source) states) _
    (listQSum_sub_local _ _ states) ?_
  refine Q'.eqv_trans _
    (mean - meanFraction * listQSum weight states) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (listQSum_mul_left meanFraction weight states)
  refine Q'.eqv_trans _ (mean - meanFraction * normalization) _
    (sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left meanFraction _ _ hmass)) ?_
  refine Q'.eqv_trans _ (mean - mean) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.divPos_mul_eqv mean normalization
        (finePhysicalPartition_pos S))
  change mean + (-mean) ≈ 0
  exact Q'.add_neg_self_eqv mean

private theorem connectedResponse_pairwiseVariance_eqv_centered
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finiteWeightedPairwiseVariance
        (positivePhysicalSources S)
        (fun source => S.fine.physicalTerm source.1)
        (positivePhysicalSourceTiltedGibbsConnectedResponse
          (physicalKernel S hfineCutoff hcoarseCoupling)
          hfineCutoff hcoarseCoupling M) ≈
      finiteWeightedPairwiseVariance
        (positivePhysicalSources S)
        (fun source => S.fine.physicalTerm source.1)
        (positivePhysicalCenteredConnectedResponse
          S hfineCutoff hcoarseCoupling M) := by
  unfold finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    finiteStationaryProductJoint
  apply listQSum_congr
  intro first
  apply listQSum_congr
  intro second
  apply Q'.mul_eqv_congr_left
  exact mul_eqv_both_local
    (Q'.eqv_symm
      (centered_difference_eqv_original
        _ _
        (finePacketPhysicalConnectedResponseMeanFraction
          S hfineCutoff hcoarseCoupling M)))
    (Q'.eqv_symm
      (centered_difference_eqv_original
        _ _
        (finePacketPhysicalConnectedResponseMeanFraction
          S hfineCutoff hcoarseCoupling M)))

/-- The posterior variance is exactly the normalized fine-source square of
the centered physical connected response.  The numerator and denominator are
kept in their pairwise-normalized form `Z * square / Z^2`. -/
def finePacketGlobalPhysicalConnectedResponseCenteredSourceSquareFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.divPos
    (S.fine.physicalPartition *
      finiteWeightedSquare
        (positivePhysicalSources S)
        (fun source => S.fine.physicalTerm source.1)
        (positivePhysicalCenteredConnectedResponse
          S hfineCutoff hcoarseCoupling M))
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

theorem finePacketGlobalPhysicalConnectedPosteriorVariance_eqv_centeredSourceSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        (physicalKernel S hfineCutoff hcoarseCoupling)
        hfineCutoff hcoarseCoupling M ≈
      finePacketGlobalPhysicalConnectedResponseCenteredSourceSquareFraction
        S hfineCutoff hcoarseCoupling M := by
  let states := positivePhysicalSources S
  let weight := fun source : PositivePhysicalSource S =>
    S.fine.physicalTerm source.1
  let response := positivePhysicalSourceTiltedGibbsConnectedResponse
    (physicalKernel S hfineCutoff hcoarseCoupling)
    hfineCutoff hcoarseCoupling M
  let centered := positivePhysicalCenteredConnectedResponse
    S hfineCutoff hcoarseCoupling M
  let mass := S.fine.physicalPartition
  let diagonal := finiteWeightedSquare states weight centered
  let massDiagonal := mass * diagonal
  let denominator := mass * mass
  let reciprocal := Q'.recipPos denominator
    (finePhysicalPartitionSquare_pos S)
  have hinvariant : finiteWeightedPairwiseVariance states weight response ≈
      finiteWeightedPairwiseVariance states weight centered :=
    connectedResponse_pairwiseVariance_eqv_centered
      S hfineCutoff hcoarseCoupling M
  have hcenter : finiteListWeightedMean states weight centered ≈ 0 :=
    positivePhysicalCenteredConnectedResponse_weightedMean_eqv_zero
      S hfineCutoff hcoarseCoupling M
  have hcentered :=
    finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal
      states weight centered hcenter
  have hmass : finiteWeightedMass states weight ≈ mass :=
    finePositivePhysicalSources_weight_total S
  have hpairwise : finiteWeightedPairwiseVariance states weight response ≈
      massDiagonal + massDiagonal := by
    refine Q'.eqv_trans _ _ _ hinvariant ?_
    refine Q'.eqv_trans _
      (finiteWeightedMass states weight * diagonal +
        finiteWeightedMass states weight * diagonal) _ hcentered ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ diagonal hmass)
      (Q'.mul_eqv_congr_right _ _ diagonal hmass)
  unfold finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
    finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
    finePacketGlobalPhysicalConnectedResponseCenteredSourceSquareFraction
    Q'.divPos
  refine Q'.eqv_trans _
    (HalfPow.half * ((massDiagonal + massDiagonal) * reciprocal)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.mul_eqv_congr_right _ _ reciprocal hpairwise)
  refine Q'.eqv_trans _
    (HalfPow.half *
      (massDiagonal * reciprocal + massDiagonal * reciprocal)) _
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.add_mul_eqv massDiagonal massDiagonal reciprocal)) ?_
  refine Q'.eqv_trans _
    (HalfPow.half * (massDiagonal * reciprocal) +
      HalfPow.half * (massDiagonal * reciprocal)) _
    (Q'.mul_add_eqv HalfPow.half
      (massDiagonal * reciprocal) (massDiagonal * reciprocal)) ?_
  exact YMGap.Constructive.ExpNeg.two_halves
    (massDiagonal * reciprocal)

/-! ## 3. Identify the same square with the physical centered row action -/

/-- The fine-source mean of the physical production-minus-refresh action,
presented so the source-independent coarse refresh term remains visible. -/
def finePacketPhysicalConnectedProductionRefreshMean
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  finePacketPhysicalConnectedResponseMeanFraction
      S hfineCutoff hcoarseCoupling M -
    observableExpectation S.coarse.normalizedMass
      S.coarse.physicalLabellings
      (connectedRemainderObservable
        (physicalKernel S hfineCutoff hcoarseCoupling) M)

/-- Existing production-minus-refresh row action with its physical
fine-source mean removed. -/
def positivePhysicalCenteredGibbsRefreshConnectedRowAction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (source : PositivePhysicalSource S) : Q' :=
  coarseGibbsRefreshConnectedRowAction
      S hfineCutoff hcoarseCoupling M source.1 -
    finePacketPhysicalConnectedProductionRefreshMean
      S hfineCutoff hcoarseCoupling M

/-- Vacuum centering cancels the source-independent refresh expectation
exactly, leaving the centered production response. -/
theorem positivePhysicalCenteredGibbsRefreshConnectedRowAction_eqv_centeredResponse
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (source : PositivePhysicalSource S) :
    positivePhysicalCenteredGibbsRefreshConnectedRowAction
        S hfineCutoff hcoarseCoupling M source ≈
      positivePhysicalCenteredConnectedResponse
        S hfineCutoff hcoarseCoupling M source := by
  let response := positivePhysicalSourceTiltedGibbsConnectedResponse
    (physicalKernel S hfineCutoff hcoarseCoupling)
    hfineCutoff hcoarseCoupling M source
  let mean := finePacketPhysicalConnectedResponseMeanFraction
    S hfineCutoff hcoarseCoupling M
  let refresh := observableExpectation S.coarse.normalizedMass
    S.coarse.physicalLabellings
    (connectedRemainderObservable
      (physicalKernel S hfineCutoff hcoarseCoupling) M)
  unfold positivePhysicalCenteredGibbsRefreshConnectedRowAction
    finePacketPhysicalConnectedProductionRefreshMean
    positivePhysicalCenteredConnectedResponse
  refine Q'.eqv_trans _ ((response - refresh) - (mean - refresh)) _ ?_ ?_
  · exact sub_eqv_both_local
      (coarseGibbsRefreshConnectedRowAction_positive_eqv_response_sub_refresh
        S hfineCutoff hcoarseCoupling M source)
      (Q'.eqv_refl _)
  exact common_reference_cancels_after_centering response mean refresh

theorem positivePhysicalCenteredGibbsRefreshConnectedRowAction_weightedMean_eqv_zero
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finiteListWeightedMean
        (positivePhysicalSources S)
        (fun source => S.fine.physicalTerm source.1)
        (positivePhysicalCenteredGibbsRefreshConnectedRowAction
          S hfineCutoff hcoarseCoupling M) ≈ 0 := by
  refine Q'.eqv_trans _
    (finiteListWeightedMean
      (positivePhysicalSources S)
      (fun source => S.fine.physicalTerm source.1)
      (positivePhysicalCenteredConnectedResponse
        S hfineCutoff hcoarseCoupling M)) _ ?_ ?_
  · unfold finiteListWeightedMean
    apply listQSum_congr
    intro source
    exact Q'.mul_eqv_congr_right _ _ _
      (positivePhysicalCenteredGibbsRefreshConnectedRowAction_eqv_centeredResponse
        S hfineCutoff hcoarseCoupling M source)
  · exact positivePhysicalCenteredConnectedResponse_weightedMean_eqv_zero
      S hfineCutoff hcoarseCoupling M

def finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.divPos
    (S.fine.physicalPartition *
      finiteWeightedSquare
        (positivePhysicalSources S)
        (fun source => S.fine.physicalTerm source.1)
        (positivePhysicalCenteredGibbsRefreshConnectedRowAction
          S hfineCutoff hcoarseCoupling M))
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

theorem finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_eqv_centeredResponseSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
        S hfineCutoff hcoarseCoupling M ≈
      finePacketGlobalPhysicalConnectedResponseCenteredSourceSquareFraction
        S hfineCutoff hcoarseCoupling M := by
  unfold finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
    finePacketGlobalPhysicalConnectedResponseCenteredSourceSquareFraction
    Q'.divPos
  apply Q'.mul_eqv_congr_right
  apply Q'.mul_eqv_congr_left
  unfold finiteWeightedSquare
  apply listQSum_congr
  intro source
  apply Q'.mul_eqv_congr_left
  exact mul_eqv_both_local
    (positivePhysicalCenteredGibbsRefreshConnectedRowAction_eqv_centeredResponse
      S hfineCutoff hcoarseCoupling M source)
    (positivePhysicalCenteredGibbsRefreshConnectedRowAction_eqv_centeredResponse
      S hfineCutoff hcoarseCoupling M source)

/-- Main bridge: the strict posterior quantity is exactly the normalized
vacuum-centered physical production-minus-refresh quadratic form. -/
theorem finePacketGlobalPhysicalConnectedPosteriorVariance_eqv_centeredProductionRefreshForm
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        (physicalKernel S hfineCutoff hcoarseCoupling)
        hfineCutoff hcoarseCoupling M ≈
      finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
        S hfineCutoff hcoarseCoupling M := by
  exact Q'.eqv_trans _ _ _
    (finePacketGlobalPhysicalConnectedPosteriorVariance_eqv_centeredSourceSquare
      S hfineCutoff hcoarseCoupling M)
    (Q'.eqv_symm
      (finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_eqv_centeredResponseSquare
        S hfineCutoff hcoarseCoupling M))

/-! ## 4. Strict physical centered-form bound at the SU(2) anchor -/

theorem finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_le_anchorRate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half) :
    finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
        S hfineCutoff hcoarseCoupling M ≤
      finePacketAnchorVacuumPacketStrictRate := by
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (finePacketGlobalPhysicalConnectedPosteriorVariance_eqv_centeredProductionRefreshForm
        S hfineCutoff hcoarseCoupling M))
    (finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_anchorRate
      (physicalKernel S hfineCutoff hcoarseCoupling)
      hfineCutoff hcoarseCoupling M cutoff half hfine)

theorem finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_lt_one_at_anchor
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half) :
    finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
        S hfineCutoff hcoarseCoupling M < (1 : Q') := by
  exact Q'.lt_of_le_of_lt
    (finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_le_anchorRate
      S hfineCutoff hcoarseCoupling M cutoff half hfine)
    finePacketAnchorVacuumPacketStrictRate_lt_one

/-! ## Axiom audit -/

#print axioms positivePhysicalSourceTiltedGibbsConnectedResponse_eqv_physicalKernelExpectation
#print axioms coarseGibbsRefreshConnectedRowAction_positive_eqv_response_sub_refresh
#print axioms positivePhysicalCenteredConnectedResponse_weightedMean_eqv_zero
#print axioms finePacketGlobalPhysicalConnectedResponseCenteredSourceSquareFraction
#print axioms finePacketGlobalPhysicalConnectedPosteriorVariance_eqv_centeredSourceSquare
#print axioms positivePhysicalCenteredGibbsRefreshConnectedRowAction_eqv_centeredResponse
#print axioms positivePhysicalCenteredGibbsRefreshConnectedRowAction_weightedMean_eqv_zero
#print axioms finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
#print axioms finePacketGlobalPhysicalConnectedPosteriorVariance_eqv_centeredProductionRefreshForm
#print axioms finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_le_anchorRate
#print axioms finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_lt_one_at_anchor

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableCenteredProductionRefreshForm
