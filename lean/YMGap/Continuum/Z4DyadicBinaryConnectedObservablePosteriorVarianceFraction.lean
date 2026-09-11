/-
# Strict posterior variance of the actual connected-observable response

Let `R(source)` be the normalized tilted-Gibbs expectation of the same
connected remainder observable used in the physical row calculation.  Under
the normalized fine-source law, this file defines its posterior variance by

  `Var(R) = (1/2) * E[(R(first) - R(second))^2]`.

The finite pairwise identity proves that this is exactly the usual centered
second moment.  The connected response has pairwise diameter one, so its
pairwise square is at most its absolute difference.  The latter has two
causal face envelopes.  At the named SU(2) anchor, each face costs at most
`q = 1449/1700`; the exact factor one half cancels their sum and gives

  `Var(R) <= q < 1`.

This is a strict finite-volume posterior-variance bound for the actual
connected response.  It is not yet an identification with the centered
production/refresh form, a dense spectral bound, a completed gap, a
thermodynamic limit, a continuum theory, or the Clay theorem.

Constructive contract: exact finite weighted variance algebra, rational
absolute-value order, explicit positive division, and the previously proved
SU(2)-specific anchor bounds only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, trusted external computation,
enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalConnectedObservableResponseOscillation
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservablePosteriorVarianceFraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedObservableResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
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
               Int.mul_one];
             ac_rfl))

private theorem twice_deficit_rearrange (diagonal meanSquare : Q') :
    (diagonal + diagonal) + -(meanSquare + meanSquare) ≈
      (diagonal + -meanSquare) + (diagonal + -meanSquare) := by
  ring_qeqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem finePhysicalPartitionSquare_pos (S : SlabScalePair) :
    (0 : Q') < S.fine.physicalPartition * S.fine.physicalPartition :=
  Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)

private theorem finePositiveSourcePairWeight_nonnegative
    (S : SlabScalePair) (pair : PositivePhysicalSourcePair S) :
    (0 : Q') ≤ finePacketFineSourceRawPairWeight
      S pair.1.1 pair.2.1 := by
  unfold finePacketFineSourceRawPairWeight
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt pair.1.2.2)
    (Q'.le_of_lt pair.2.2.2)

private theorem square_le_abs_of_abs_le_one
    (difference : Q')
    (hdifference : Q'.abs difference ≤ (1 : Q')) :
    difference * difference ≤ Q'.abs difference := by
  have hsquare : difference * difference ≤
      Q'.abs difference * Q'.abs difference :=
    Q'.mul_le_of_bounds
      (Q'.abs_nonneg difference) (Q'.abs_nonneg difference)
      (YMGap.Constructive.ExpNeg.neg_abs_le difference)
      (Q'.le_abs_self difference)
      (YMGap.Constructive.ExpNeg.neg_abs_le difference)
      (Q'.le_abs_self difference)
  have hcontract : Q'.abs difference * Q'.abs difference ≤
      Q'.abs difference * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdifference
      (Q'.abs_nonneg difference)
  exact Q'.le_trans' _ _ _ hsquare
    (Q'.le_trans' _ _ _ hcontract
      (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs difference))))

/-! ## 1. Pairwise and centered variance of the actual connected response -/

def finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  finiteWeightedPairwiseVariance
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (positivePhysicalSourceTiltedGibbsConnectedResponse
      K hfineCutoff hcoarseCoupling M)

/-- Conventional normalized posterior variance: one half of the normalized
independent-pair squared response difference. -/
def finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  HalfPow.half *
    Q'.divPos
      (finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
        K hfineCutoff hcoarseCoupling M)
      (S.fine.physicalPartition * S.fine.physicalPartition)
      (finePhysicalPartitionSquare_pos S)

def finePacketTiltedGibbsConnectedResponseMeanMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  finiteListWeightedMean
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (positivePhysicalSourceTiltedGibbsConnectedResponse
      K hfineCutoff hcoarseCoupling M)

def finePacketTiltedGibbsConnectedResponseSquareMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  finiteWeightedSquare
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (positivePhysicalSourceTiltedGibbsConnectedResponse
      K hfineCutoff hcoarseCoupling M)

/-- Denominator-cleared centered second moment
`partition * secondMoment - mean^2`. -/
def finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  S.fine.physicalPartition *
      finePacketTiltedGibbsConnectedResponseSquareMass
        K hfineCutoff hcoarseCoupling M -
    finePacketTiltedGibbsConnectedResponseMeanMass
        K hfineCutoff hcoarseCoupling M *
      finePacketTiltedGibbsConnectedResponseMeanMass
        K hfineCutoff hcoarseCoupling M

/-- The independent-pair square is exactly twice the denominator-cleared
centered second moment of the same connected response. -/
theorem finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_eqv_twice_centered
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
        K hfineCutoff hcoarseCoupling M ≈
      finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
          K hfineCutoff hcoarseCoupling M +
        finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
          K hfineCutoff hcoarseCoupling M := by
  let states := positivePhysicalSources S
  let weight := fun source : PositivePhysicalSource S =>
    S.fine.physicalTerm source.1
  let coefficient := positivePhysicalSourceTiltedGibbsConnectedResponse
    K hfineCutoff hcoarseCoupling M
  let mass := finiteWeightedMass states weight
  let diagonal := finiteWeightedSquare states weight coefficient
  let mean := finiteListWeightedMean states weight coefficient
  let centered :=
    finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
      K hfineCutoff hcoarseCoupling M
  have hgeneric := finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean
    states weight coefficient
  have hmass : mass ≈ S.fine.physicalPartition :=
    finePositivePhysicalSources_weight_total S
  have hmassDiagonal : mass * diagonal ≈
      S.fine.physicalPartition * diagonal :=
    Q'.mul_eqv_congr_right _ _ diagonal hmass
  have hcentered : centered ≈
      S.fine.physicalPartition * diagonal + -(mean * mean) := by
    unfold centered
      finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
      finePacketTiltedGibbsConnectedResponseSquareMass
      finePacketTiltedGibbsConnectedResponseMeanMass
    exact Q'.eqv_refl _
  change finiteWeightedPairwiseVariance states weight coefficient ≈
    centered + centered
  refine Q'.eqv_trans _
    ((mass * diagonal + mass * diagonal) +
      -(mean * mean + mean * mean)) _ hgeneric ?_
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * diagonal +
        S.fine.physicalPartition * diagonal) +
      -(mean * mean + mean * mean)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hmassDiagonal hmassDiagonal)
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * diagonal + -(mean * mean)) +
      (S.fine.physicalPartition * diagonal + -(mean * mean))) _
    (twice_deficit_rearrange
      (S.fine.physicalPartition * diagonal) (mean * mean)) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm hcentered) (Q'.eqv_symm hcentered)

/-- The half-pairwise definition is exactly the normalized centered second
moment of the actual connected response. -/
theorem finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_eqv_centered
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        K hfineCutoff hcoarseCoupling M ≈
      Q'.divPos
        (finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
          K hfineCutoff hcoarseCoupling M)
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (finePhysicalPartitionSquare_pos S) := by
  let pairwise :=
    finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
      K hfineCutoff hcoarseCoupling M
  let centered :=
    finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
      K hfineCutoff hcoarseCoupling M
  let denominator := S.fine.physicalPartition * S.fine.physicalPartition
  let reciprocal := Q'.recipPos denominator
    (finePhysicalPartitionSquare_pos S)
  have hpairwise : pairwise ≈ centered + centered :=
    finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_eqv_twice_centered
      K hfineCutoff hcoarseCoupling M
  unfold finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
    Q'.divPos
  refine Q'.eqv_trans _
    (HalfPow.half * ((centered + centered) * reciprocal)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.mul_eqv_congr_right _ _ reciprocal hpairwise)
  refine Q'.eqv_trans _
    (HalfPow.half *
      (centered * reciprocal + centered * reciprocal)) _
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.add_mul_eqv centered centered reciprocal)) ?_
  refine Q'.eqv_trans _
    (HalfPow.half * (centered * reciprocal) +
      HalfPow.half * (centered * reciprocal)) _
    (Q'.mul_add_eqv HalfPow.half
      (centered * reciprocal) (centered * reciprocal)) ?_
  exact YMGap.Constructive.ExpNeg.two_halves (centered * reciprocal)

/-! ## 2. Pairwise square versus global absolute oscillation -/

private theorem finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_eqv_flat
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
        K hfineCutoff hcoarseCoupling M ≈
      listQSum
        (fun pair : PositivePhysicalSourcePair S =>
          finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
            ((positivePhysicalSourceTiltedGibbsConnectedResponse
                  K hfineCutoff hcoarseCoupling M pair.1 -
                positivePhysicalSourceTiltedGibbsConnectedResponse
                  K hfineCutoff hcoarseCoupling M pair.2) *
              (positivePhysicalSourceTiltedGibbsConnectedResponse
                  K hfineCutoff hcoarseCoupling M pair.1 -
                positivePhysicalSourceTiltedGibbsConnectedResponse
                  K hfineCutoff hcoarseCoupling M pair.2)))
        (positivePhysicalSourcePairs S) := by
  unfold finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
    finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    finiteStationaryProductJoint positivePhysicalSourcePairs
    finePacketFineSourceRawPairWeight
  exact Q'.eqv_symm
    (listQSum_cartesian_eq_nested_local _
      (positivePhysicalSources S) (positivePhysicalSources S))

theorem finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_le_oscillationMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
        K hfineCutoff hcoarseCoupling M ≤
      finePacketGlobalTiltedGibbsConnectedResponseOscillationMass
        K hfineCutoff hcoarseCoupling M := by
  let squareTerm := fun pair : PositivePhysicalSourcePair S =>
    let difference :=
      positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M pair.1 -
        positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M pair.2
    finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
      (difference * difference)
  let absTerm := fun pair : PositivePhysicalSourcePair S =>
    let difference :=
      positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M pair.1 -
        positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M pair.2
    finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
      Q'.abs difference
  refine Q'.le_trans' _
    (listQSum squareTerm (positivePhysicalSourcePairs S)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_eqv_flat
        K hfineCutoff hcoarseCoupling M)
  have hsum : listQSum squareTerm (positivePhysicalSourcePairs S) ≤
      listQSum absTerm (positivePhysicalSourcePairs S) := by
    apply listQSum_mono_local
    intro pair _
    let difference :=
      positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M pair.1 -
        positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M pair.2
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (square_le_abs_of_abs_le_one difference
        (positivePhysicalTiltedGibbsConnectedResponseDifference_abs_le_one
          K hfineCutoff hcoarseCoupling M pair.1 pair.2))
      (finePositiveSourcePairWeight_nonnegative S pair)
  refine Q'.le_trans' _ _ _ hsum ?_
  unfold finePacketGlobalTiltedGibbsConnectedResponseOscillationMass absTerm
  exact Q'.le_refl' _

theorem finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_half_oscillation
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        K hfineCutoff hcoarseCoupling M ≤
      HalfPow.half *
        finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction
          K hfineCutoff hcoarseCoupling M := by
  unfold finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
    finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction Q'.divPos
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_le_oscillationMass
        K hfineCutoff hcoarseCoupling M)
      (Q'.le_of_lt
        (Q'.recipPos_pos _ (finePhysicalPartitionSquare_pos S)))
  · exact HalfPow.half_nonneg

/-! ## 3. Strict SU(2)-anchor posterior-variance contraction -/

theorem finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_half_faceEnvelopes
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        K hfineCutoff hcoarseCoupling M ≤
      HalfPow.half *
        (finePacketGlobalConnectedResponseEnvelopeFraction
            S hfineCutoff hcoarseCoupling M.coarseRoot +
          finePacketGlobalConnectedResponseEnvelopeFraction
            S hfineCutoff hcoarseCoupling M.coarseTarget) := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_half_oscillation
      K hfineCutoff hcoarseCoupling M)
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_faceEnvelopes
        K hfineCutoff hcoarseCoupling M)
      HalfPow.half_nonneg)

/-- The posterior variance of the actual connected response is bounded by
the same strict `1449/1700` SU(2)-anchor rate: the exact variance half cancels
the two causal face envelopes. -/
theorem finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_anchorRate
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half) :
    finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        K hfineCutoff hcoarseCoupling M ≤
      finePacketAnchorVacuumPacketStrictRate := by
  have hroot :=
    finePacketGlobalConnectedResponseEnvelopeFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling cutoff half M.coarseRoot
        hfine M.coarseRoot_mem
  have htarget :=
    finePacketGlobalConnectedResponseEnvelopeFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling cutoff half M.coarseTarget
        hfine M.coarseTarget_mem
  have hsum := Q'.add_le_add hroot htarget
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    hsum HalfPow.half_nonneg
  exact Q'.le_trans' _ _ _
    (finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_half_faceEnvelopes
      K hfineCutoff hcoarseCoupling M)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        refine Q'.eqv_trans _
          (HalfPow.half * finePacketAnchorVacuumPacketStrictRate +
            HalfPow.half * finePacketAnchorVacuumPacketStrictRate) _
          (Q'.mul_add_eqv HalfPow.half
            finePacketAnchorVacuumPacketStrictRate
            finePacketAnchorVacuumPacketStrictRate) ?_
        exact YMGap.Constructive.ExpNeg.two_halves
          finePacketAnchorVacuumPacketStrictRate)))

theorem finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_lt_one_at_anchor
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half) :
    finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        K hfineCutoff hcoarseCoupling M < (1 : Q') := by
  exact Q'.lt_of_le_of_lt
    (finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_anchorRate
      K hfineCutoff hcoarseCoupling M cutoff half hfine)
    finePacketAnchorVacuumPacketStrictRate_lt_one

/-! ## Axiom audit -/

#print axioms finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
#print axioms finePacketTiltedGibbsConnectedResponseCenteredVarianceNumerator
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_eqv_twice_centered
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_eqv_centered
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass_le_oscillationMass
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_half_oscillation
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_half_faceEnvelopes
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_le_anchorRate
#print axioms finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction_lt_one_at_anchor

end YMGap.Continuum.Z4DyadicBinaryConnectedObservablePosteriorVarianceFraction
