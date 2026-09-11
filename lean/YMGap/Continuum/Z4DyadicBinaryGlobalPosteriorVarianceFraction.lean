/-
# Global one-face posterior variance at the SU(2) anchor

The global response-oscillation estimate has an exact quadratic consequence.
For the normalized fine source law, let `r(source)` be the conditional
probability that one selected coarse face is positive.  Two independent
sources satisfy the finite identity

  `2 * Var(r) = E[(r(first) - r(second))^2]`.

Since every event response lies in `[0,1]`, its difference lies in `[-1,1]`
and hence `difference^2 <= |difference|`.  Therefore the normalized posterior
variance is at most one half of the already bounded response oscillation.  At
the named SU(2) anchor this gives the explicit volume-independent rate

  `Var(r) <= 1449/3400 < 1`.

This is the posterior variance of one actual face-event response under the
fine source law.  The existing connected refresh observable also contains a
joint two-face event and signed moment coefficients; no identification with
that full centered refresh form, dense spectral bound, completed gap,
thermodynamic limit, continuum theory, or Clay theorem is asserted here.

Constructive contract: exact finite weighted pairwise variance, rational
absolute-value order, and the previously proved SU(2) response oscillation
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, enlarged heartbeat budget, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

namespace YMGap.Continuum.Z4DyadicBinaryGlobalPosteriorVarianceFraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.mkPos_num, Q'.mkPos_den,
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

private theorem finePositiveSourceWeight_nonnegative
    (S : SlabScalePair) (source : PositivePhysicalSource S) :
    (0 : Q') ≤ S.fine.physicalTerm source.1 :=
  Q'.le_of_lt source.2.2

private theorem finePositiveSourcePairWeight_nonnegative
    (S : SlabScalePair) (pair : PositivePhysicalSourcePair S) :
    (0 : Q') ≤ finePacketFineSourceRawPairWeight
      S pair.1.1 pair.2.1 := by
  unfold finePacketFineSourceRawPairWeight
  exact Q'.mul_nonneg _ _
    (finePositiveSourceWeight_nonnegative S pair.1)
    (finePositiveSourceWeight_nonnegative S pair.2)

/-! ## 1. The actual posterior coefficient and its unit interval -/

def finePacketTiltedGibbsFaceResponse
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) (source : PositivePhysicalSource S) : Q' :=
  positivePhysicalSourceTiltedGibbsEventMass
    S hfineCutoff hcoarseCoupling source
      (slabPhysicalFacePositiveB observableFaceId)

private theorem fineCouplingKernelOutputEventMass_eqv_finiteEventMass_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (source : EdgeLabelling) (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass K source event ≈
      finiteEventMass (K.kernel source)
        S.coarse.physicalLabellings event := by
  unfold fineCouplingKernelOutputEventMass finiteEventMass
  exact listQSum_filter (K.kernel source) event
    S.coarse.physicalLabellings

private theorem fineCouplingKernelOutputEventMass_unitInterval_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤ fineCouplingKernelOutputEventMass K source event ∧
      fineCouplingKernelOutputEventMass K source event ≤ (1 : Q') := by
  have heqv := fineCouplingKernelOutputEventMass_eqv_finiteEventMass_local
    K source event
  constructor
  · exact Q'.le_trans' _ _ _
      (finiteEventMass_nonnegative
        (K.kernel source) S.coarse.physicalLabellings event
        (fun target htarget =>
          K.nonnegative source target hsource htarget))
      (Q'.ge_of_eqv heqv)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv heqv)
      (finiteEventMass_le_one
        (K.kernel source) S.coarse.physicalLabellings event
        (fun target htarget =>
          K.nonnegative source target hsource htarget)
        (K.row_normalized source hsource))

theorem finePacketTiltedGibbsFaceResponse_unitInterval
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) (source : PositivePhysicalSource S) :
    (0 : Q') ≤ finePacketTiltedGibbsFaceResponse
        S hfineCutoff hcoarseCoupling observableFaceId source ∧
      finePacketTiltedGibbsFaceResponse
        S hfineCutoff hcoarseCoupling observableFaceId source ≤ (1 : Q') := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let event := slabPhysicalFacePositiveB observableFaceId
  have hactual := fineCouplingKernelOutputEventMass_unitInterval_local
    K source.1 source.2.1 event
  have heqv := fineCouplingPhysicalKernelOutputEventMass_eqv_tiltedGibbs
    S hfineCutoff hcoarseCoupling source event
  unfold finePacketTiltedGibbsFaceResponse
  constructor
  · exact Q'.le_trans' _ _ _ hactual.1 (Q'.le_of_eqv heqv)
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv) hactual.2

private theorem finePacketTiltedGibbsFaceResponseDifference_unitInterval
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) (first second : PositivePhysicalSource S) :
    (-(1 : Q')) ≤
        finePacketTiltedGibbsFaceResponse
            S hfineCutoff hcoarseCoupling observableFaceId first -
          finePacketTiltedGibbsFaceResponse
            S hfineCutoff hcoarseCoupling observableFaceId second ∧
      finePacketTiltedGibbsFaceResponse
            S hfineCutoff hcoarseCoupling observableFaceId first -
          finePacketTiltedGibbsFaceResponse
            S hfineCutoff hcoarseCoupling observableFaceId second ≤
        (1 : Q') := by
  let firstResponse := finePacketTiltedGibbsFaceResponse
    S hfineCutoff hcoarseCoupling observableFaceId first
  let secondResponse := finePacketTiltedGibbsFaceResponse
    S hfineCutoff hcoarseCoupling observableFaceId second
  have hfirst := finePacketTiltedGibbsFaceResponse_unitInterval
    S hfineCutoff hcoarseCoupling observableFaceId first
  have hsecond := finePacketTiltedGibbsFaceResponse_unitInterval
    S hfineCutoff hcoarseCoupling observableFaceId second
  change (-(1 : Q')) ≤ firstResponse - secondResponse ∧
    firstResponse - secondResponse ≤ (1 : Q')
  constructor
  · have hadd := Q'.add_le_add
      (Q'.neg_le_neg hsecond.2) hfirst.1
    rw [Q'.add_zero'] at hadd
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (Q'.add_comm_eqv (-secondResponse) firstResponse))
  · have hadd := Q'.add_le_add hfirst.2
      (Q'.nonpos_neg_of_nonneg hsecond.1)
    rwa [Q'.add_zero'] at hadd

private theorem square_le_abs_of_unitInterval
    (difference : Q')
    (hdifference : (-(1 : Q')) ≤ difference ∧
      difference ≤ (1 : Q')) :
    difference * difference ≤ Q'.abs difference := by
  have habsOne : Q'.abs difference ≤ (1 : Q') :=
    Q'.abs_le_of_bounds hdifference.1 hdifference.2
  have hsquare : difference * difference ≤
      Q'.abs difference * Q'.abs difference :=
    Q'.mul_le_of_bounds
      (Q'.abs_nonneg difference) (Q'.abs_nonneg difference)
      (YMGap.Constructive.ExpNeg.neg_abs_le difference)
      (Q'.le_abs_self difference)
      (YMGap.Constructive.ExpNeg.neg_abs_le difference)
      (Q'.le_abs_self difference)
  have habsContract : Q'.abs difference * Q'.abs difference ≤
      Q'.abs difference * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ habsOne
      (Q'.abs_nonneg difference)
  exact Q'.le_trans' _ _ _ hsquare
    (Q'.le_trans' _ _ _ habsContract
      (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs difference))))

/-! ## 2. Pairwise and centered posterior variance -/

/-- The unnormalized two-replica squared response difference under the actual
fine source weights. -/
def finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  finiteWeightedPairwiseVariance
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (finePacketTiltedGibbsFaceResponse
      S hfineCutoff hcoarseCoupling observableFaceId)

/-- The conventional normalized posterior variance: one half of the
normalized independent-pair squared response difference. -/
def finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  HalfPow.half *
    Q'.divPos
      (finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
        S hfineCutoff hcoarseCoupling observableFaceId)
      (S.fine.physicalPartition * S.fine.physicalPartition)
      (finePhysicalPartitionSquare_pos S)

def finePacketTiltedGibbsFaceResponseMeanMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  finiteListWeightedMean
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (finePacketTiltedGibbsFaceResponse
      S hfineCutoff hcoarseCoupling observableFaceId)

def finePacketTiltedGibbsFaceResponseSquareMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  finiteWeightedSquare
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (finePacketTiltedGibbsFaceResponse
      S hfineCutoff hcoarseCoupling observableFaceId)

/-- The denominator-cleared centered second moment
`partition * secondMoment - mean^2`. -/
def finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  S.fine.physicalPartition *
      finePacketTiltedGibbsFaceResponseSquareMass
        S hfineCutoff hcoarseCoupling observableFaceId -
    finePacketTiltedGibbsFaceResponseMeanMass
        S hfineCutoff hcoarseCoupling observableFaceId *
      finePacketTiltedGibbsFaceResponseMeanMass
        S hfineCutoff hcoarseCoupling observableFaceId

/-- The independent-pair squared response mass is exactly twice the
denominator-cleared centered second moment. -/
theorem finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_eqv_twice_centered
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) :
    finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
        S hfineCutoff hcoarseCoupling observableFaceId ≈
      finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
          S hfineCutoff hcoarseCoupling observableFaceId +
        finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
          S hfineCutoff hcoarseCoupling observableFaceId := by
  let states := positivePhysicalSources S
  let weight := fun source : PositivePhysicalSource S =>
    S.fine.physicalTerm source.1
  let coefficient := finePacketTiltedGibbsFaceResponse
    S hfineCutoff hcoarseCoupling observableFaceId
  let mass := finiteWeightedMass states weight
  let diagonal := finiteWeightedSquare states weight coefficient
  let mean := finiteListWeightedMean states weight coefficient
  let centered :=
    finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
      S hfineCutoff hcoarseCoupling observableFaceId
  have hgeneric := finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean
    states weight coefficient
  have hmass : mass ≈ S.fine.physicalPartition := by
    exact finePositivePhysicalSources_weight_total S
  have hmassDiagonal : mass * diagonal ≈
      S.fine.physicalPartition * diagonal :=
    Q'.mul_eqv_congr_right _ _ diagonal hmass
  have hcentered : centered ≈
      S.fine.physicalPartition * diagonal + -(mean * mean) := by
    unfold centered finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
      finePacketTiltedGibbsFaceResponseSquareMass
      finePacketTiltedGibbsFaceResponseMeanMass
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

/-- The half-pairwise definition is exactly the usual normalized centered
second moment. -/
theorem finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_eqv_centered
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) :
    finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≈
      Q'.divPos
        (finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
          S hfineCutoff hcoarseCoupling observableFaceId)
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (finePhysicalPartitionSquare_pos S) := by
  let pairwise :=
    finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
      S hfineCutoff hcoarseCoupling observableFaceId
  let centered :=
    finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
      S hfineCutoff hcoarseCoupling observableFaceId
  let denominator := S.fine.physicalPartition * S.fine.physicalPartition
  let reciprocal := Q'.recipPos denominator
    (finePhysicalPartitionSquare_pos S)
  have hpairwise : pairwise ≈ centered + centered :=
    finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_eqv_twice_centered
      S hfineCutoff hcoarseCoupling observableFaceId
  unfold finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
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

/-! ## 3. Domination by the global response oscillation -/

private theorem finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_eqv_flat
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) :
    finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
        S hfineCutoff hcoarseCoupling observableFaceId ≈
      listQSum
        (fun pair : PositivePhysicalSourcePair S =>
          finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
            ((finePacketTiltedGibbsFaceResponse
                  S hfineCutoff hcoarseCoupling observableFaceId pair.1 -
                finePacketTiltedGibbsFaceResponse
                  S hfineCutoff hcoarseCoupling observableFaceId pair.2) *
              (finePacketTiltedGibbsFaceResponse
                  S hfineCutoff hcoarseCoupling observableFaceId pair.1 -
                finePacketTiltedGibbsFaceResponse
                  S hfineCutoff hcoarseCoupling observableFaceId pair.2)))
        (positivePhysicalSourcePairs S) := by
  unfold finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
    finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    finiteStationaryProductJoint positivePhysicalSourcePairs
    finePacketFineSourceRawPairWeight
  exact Q'.eqv_symm
    (listQSum_cartesian_eq_nested_local _
      (positivePhysicalSources S) (positivePhysicalSources S))

theorem finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_le_oscillationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) :
    finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      finePacketGlobalTiltedGibbsFaceResponseOscillationMass
        S hfineCutoff hcoarseCoupling observableFaceId := by
  let squareTerm := fun pair : PositivePhysicalSourcePair S =>
    let difference :=
      finePacketTiltedGibbsFaceResponse
          S hfineCutoff hcoarseCoupling observableFaceId pair.1 -
        finePacketTiltedGibbsFaceResponse
          S hfineCutoff hcoarseCoupling observableFaceId pair.2
    finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
      (difference * difference)
  let absTerm := fun pair : PositivePhysicalSourcePair S =>
    let difference :=
      finePacketTiltedGibbsFaceResponse
          S hfineCutoff hcoarseCoupling observableFaceId pair.1 -
        finePacketTiltedGibbsFaceResponse
          S hfineCutoff hcoarseCoupling observableFaceId pair.2
    finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
      Q'.abs difference
  refine Q'.le_trans' _ (listQSum squareTerm
    (positivePhysicalSourcePairs S)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_eqv_flat
        S hfineCutoff hcoarseCoupling observableFaceId)
  have hsum : listQSum squareTerm (positivePhysicalSourcePairs S) ≤
      listQSum absTerm (positivePhysicalSourcePairs S) := by
    apply listQSum_mono_local
    intro pair _
    let difference :=
      finePacketTiltedGibbsFaceResponse
          S hfineCutoff hcoarseCoupling observableFaceId pair.1 -
        finePacketTiltedGibbsFaceResponse
          S hfineCutoff hcoarseCoupling observableFaceId pair.2
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (square_le_abs_of_unitInterval difference
        (finePacketTiltedGibbsFaceResponseDifference_unitInterval
          S hfineCutoff hcoarseCoupling observableFaceId pair.1 pair.2))
      (finePositiveSourcePairWeight_nonnegative S pair)
  refine Q'.le_trans' _ _ _ hsum ?_
  unfold finePacketGlobalTiltedGibbsFaceResponseOscillationMass absTerm
    finePacketTiltedGibbsFaceResponse
  exact Q'.le_refl' _

theorem finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_le_half_oscillation
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) :
    finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      HalfPow.half *
        finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
          S hfineCutoff hcoarseCoupling observableFaceId := by
  unfold finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
    finePacketGlobalTiltedGibbsFaceResponseOscillationFraction Q'.divPos
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_le_oscillationMass
        S hfineCutoff hcoarseCoupling observableFaceId)
      (Q'.le_of_lt
        (Q'.recipPos_pos _ (finePhysicalPartitionSquare_pos S)))
  · exact HalfPow.half_nonneg

def finePacketAnchorPosteriorVarianceRate : Q' :=
  Q'.mkPos 1449 3400 (by decide)

theorem half_anchorVacuumPacketStrictRate_eqv_posteriorVarianceRate :
    HalfPow.half * finePacketAnchorVacuumPacketStrictRate ≈
      finePacketAnchorPosteriorVarianceRate := by
  unfold HalfPow.half finePacketAnchorVacuumPacketStrictRate
    finePacketAnchorPosteriorVarianceRate
  decide

/-- At the named SU(2) anchor the conventional normalized posterior variance
of the selected one-face conditional response is at most `1449/3400`. -/
theorem finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_le_anchorRate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      finePacketAnchorPosteriorVarianceRate := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_le_half_oscillation
      S hfineCutoff hcoarseCoupling observableFaceId)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
        (finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_anchorVacuumPacketRate
          S hfineCutoff hcoarseCoupling cutoff half observableFaceId
            hfine hobservableFace)
        HalfPow.half_nonneg)
      (Q'.le_of_eqv
        half_anchorVacuumPacketStrictRate_eqv_posteriorVarianceRate))

theorem finePacketAnchorPosteriorVarianceRate_lt_one :
    finePacketAnchorPosteriorVarianceRate < (1 : Q') := by
  unfold finePacketAnchorPosteriorVarianceRate
  decide

theorem finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_lt_one_at_anchor
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
        S hfineCutoff hcoarseCoupling observableFaceId < (1 : Q') := by
  exact Q'.lt_of_le_of_lt
    (finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_le_anchorRate
      S hfineCutoff hcoarseCoupling cutoff half observableFaceId
        hfine hobservableFace)
    finePacketAnchorPosteriorVarianceRate_lt_one

/-! ## Axiom audit -/

#print axioms finePacketTiltedGibbsFaceResponse
#print axioms finePacketTiltedGibbsFaceResponse_unitInterval
#print axioms finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass
#print axioms finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction
#print axioms finePacketTiltedGibbsFaceResponseCenteredVarianceNumerator
#print axioms finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_eqv_twice_centered
#print axioms finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_eqv_centered
#print axioms finePacketGlobalTiltedGibbsFaceResponsePairwiseVarianceMass_le_oscillationMass
#print axioms finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_le_half_oscillation
#print axioms finePacketAnchorPosteriorVarianceRate
#print axioms finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_le_anchorRate
#print axioms finePacketAnchorPosteriorVarianceRate_lt_one
#print axioms finePacketGlobalTiltedGibbsFaceResponsePosteriorVarianceFraction_lt_one_at_anchor

end YMGap.Continuum.Z4DyadicBinaryGlobalPosteriorVarianceFraction
