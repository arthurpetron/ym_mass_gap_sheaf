/-
# Exact fluctuation--bias decomposition of the connected production/refresh row

The strict `1449/1700` theorem controls the normalized square of the selected
production-minus-refresh row after subtracting its fine-source mean.  It does
not control the uncentered row by itself.  This file identifies the missing
term exactly.

For the actual cutoff-one physical kernel, let `A(source)` be the connected
production-minus-coarse-refresh row action.  Constructive finite weighted
algebra proves

  `E[A^2] = E[(A - E[A])^2] + E[A]^2`.

Moreover the normalized mean `E[A]` is exactly the already-defined
`centeredCylinderRemainder`.  Thus the uncentered selected-row form is the
strict posterior-variance form plus one literal observable-matching bias
square.  At the SU(2) strong-coupling anchor this gives

  `uncenteredForm <= 1449/1700 + centeredCylinderRemainder^2`.

This is an RG blocking-row identity, not an Osterwalder--Schrader transfer
identity.  It does not turn the absolute one-observable estimate into a
relative all-vector bound, and it does not construct the weak-to-strong
completed RG intertwiner, a thermodynamic limit, a continuum theory, or the
Clay mass gap.

Constructive contract: finite rational sums and positive-denominator
normalization only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservableCenteredProductionRefreshForm

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableProductionRefreshBiasVariance

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
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableCenteredProductionRefreshForm
open YMGap.Continuum.Z4DyadicBinaryConnectedObservablePosteriorVarianceFraction
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction
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
  exact Q'.eqv_of_eq (Q'.add_zero' (left + -right))

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

private theorem sub_mul_expand_local (left right factor : Q') :
    (left - right) * factor ≈ left * factor - right * factor := by
  refine Q'.eqv_trans _ (factor * (left - right)) _
    (Q'.mul_comm_eqv (left - right) factor) ?_
  refine Q'.eqv_trans _ (factor * left - factor * right) _ ?_ ?_
  · refine Q'.eqv_trans _
      (factor * left + factor * (-right)) _
      (Q'.mul_add_eqv factor left (-right)) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv factor right)
  exact sub_eqv_both_local
    (Q'.mul_comm_eqv factor left) (Q'.mul_comm_eqv factor right)

private theorem mul_swap_last_local (first second third : Q') :
    (first * second) * third ≈ (first * third) * second := by
  refine Q'.eqv_trans _ (first * (second * third)) _
    (Q'.mul_assoc_eqv first second third) ?_
  refine Q'.eqv_trans _ (first * (third * second)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left first _ _
      (Q'.mul_comm_eqv second third)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv first third second)

private theorem paired_square_swap_local (left right : Q') :
    (left * right) * (left * right) ≈
      (right * right) * (left * left) := by
  ring_qeqv

/-- Exact cancellation of the factor two in a signed half-pairwise form. -/
private theorem half_twice_difference_mul_eqv
    (positive negative reciprocal : Q') :
    HalfPow.half *
        (((positive + positive) + -(negative + negative)) * reciprocal) ≈
      positive * reciprocal - negative * reciprocal := by
  let x := positive * reciprocal
  let y := negative * reciprocal
  have hinside :
      ((positive + positive) + -(negative + negative)) * reciprocal ≈
        (x + x) + -(y + y) := by
    refine Q'.eqv_trans _
      ((positive + positive) * reciprocal +
        (-(negative + negative)) * reciprocal) _
      (Q'.add_mul_eqv (positive + positive)
        (-(negative + negative)) reciprocal) ?_
    apply Q'.add_eqv_congr'
    · exact Q'.add_mul_eqv positive positive reciprocal
    refine Q'.eqv_trans _ (-((negative + negative) * reciprocal)) _
      (Q'.neg_mul_eqv (negative + negative) reciprocal) ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.add_mul_eqv negative negative reciprocal)
  refine Q'.eqv_trans _
    (HalfPow.half * ((x + x) + -(y + y))) _
    (Q'.mul_eqv_congr_left HalfPow.half _ _ hinside) ?_
  refine Q'.eqv_trans _
    (HalfPow.half * (x + x) + HalfPow.half * (-(y + y))) _
    (Q'.mul_add_eqv HalfPow.half (x + x) (-(y + y))) ?_
  apply Q'.add_eqv_congr'
  · refine Q'.eqv_trans _
      (HalfPow.half * x + HalfPow.half * x) _
      (Q'.mul_add_eqv HalfPow.half x x) ?_
    exact YMGap.Constructive.ExpNeg.two_halves x
  refine Q'.eqv_trans _ (-(HalfPow.half * (y + y))) _
    (Q'.mul_neg_eqv HalfPow.half (y + y)) ?_
  refine Q'.eqv_trans _
    (-(HalfPow.half * y + HalfPow.half * y)) _
    (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv HalfPow.half y y)) ?_
  exact Q'.neg_eqv_congr _ _
    (YMGap.Constructive.ExpNeg.two_halves y)

private theorem finePhysicalPartition_pos (S : SlabScalePair) :
    (0 : Q') < S.fine.physicalPartition :=
  slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent

private theorem finePhysicalPartitionSquare_pos (S : SlabScalePair) :
    (0 : Q') < S.fine.physicalPartition * S.fine.physicalPartition :=
  Q'.mul_pos (finePhysicalPartition_pos S) (finePhysicalPartition_pos S)

/-! ## 1. Uncentered row, its raw mean, and its bias square -/

/-- Fine-source weighted mean mass of the uncentered selected physical row. -/
def finePacketPhysicalConnectedProductionRefreshMeanMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  finiteListWeightedMean
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (fun source => coarseGibbsRefreshConnectedRowAction
      S hfineCutoff hcoarseCoupling M source.1)

/-- Normalized square of the uncentered selected physical row. -/
def finePacketGlobalPhysicalConnectedProductionRefreshForm
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.divPos
    (S.fine.physicalPartition *
      finiteWeightedSquare
        (positivePhysicalSources S)
        (fun source => S.fine.physicalTerm source.1)
        (fun source => coarseGibbsRefreshConnectedRowAction
          S hfineCutoff hcoarseCoupling M source.1))
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

/-- The contribution of the uncentered row mean, on the same `Z^2`
normalization as the row form. -/
def finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.divPos
    (finePacketPhysicalConnectedProductionRefreshMeanMass
        S hfineCutoff hcoarseCoupling M *
      finePacketPhysicalConnectedProductionRefreshMeanMass
        S hfineCutoff hcoarseCoupling M)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

/-! ## 2. The normalized row mean is the connected blocking remainder -/

/-- The raw positive-source row mean is the partition times the normalized
mean already used to center the row. -/
theorem finePacketPhysicalConnectedProductionRefreshMeanMass_eqv_partition_mul_mean
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketPhysicalConnectedProductionRefreshMeanMass
        S hfineCutoff hcoarseCoupling M ≈
      S.fine.physicalPartition *
        finePacketPhysicalConnectedProductionRefreshMean
          S hfineCutoff hcoarseCoupling M := by
  let states := positivePhysicalSources S
  let weight := fun source : PositivePhysicalSource S =>
    S.fine.physicalTerm source.1
  let action := fun source : PositivePhysicalSource S =>
    coarseGibbsRefreshConnectedRowAction
      S hfineCutoff hcoarseCoupling M source.1
  let mean := finePacketPhysicalConnectedProductionRefreshMean
    S hfineCutoff hcoarseCoupling M
  have hcentered :=
    positivePhysicalCenteredGibbsRefreshConnectedRowAction_weightedMean_eqv_zero
      S hfineCutoff hcoarseCoupling M
  have hmass : listQSum weight states ≈ S.fine.physicalPartition :=
    finePositivePhysicalSources_weight_total S
  have hsplit :
      finiteListWeightedMean states weight
          (positivePhysicalCenteredGibbsRefreshConnectedRowAction
            S hfineCutoff hcoarseCoupling M) ≈
        finiteListWeightedMean states weight action -
          mean * listQSum weight states := by
    unfold finiteListWeightedMean
    refine Q'.eqv_trans _
      (listQSum
        (fun source => action source * weight source -
          mean * weight source) states) _ ?_ ?_
    · apply listQSum_congr
      intro source
      exact sub_mul_expand_local (action source) mean (weight source)
    refine Q'.eqv_trans _
      (listQSum (fun source => action source * weight source) states -
        listQSum (fun source => mean * weight source) states) _
      (listQSum_sub_local _ _ states) ?_
    exact sub_eqv_both_local (Q'.eqv_refl _)
      (listQSum_mul_left mean weight states)
  have hzero :
      finiteListWeightedMean states weight action -
          mean * S.fine.physicalPartition ≈ 0 := by
    exact Q'.eqv_trans _
      (finiteListWeightedMean states weight action -
        mean * listQSum weight states) _
      (sub_eqv_both_local (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_left mean _ _ (Q'.eqv_symm hmass)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hsplit) hcentered)
  refine Q'.eqv_trans _
    ((finiteListWeightedMean states weight action -
        mean * S.fine.physicalPartition) +
      mean * S.fine.physicalPartition) _ ?_ ?_
  · unfold finePacketPhysicalConnectedProductionRefreshMeanMass
    refine Q'.eqv_trans _
      (mean * S.fine.physicalPartition +
        (finiteListWeightedMean states weight action -
          mean * S.fine.physicalPartition)) _
      (Q'.add_sub_cancel_eqv
        (finiteListWeightedMean states weight action)
        (mean * S.fine.physicalPartition)) ?_
    exact Q'.add_comm_eqv _ _
  refine Q'.eqv_trans _ (0 + mean * S.fine.physicalPartition) _ ?_ ?_
  · exact Q'.add_eqv_congr' hzero (Q'.eqv_refl _)
  refine Q'.eqv_trans _ (mean * S.fine.physicalPartition) _
    (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
  exact Q'.mul_comm_eqv mean S.fine.physicalPartition

private theorem physicalActionRawMean_eqv_positiveAux
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            coarseGibbsRefreshConnectedRowAction
                S hfineCutoff hcoarseCoupling M source *
              S.fine.physicalTerm source)
          sources ≈
        finiteListWeightedMean
          (positivePhysicalSourcesAux S sources hphysical)
          (fun source => S.fine.physicalTerm source.1)
          (fun source => coarseGibbsRefreshConnectedRowAction
            S hfineCutoff hcoarseCoupling M source.1)
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive : (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum, positivePhysicalSourcesAux, dif_pos hpositive,
          finiteListWeightedMean]
        exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (physicalActionRawMean_eqv_positiveAux
            S hfineCutoff hcoarseCoupling M tail htail)
      · simp only [listQSum, positivePhysicalSourcesAux, dif_neg hpositive,
          finiteListWeightedMean]
        refine Q'.eqv_trans _
          (0 + listQSum
            (fun item =>
              coarseGibbsRefreshConnectedRowAction
                  S hfineCutoff hcoarseCoupling M item *
                S.fine.physicalTerm item)
            tail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (coarseGibbsRefreshConnectedRowAction
                  S hfineCutoff hcoarseCoupling M source * 0) _
              (Q'.mul_eqv_congr_left _ _ _
                (physicalTerm_eqv_zero_of_not_positive
                  S.fine source hpositive))
              (Q'.mul_zero_eqv _))
            (Q'.eqv_refl _)
        refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
        exact physicalActionRawMean_eqv_positiveAux
          S hfineCutoff hcoarseCoupling M tail htail

/-- The normalized positive-source mean is the existing full signed Gibbs
average, hence exactly the selected connected cylinder remainder. -/
theorem finePacketPhysicalConnectedProductionRefreshMean_eqv_centeredRemainder
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketPhysicalConnectedProductionRefreshMean
        S hfineCutoff hcoarseCoupling M ≈
      centeredCylinderRemainder
        (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  let action := fun source : EdgeLabelling =>
    coarseGibbsRefreshConnectedRowAction
      S hfineCutoff hcoarseCoupling M source
  let meanMass := finePacketPhysicalConnectedProductionRefreshMeanMass
    S hfineCutoff hcoarseCoupling M
  let mean := finePacketPhysicalConnectedProductionRefreshMean
    S hfineCutoff hcoarseCoupling M
  let reciprocal := Q'.recipPos S.fine.physicalPartition
    (finePhysicalPartition_pos S)
  have hraw :
      listQSum (fun source => action source * S.fine.physicalTerm source)
          S.fine.physicalLabellings ≈ meanMass := by
    unfold meanMass finePacketPhysicalConnectedProductionRefreshMeanMass
      positivePhysicalSources
    exact physicalActionRawMean_eqv_positiveAux
      S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
        (fun _ hsource => hsource)
  have hmeanMass : meanMass ≈ S.fine.physicalPartition * mean :=
    finePacketPhysicalConnectedProductionRefreshMeanMass_eqv_partition_mul_mean
      S hfineCutoff hcoarseCoupling M
  have haverage :
      coarseGibbsRefreshConnectedSignedSourceAverage
          S hfineCutoff hcoarseCoupling M ≈ mean := by
    unfold coarseGibbsRefreshConnectedSignedSourceAverage
      SlabPhysicalData.normalizedMass Q'.divPos
    refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          (action source * S.fine.physicalTerm source) * reciprocal)
        S.fine.physicalLabellings) _ ?_ ?_
    · apply listQSum_congr
      intro source
      change
        (S.fine.physicalTerm source * reciprocal) * action source ≈
          (action source * S.fine.physicalTerm source) * reciprocal
      refine Q'.eqv_trans _
        (S.fine.physicalTerm source * action source * reciprocal) _
        (mul_swap_last_local
          (S.fine.physicalTerm source) reciprocal (action source)) ?_
      exact Q'.mul_eqv_congr_right _ _ reciprocal
        (Q'.mul_comm_eqv _ _)
    refine Q'.eqv_trans _
      (listQSum (fun source => action source * S.fine.physicalTerm source)
          S.fine.physicalLabellings * reciprocal) _
      (listQSum_mul_right _ reciprocal S.fine.physicalLabellings) ?_
    refine Q'.eqv_trans _ (meanMass * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ reciprocal hraw) ?_
    refine Q'.eqv_trans _
      ((S.fine.physicalPartition * mean) * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ reciprocal hmeanMass) ?_
    refine Q'.eqv_trans _
      (mean * (S.fine.physicalPartition * reciprocal)) _ ?_ ?_
    · ring_qeqv
    refine Q'.eqv_trans _ (mean * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left mean _ _
        (Q'.mul_recipPos_eqv S.fine.physicalPartition
          (finePhysicalPartition_pos S))
    exact Q'.mul_one_eqv mean
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm haverage)
    (coarseGibbsRefreshConnectedSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M)

/-! ## 3. Exact normalized fluctuation--bias decomposition -/

def finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  finiteWeightedPairwiseVariance
    (positivePhysicalSources S)
    (fun source => S.fine.physicalTerm source.1)
    (fun source => coarseGibbsRefreshConnectedRowAction
      S hfineCutoff hcoarseCoupling M source.1)

theorem finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass_eqv_response
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass
        S hfineCutoff hcoarseCoupling M ≈
      finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
        (physicalKernel S hfineCutoff hcoarseCoupling)
        hfineCutoff hcoarseCoupling M := by
  unfold finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass
    finePacketGlobalTiltedGibbsConnectedResponsePairwiseVarianceMass
    finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    finiteStationaryProductJoint
  apply listQSum_congr
  intro first
  apply listQSum_congr
  intro second
  apply Q'.mul_eqv_congr_left
  let refresh := observableExpectation S.coarse.normalizedMass
    S.coarse.physicalLabellings
    (connectedRemainderObservable
      (physicalKernel S hfineCutoff hcoarseCoupling) M)
  have hfirst :=
    coarseGibbsRefreshConnectedRowAction_positive_eqv_response_sub_refresh
      S hfineCutoff hcoarseCoupling M first
  have hsecond :=
    coarseGibbsRefreshConnectedRowAction_positive_eqv_response_sub_refresh
      S hfineCutoff hcoarseCoupling M second
  have hdifference :
      coarseGibbsRefreshConnectedRowAction
          S hfineCutoff hcoarseCoupling M first.1 +
        -coarseGibbsRefreshConnectedRowAction
          S hfineCutoff hcoarseCoupling M second.1 ≈
      positivePhysicalSourceTiltedGibbsConnectedResponse
          (physicalKernel S hfineCutoff hcoarseCoupling)
          hfineCutoff hcoarseCoupling M first +
        -positivePhysicalSourceTiltedGibbsConnectedResponse
          (physicalKernel S hfineCutoff hcoarseCoupling)
          hfineCutoff hcoarseCoupling M second := by
    refine Q'.eqv_trans _
      ((positivePhysicalSourceTiltedGibbsConnectedResponse
            (physicalKernel S hfineCutoff hcoarseCoupling)
            hfineCutoff hcoarseCoupling M first - refresh) +
        -(positivePhysicalSourceTiltedGibbsConnectedResponse
            (physicalKernel S hfineCutoff hcoarseCoupling)
            hfineCutoff hcoarseCoupling M second - refresh)) _ ?_ ?_
    · exact Q'.add_eqv_congr' hfirst
        (Q'.neg_eqv_congr _ _ hsecond)
    exact centered_difference_eqv_original _ _ refresh
  exact mul_eqv_both_local hdifference hdifference

/-- The half-pairwise square of the uncentered row is the existing posterior
variance of the production response. -/
theorem finePacketPhysicalConnectedProductionRefreshHalfPairwise_eqv_posterior
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    HalfPow.half *
        Q'.divPos
          (finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass
            S hfineCutoff hcoarseCoupling M)
          (S.fine.physicalPartition * S.fine.physicalPartition)
          (finePhysicalPartitionSquare_pos S) ≈
      finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        (physicalKernel S hfineCutoff hcoarseCoupling)
        hfineCutoff hcoarseCoupling M := by
  unfold finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
    Q'.divPos
  exact Q'.mul_eqv_congr_left HalfPow.half _ _
    (Q'.mul_eqv_congr_right _ _ _
      (finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass_eqv_response
        S hfineCutoff hcoarseCoupling M))

/-- Generic pairwise-variance algebra, on the actual physical source mass,
identifies half of the normalized pairwise square with raw square minus bias. -/
theorem finePacketPhysicalConnectedProductionRefreshHalfPairwise_eqv_form_sub_bias
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    HalfPow.half *
        Q'.divPos
          (finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass
            S hfineCutoff hcoarseCoupling M)
          (S.fine.physicalPartition * S.fine.physicalPartition)
          (finePhysicalPartitionSquare_pos S) ≈
      finePacketGlobalPhysicalConnectedProductionRefreshForm
          S hfineCutoff hcoarseCoupling M -
        finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
          S hfineCutoff hcoarseCoupling M := by
  let states := positivePhysicalSources S
  let weight := fun source : PositivePhysicalSource S =>
    S.fine.physicalTerm source.1
  let action := fun source : PositivePhysicalSource S =>
    coarseGibbsRefreshConnectedRowAction
      S hfineCutoff hcoarseCoupling M source.1
  let mass := finiteWeightedMass states weight
  let diagonal := finiteWeightedSquare states weight action
  let mean := finiteListWeightedMean states weight action
  let partition := S.fine.physicalPartition
  let denominator := partition * partition
  let reciprocal := Q'.recipPos denominator
    (finePhysicalPartitionSquare_pos S)
  have hgeneric :=
    finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean
      states weight action
  have hmass : mass ≈ partition :=
    finePositivePhysicalSources_weight_total S
  have hgenericPhysical :
      finiteWeightedPairwiseVariance states weight action ≈
        ((partition * diagonal + partition * diagonal) +
          -(mean * mean + mean * mean)) := by
    refine Q'.eqv_trans _
      ((mass * diagonal + mass * diagonal) +
        -(mean * mean + mean * mean)) _ hgeneric ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ diagonal hmass)
        (Q'.mul_eqv_congr_right _ _ diagonal hmass))
      (Q'.eqv_refl _)
  change
    HalfPow.half *
        (finiteWeightedPairwiseVariance states weight action * reciprocal) ≈
      (partition * diagonal) * reciprocal -
        (mean * mean) * reciprocal
  refine Q'.eqv_trans _
    (HalfPow.half *
      (((partition * diagonal + partition * diagonal) +
        -(mean * mean + mean * mean)) * reciprocal)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.mul_eqv_congr_right _ _ reciprocal hgenericPhysical)
  exact half_twice_difference_mul_eqv
    (partition * diagonal) (mean * mean) reciprocal

/-- Exact finite Pythagorean identity for the selected physical row. -/
theorem finePacketGlobalPhysicalConnectedProductionRefreshForm_eqv_centered_add_bias
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalPhysicalConnectedProductionRefreshForm
        S hfineCutoff hcoarseCoupling M ≈
      finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
          S hfineCutoff hcoarseCoupling M +
        finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
          S hfineCutoff hcoarseCoupling M := by
  let pairwise := HalfPow.half *
    Q'.divPos
      (finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass
        S hfineCutoff hcoarseCoupling M)
      (S.fine.physicalPartition * S.fine.physicalPartition)
      (finePhysicalPartitionSquare_pos S)
  let raw := finePacketGlobalPhysicalConnectedProductionRefreshForm
    S hfineCutoff hcoarseCoupling M
  let centered :=
    finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
      S hfineCutoff hcoarseCoupling M
  let bias := finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
    S hfineCutoff hcoarseCoupling M
  have hpairRaw : pairwise ≈ raw - bias :=
    finePacketPhysicalConnectedProductionRefreshHalfPairwise_eqv_form_sub_bias
      S hfineCutoff hcoarseCoupling M
  have hpairPosterior : pairwise ≈
      finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
        (physicalKernel S hfineCutoff hcoarseCoupling)
        hfineCutoff hcoarseCoupling M :=
    finePacketPhysicalConnectedProductionRefreshHalfPairwise_eqv_posterior
      S hfineCutoff hcoarseCoupling M
  have hposteriorCentered :
      finePacketGlobalTiltedGibbsConnectedResponsePosteriorVarianceFraction
          (physicalKernel S hfineCutoff hcoarseCoupling)
          hfineCutoff hcoarseCoupling M ≈ centered :=
    finePacketGlobalPhysicalConnectedPosteriorVariance_eqv_centeredProductionRefreshForm
      S hfineCutoff hcoarseCoupling M
  have hsub : raw - bias ≈ centered :=
    Q'.eqv_trans _ pairwise _ (Q'.eqv_symm hpairRaw)
      (Q'.eqv_trans _ _ _ hpairPosterior hposteriorCentered)
  refine Q'.eqv_trans _ ((raw - bias) + bias) _ ?_ ?_
  · refine Q'.eqv_trans _ (bias + (raw - bias)) _ ?_ ?_
    · exact Q'.add_sub_cancel_eqv raw bias
    exact Q'.add_comm_eqv bias (raw - bias)
  exact Q'.add_eqv_congr' hsub (Q'.eqv_refl _)

/-- The bias fraction is literally the square of the normalized row mean. -/
theorem finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction_eqv_mean_square
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
        S hfineCutoff hcoarseCoupling M ≈
      finePacketPhysicalConnectedProductionRefreshMean
          S hfineCutoff hcoarseCoupling M *
        finePacketPhysicalConnectedProductionRefreshMean
          S hfineCutoff hcoarseCoupling M := by
  let meanMass := finePacketPhysicalConnectedProductionRefreshMeanMass
    S hfineCutoff hcoarseCoupling M
  let mean := finePacketPhysicalConnectedProductionRefreshMean
    S hfineCutoff hcoarseCoupling M
  let partition := S.fine.physicalPartition
  let denominator := partition * partition
  let reciprocal := Q'.recipPos denominator
    (finePhysicalPartitionSquare_pos S)
  have hmeanMass : meanMass ≈ partition * mean :=
    finePacketPhysicalConnectedProductionRefreshMeanMass_eqv_partition_mul_mean
      S hfineCutoff hcoarseCoupling M
  have hdenominator : denominator * reciprocal ≈ 1 :=
    Q'.mul_recipPos_eqv denominator (finePhysicalPartitionSquare_pos S)
  unfold finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
    Q'.divPos
  change (meanMass * meanMass) * reciprocal ≈ mean * mean
  refine Q'.eqv_trans _
    ((partition * mean) * (partition * mean) * reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal
      (mul_eqv_both_local hmeanMass hmeanMass)
  refine Q'.eqv_trans _ ((mean * mean) * denominator * reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal
      (paired_square_swap_local partition mean)
  refine Q'.eqv_trans _ ((mean * mean) * (denominator * reciprocal)) _
    (Q'.mul_assoc_eqv (mean * mean) denominator reciprocal) ?_
  refine Q'.eqv_trans _ ((mean * mean) * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (mean * mean) _ _ hdenominator
  exact Q'.mul_one_eqv (mean * mean)

/-- The same bias is the square of the exact connected cylinder remainder. -/
theorem finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction_eqv_remainder_square
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
        S hfineCutoff hcoarseCoupling M ≈
      centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M *
        centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  refine Q'.eqv_trans _
    (finePacketPhysicalConnectedProductionRefreshMean
          S hfineCutoff hcoarseCoupling M *
      finePacketPhysicalConnectedProductionRefreshMean
          S hfineCutoff hcoarseCoupling M) _
    (finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction_eqv_mean_square
      S hfineCutoff hcoarseCoupling M) ?_
  exact mul_eqv_both_local
    (finePacketPhysicalConnectedProductionRefreshMean_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M)
    (finePacketPhysicalConnectedProductionRefreshMean_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M)

/-! ## 4. Honest strong-endpoint consequence -/

/-- At the named SU(2) anchor the only term beyond the strict fluctuation
rate is the exact squared connected blocking bias. -/
theorem finePacketGlobalPhysicalConnectedProductionRefreshForm_le_anchorRate_add_remainderSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half) :
    finePacketGlobalPhysicalConnectedProductionRefreshForm
        S hfineCutoff hcoarseCoupling M ≤
      finePacketAnchorVacuumPacketStrictRate +
        centeredCylinderRemainder
            (physicalKernel S hfineCutoff hcoarseCoupling) M *
          centeredCylinderRemainder
            (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  let centered :=
    finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm
      S hfineCutoff hcoarseCoupling M
  let bias := finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
    S hfineCutoff hcoarseCoupling M
  have hdecomposition :
      finePacketGlobalPhysicalConnectedProductionRefreshForm
          S hfineCutoff hcoarseCoupling M ≈ centered + bias :=
    finePacketGlobalPhysicalConnectedProductionRefreshForm_eqv_centered_add_bias
      S hfineCutoff hcoarseCoupling M
  have hcentered : centered ≤ finePacketAnchorVacuumPacketStrictRate :=
    finePacketGlobalPhysicalConnectedCenteredProductionRefreshForm_le_anchorRate
      S hfineCutoff hcoarseCoupling M cutoff half hfine
  have hsum : centered + bias ≤ finePacketAnchorVacuumPacketStrictRate + bias :=
    Q'.add_le_add hcentered (Q'.le_refl' bias)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomposition)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_left finePacketAnchorVacuumPacketStrictRate _ _
          (finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction_eqv_remainder_square
            S hfineCutoff hcoarseCoupling M))))

/-! ## Axiom audit -/

#print axioms finePacketPhysicalConnectedProductionRefreshMeanMass
#print axioms finePacketGlobalPhysicalConnectedProductionRefreshForm
#print axioms finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction
#print axioms finePacketPhysicalConnectedProductionRefreshMeanMass_eqv_partition_mul_mean
#print axioms finePacketPhysicalConnectedProductionRefreshMean_eqv_centeredRemainder
#print axioms finePacketPhysicalConnectedProductionRefreshPairwiseVarianceMass_eqv_response
#print axioms finePacketPhysicalConnectedProductionRefreshHalfPairwise_eqv_posterior
#print axioms finePacketPhysicalConnectedProductionRefreshHalfPairwise_eqv_form_sub_bias
#print axioms finePacketGlobalPhysicalConnectedProductionRefreshForm_eqv_centered_add_bias
#print axioms finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction_eqv_mean_square
#print axioms finePacketGlobalPhysicalConnectedProductionRefreshBiasFraction_eqv_remainder_square
#print axioms finePacketGlobalPhysicalConnectedProductionRefreshForm_le_anchorRate_add_remainderSquare

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableProductionRefreshBiasVariance
