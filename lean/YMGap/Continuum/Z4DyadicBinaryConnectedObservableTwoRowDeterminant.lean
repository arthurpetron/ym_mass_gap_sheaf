/-
# Two-row determinant for the rational connected observable

The existing tilted-Gibbs response determinant was stated for Boolean events.
The actual connected remainder is a rational-valued observable.  This file
proves the corresponding generic finite determinant identity, localizes the
two positive source rows, and specializes it to the connected remainder.

The exact symmetric-gradient identity then gives

  `4 * rawCross = rootGradientActiveSum + targetGradientActiveSum`.

Combining this with the sharp gradient envelopes and cancelling the common
positive factor two yields

  `abs (2 * rawCross) <= rootEnvelopeSum + targetEnvelopeSum`.

No normalized response, global source average, posterior variance, dense form
bound, completed gap, thermodynamic limit, continuum theory, or Clay theorem
is asserted here.

Constructive contract: finite rational sums, explicit positive-factor
cancellation, and exact row factorizations only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientEnvelope
import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
import YMGap.Continuum.FusionQuotientCollapse

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableTwoRowDeterminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientEnvelope
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradient
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradientSwap
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair

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

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈
      factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _
    (Q'.mul_add_eqv factor left (-right)) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

private theorem four_mul_eqv_two_mul_two_mul (x : Q') :
    (4 : Q') * x ≈ (2 : Q') * ((2 : Q') * x) := by
  refine Q'.eqv_trans _ (((2 : Q') * (2 : Q')) * x) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ x
      (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv 2 2)
  · exact Q'.mul_assoc_eqv _ _ _

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
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)
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
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_neg_local right items)

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = false → value item ≈ 0) →
      listQSum value items ≈ listQSum value (items.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false → value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

/-! ## 1. Generic rational-observable determinant -/

/-- Unnormalized expectation numerator of a rational observable. -/
def finiteWeightedObservableNumerator {A : Type}
    (weight : A → Q') (states : List A) (observable : A → Q') : Q' :=
  listQSum (fun state => weight state * observable state) states

/-- Denominator-cleared difference of two finite weighted observable means. -/
def finiteWeightedObservableCrossNumerator {A : Type}
    (firstWeight secondWeight : A → Q') (states : List A)
    (observable : A → Q') : Q' :=
  finiteWeightedObservableNumerator firstWeight states observable *
      listQSum secondWeight states -
    finiteWeightedObservableNumerator secondWeight states observable *
      listQSum firstWeight states

def finiteWeightedObservableOrientedPairSum {A : Type}
    (firstWeight secondWeight : A → Q') (states : List A)
    (observable : A → Q') : Q' :=
  listQSum
    (orientedPairDifferenceTerm firstWeight secondWeight observable)
    (cartesian states states)

def finiteWeightedObservableAntisymmetricPairSum {A : Type}
    (firstWeight secondWeight : A → Q') (states : List A)
    (observable : A → Q') : Q' :=
  listQSum
    (antisymmetricPairDifferenceTerm firstWeight secondWeight observable)
    (cartesian states states)

theorem finiteWeightedObservableOrientedPairSum_eqv_crossNumerator
    {A : Type} (firstWeight secondWeight : A → Q')
    (states : List A) (observable : A → Q') :
    finiteWeightedObservableOrientedPairSum
        firstWeight secondWeight states observable ≈
      finiteWeightedObservableCrossNumerator
        firstWeight secondWeight states observable := by
  let leftTerm := fun pair : A × A =>
    (firstWeight pair.1 * observable pair.1) * secondWeight pair.2
  let rightTerm := fun pair : A × A =>
    firstWeight pair.1 * (secondWeight pair.2 * observable pair.2)
  unfold finiteWeightedObservableOrientedPairSum
    finiteWeightedObservableCrossNumerator
    finiteWeightedObservableNumerator
  refine Q'.eqv_trans _
    (listQSum (fun pair => leftTerm pair - rightTerm pair)
      (cartesian states states)) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    unfold orientedPairDifferenceTerm leftTerm rightTerm
    refine Q'.eqv_trans _
      (firstWeight pair.1 *
        (secondWeight pair.2 * observable pair.1 -
          secondWeight pair.2 * observable pair.2)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (mul_sub_expand_local
          (secondWeight pair.2)
          (observable pair.1)
          (observable pair.2))
    refine Q'.eqv_trans _
      (firstWeight pair.1 *
          (secondWeight pair.2 * observable pair.1) -
        firstWeight pair.1 *
          (secondWeight pair.2 * observable pair.2)) _ ?_ ?_
    · exact mul_sub_expand_local _ _ _
    · exact sub_eqv_both_local (by ring_qeqv) (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (listQSum leftTerm (cartesian states states) -
      listQSum rightTerm (cartesian states states)) _ ?_ ?_
  · exact listQSum_sub_local leftTerm rightTerm _
  apply sub_eqv_both_local
  · exact listQSum_cartesian_product
      (fun state => firstWeight state * observable state)
      secondWeight states states
  · refine Q'.eqv_trans _
      (listQSum firstWeight states *
        listQSum
          (fun state => secondWeight state * observable state) states) _ ?_ ?_
    · exact listQSum_cartesian_product firstWeight
        (fun state => secondWeight state * observable state) states states
    · exact Q'.mul_comm_eqv _ _

theorem finiteWeightedObservableAntisymmetricPairSum_eqv_two_crossNumerator
    {A : Type} (firstWeight secondWeight : A → Q')
    (states : List A) (observable : A → Q') :
    finiteWeightedObservableAntisymmetricPairSum
        firstWeight secondWeight states observable ≈
      (2 : Q') *
        finiteWeightedObservableCrossNumerator
          firstWeight secondWeight states observable := by
  refine Q'.eqv_trans _
    ((2 : Q') * finiteWeightedObservableOrientedPairSum
      firstWeight secondWeight states observable) _ ?_ ?_
  · unfold finiteWeightedObservableAntisymmetricPairSum
      finiteWeightedObservableOrientedPairSum
    exact listQSum_antisymmetricPairDifference_eqv_two_oriented
      states firstWeight secondWeight observable
  · exact Q'.mul_eqv_congr_left _ _ _
      (finiteWeightedObservableOrientedPairSum_eqv_crossNumerator
        firstWeight secondWeight states observable)

/-! ## 2. The two positive tilted rows -/

def positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
    (S : SlabScalePair) (source : PositivePhysicalSource S)
    (observable : EdgeLabelling → Q') : Q' :=
  finiteWeightedObservableNumerator
    (positivePhysicalSourceTiltedGibbsFullRawWeight S source)
    S.coarse.physicalLabellings observable

def positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (observable : EdgeLabelling → Q') : Q' :=
  positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
        S first observable *
      positivePhysicalSourceTiltedGibbsRowMass S second -
    positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
        S second observable *
      positivePhysicalSourceTiltedGibbsRowMass S first

private theorem firstRawObservableNumerator_eqv_localized
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (observable : EdgeLabelling → Q') :
    positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
        S first observable ≈
      finiteWeightedObservableNumerator
        (finePacketLocalizedTiltedGibbsRawWeight
          S first.1 first.1 second.1)
        S.coarse.physicalLabellings observable := by
  unfold positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
    finiteWeightedObservableNumerator
  apply listQSum_congr
  intro targetState
  exact Q'.mul_eqv_congr_right _ _ (observable targetState)
    (firstTiltedGibbsRawWeight_eqv_localized
      S first.1 second.1 targetState)

private theorem secondRawObservableNumerator_eqv_localized
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (observable : EdgeLabelling → Q') :
    positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
        S second observable ≈
      finiteWeightedObservableNumerator
        (finePacketLocalizedTiltedGibbsRawWeight
          S second.1 first.1 second.1)
        S.coarse.physicalLabellings observable := by
  unfold positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
    finiteWeightedObservableNumerator
  apply listQSum_congr
  intro targetState
  exact Q'.mul_eqv_congr_right _ _ (observable targetState)
    (secondTiltedGibbsRawWeight_eqv_localized
      S first.1 second.1 targetState)

theorem positivePhysicalTiltedGibbsTwoRowRawObservableCross_eqv_localized
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observable : EdgeLabelling → Q') :
    positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
        S first second observable ≈
      finiteWeightedObservableCrossNumerator
        (finePacketLocalizedTiltedGibbsRawWeight
          S first.1 first.1 second.1)
        (finePacketLocalizedTiltedGibbsRawWeight
          S second.1 first.1 second.1)
        S.coarse.physicalLabellings observable := by
  unfold positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
    finiteWeightedObservableCrossNumerator
  exact sub_eqv_both_local
    (mul_eqv_both_local
      (firstRawObservableNumerator_eqv_localized
        S first second observable)
      (secondTiltedGibbsRowMass_eqv_localizedSum
        S hfineCutoff first second))
    (mul_eqv_both_local
      (secondRawObservableNumerator_eqv_localized
        S first second observable)
      (firstTiltedGibbsRowMass_eqv_localizedSum
        S hfineCutoff first second))

/-! ## 3. Localize the rational observable without splitting it -/

theorem localizedTiltedWeightDeterminant_eqv_factored
    (S : SlabScalePair) (first second x y : EdgeLabelling) :
    finePacketLocalizedTiltedGibbsRawWeight S first first second x *
          finePacketLocalizedTiltedGibbsRawWeight S second first second y -
        finePacketLocalizedTiltedGibbsRawWeight S second first second x *
          finePacketLocalizedTiltedGibbsRawWeight S first first second y ≈
      (finePacketCommonExteriorGibbsWeight S first second x *
          finePacketCommonExteriorGibbsWeight S first second y) *
        (finePacketDisagreementTilt S first first second x *
            finePacketDisagreementTilt S second first second y -
          finePacketDisagreementTilt S second first second x *
            finePacketDisagreementTilt S first first second y) := by
  let bx := finePacketCommonExteriorGibbsWeight S first second x
  let by' := finePacketCommonExteriorGibbsWeight S first second y
  let d1x := finePacketDisagreementTilt S first first second x
  let d2x := finePacketDisagreementTilt S second first second x
  let d1y := finePacketDisagreementTilt S first first second y
  let d2y := finePacketDisagreementTilt S second first second y
  refine Q'.eqv_trans _
    ((bx * d1x) * (by' * d2y) -
      (bx * d2x) * (by' * d1y)) _ ?_ ?_
  · exact sub_eqv_both_local
      (mul_eqv_both_local
        (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
          S first first second x)
        (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
          S second first second y))
      (mul_eqv_both_local
        (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
          S second first second x)
        (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
          S first first second y))
  refine Q'.eqv_trans _
    ((bx * by') * (d1x * d2y) -
      (bx * by') * (d2x * d1y)) _ ?_ ?_
  · exact sub_eqv_both_local (by ring_qeqv) (by ring_qeqv)
  · exact Q'.eqv_symm
      (mul_sub_expand_local
        (bx * by') (d1x * d2y) (d2x * d1y))

theorem localizedAntisymmetricConnectedObservableTerm_eqv_factored
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    antisymmetricPairDifferenceTerm
        (finePacketLocalizedTiltedGibbsRawWeight S first first second)
        (finePacketLocalizedTiltedGibbsRawWeight S second first second)
        (connectedRemainderObservable K M) pair ≈
      finePacketLocalizedConnectedObservableAntisymmetricPairTerm
        K M first second pair := by
  unfold antisymmetricPairDifferenceTerm
    finePacketLocalizedConnectedObservableAntisymmetricPairTerm
  refine Q'.eqv_trans _
    (((finePacketCommonExteriorGibbsWeight S first second pair.1 *
          finePacketCommonExteriorGibbsWeight S first second pair.2) *
        (finePacketDisagreementTilt S first first second pair.1 *
            finePacketDisagreementTilt S second first second pair.2 -
          finePacketDisagreementTilt S second first second pair.1 *
            finePacketDisagreementTilt S first first second pair.2)) *
      (connectedRemainderObservable K M pair.1 -
        connectedRemainderObservable K M pair.2)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (localizedTiltedWeightDeterminant_eqv_factored
        S first second pair.1 pair.2)
  · exact Q'.mul_assoc_eqv _ _ _

theorem two_mul_positivePhysicalTiltedGibbsConnectedRawCross_eqv_localizedPairSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (M : SlabFaceBlockMap S) (first second : PositivePhysicalSource S) :
    (2 : Q') *
        positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
          S first second (connectedRemainderObservable K M) ≈
      listQSum
        (finePacketLocalizedConnectedObservableAntisymmetricPairTerm
          K M first.1 second.1)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) := by
  let firstWeight := finePacketLocalizedTiltedGibbsRawWeight
    S first.1 first.1 second.1
  let secondWeight := finePacketLocalizedTiltedGibbsRawWeight
    S second.1 first.1 second.1
  let observable := connectedRemainderObservable K M
  refine Q'.eqv_trans _
    ((2 : Q') * finiteWeightedObservableCrossNumerator
      firstWeight secondWeight S.coarse.physicalLabellings observable) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (positivePhysicalTiltedGibbsTwoRowRawObservableCross_eqv_localized
        S hfineCutoff first second observable)
  refine Q'.eqv_trans _
    (finiteWeightedObservableAntisymmetricPairSum
      firstWeight secondWeight S.coarse.physicalLabellings observable) _ ?_ ?_
  · exact Q'.eqv_symm
      (finiteWeightedObservableAntisymmetricPairSum_eqv_two_crossNumerator
        firstWeight secondWeight S.coarse.physicalLabellings observable)
  unfold finiteWeightedObservableAntisymmetricPairSum
  apply listQSum_congr
  intro pair
  exact localizedAntisymmetricConnectedObservableTerm_eqv_factored
    K M first.1 second.1 pair

/-! ## 4. Prune the two gradient terms to their active carriers -/

private theorem localizedConnectedRootGradientPairTerm_eqv_zero_of_inactive
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hinactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB M.coarseRoot) pair = false) :
    finePacketLocalizedConnectedRootGradientPairTerm
        K M first second pair ≈ 0 := by
  unfold finePacketLocalizedConnectedRootGradientPairTerm
  refine Q'.eqv_trans _
    (0 * connectedRemainderRootDoubledSymmetricGradient
      K M pair.1 pair.2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (finePacketLocalizedAntisymmetricResponsePairTerm_eqv_zero_of_inactive
        S first second (slabPhysicalFacePositiveB M.coarseRoot)
          pair hinactive)
  · exact Q'.zero_mul_eqv _

private theorem localizedConnectedTargetGradientPairTerm_eqv_zero_of_inactive
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hinactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB M.coarseTarget) pair = false) :
    finePacketLocalizedConnectedTargetGradientPairTerm
        K M first second pair ≈ 0 := by
  unfold finePacketLocalizedConnectedTargetGradientPairTerm
  refine Q'.eqv_trans _
    (0 * connectedRemainderTargetDoubledSymmetricGradient
      K M pair.1 pair.2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (finePacketLocalizedAntisymmetricResponsePairTerm_eqv_zero_of_inactive
        S first second (slabPhysicalFacePositiveB M.coarseTarget)
          pair hinactive)
  · exact Q'.zero_mul_eqv _

theorem connectedRootGradientFullPairSum_eqv_active
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    listQSum
        (finePacketLocalizedConnectedRootGradientPairTerm K M first second)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) ≈
      listQSum
        (finePacketLocalizedConnectedRootGradientPairTerm K M first second)
        (finePacketLocalizedResponseActivePairs S first second
          (slabPhysicalFacePositiveB M.coarseRoot)) := by
  unfold finePacketLocalizedResponseActivePairs
  exact listQSum_eq_filter_of_zero_local
    (finePacketLocalizedConnectedRootGradientPairTerm K M first second)
    (finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB M.coarseRoot))
    (cartesian S.coarse.physicalLabellings S.coarse.physicalLabellings)
    (fun pair _ hinactive =>
      localizedConnectedRootGradientPairTerm_eqv_zero_of_inactive
        K M first second pair hinactive)

theorem connectedTargetGradientFullPairSum_eqv_active
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    listQSum
        (finePacketLocalizedConnectedTargetGradientPairTerm K M first second)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) ≈
      listQSum
        (finePacketLocalizedConnectedTargetGradientPairTerm K M first second)
        (finePacketLocalizedResponseActivePairs S first second
          (slabPhysicalFacePositiveB M.coarseTarget)) := by
  unfold finePacketLocalizedResponseActivePairs
  exact listQSum_eq_filter_of_zero_local
    (finePacketLocalizedConnectedTargetGradientPairTerm K M first second)
    (finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB M.coarseTarget))
    (cartesian S.coarse.physicalLabellings S.coarse.physicalLabellings)
    (fun pair _ hinactive =>
      localizedConnectedTargetGradientPairTerm_eqv_zero_of_inactive
        K M first second pair hinactive)

/-! ## 5. Exact connected cross and the lossless envelope bound -/

theorem four_mul_positivePhysicalTiltedGibbsConnectedRawCross_eqv_gradientActiveSums
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (M : SlabFaceBlockMap S) (first second : PositivePhysicalSource S) :
    (4 : Q') *
        positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
          S first second (connectedRemainderObservable K M) ≈
      listQSum
          (finePacketLocalizedConnectedRootGradientPairTerm
            K M first.1 second.1)
          (finePacketLocalizedResponseActivePairs S first.1 second.1
            (slabPhysicalFacePositiveB M.coarseRoot)) +
        listQSum
          (finePacketLocalizedConnectedTargetGradientPairTerm
            K M first.1 second.1)
          (finePacketLocalizedResponseActivePairs S first.1 second.1
            (slabPhysicalFacePositiveB M.coarseTarget)) := by
  let cross := positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
    S first second (connectedRemainderObservable K M)
  let localTerm := finePacketLocalizedConnectedObservableAntisymmetricPairTerm
    K M first.1 second.1
  let pairs := cartesian S.coarse.physicalLabellings
    S.coarse.physicalLabellings
  let rootTerm := finePacketLocalizedConnectedRootGradientPairTerm
    K M first.1 second.1
  let targetTerm := finePacketLocalizedConnectedTargetGradientPairTerm
    K M first.1 second.1
  refine Q'.eqv_trans _ ((2 : Q') * ((2 : Q') * cross)) _ ?_ ?_
  · exact four_mul_eqv_two_mul_two_mul cross
  refine Q'.eqv_trans _ ((2 : Q') * listQSum localTerm pairs) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (two_mul_positivePhysicalTiltedGibbsConnectedRawCross_eqv_localizedPairSum
        K hfineCutoff M first second)
  refine Q'.eqv_trans _
    (listQSum (fun pair => (2 : Q') * localTerm pair) pairs) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_mul_left (2 : Q') localTerm pairs)
  refine Q'.eqv_trans _
    (listQSum (fun pair => rootTerm pair + targetTerm pair) pairs) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact two_mul_localizedConnectedObservablePairTerm_eqv_gradients
      K M first.1 second.1 pair
  refine Q'.eqv_trans _
    (listQSum rootTerm pairs + listQSum targetTerm pairs) _ ?_ ?_
  · exact listQSum_add rootTerm targetTerm pairs
  exact Q'.add_eqv_congr'
    (connectedRootGradientFullPairSum_eqv_active
      K M first.1 second.1)
    (connectedTargetGradientFullPairSum_eqv_active
      K M first.1 second.1)

theorem two_mul_positivePhysicalTiltedGibbsConnectedRawCross_abs_le_envelopeSums
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (M : SlabFaceBlockMap S) (first second : PositivePhysicalSource S) :
    Q'.abs
        ((2 : Q') *
          positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
            S first second (connectedRemainderObservable K M)) ≤
      listQSum
          (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
          (finePacketFaceResponseConnectedActivePairs
            S first.1 second.1 M.coarseRoot) +
        listQSum
          (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
          (finePacketFaceResponseConnectedActivePairs
            S first.1 second.1 M.coarseTarget) := by
  let cross := positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
    S first second (connectedRemainderObservable K M)
  let envelope :=
    listQSum
        (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
        (finePacketFaceResponseConnectedActivePairs
          S first.1 second.1 M.coarseRoot) +
      listQSum
        (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
        (finePacketFaceResponseConnectedActivePairs
          S first.1 second.1 M.coarseTarget)
  have hfour : Q'.abs ((4 : Q') * cross) ≤ (2 : Q') * envelope :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (abs_eqv_congr
        (four_mul_positivePhysicalTiltedGibbsConnectedRawCross_eqv_gradientActiveSums
          K hfineCutoff M first second)))
      (connectedGradientActivePairSums_abs_le_two_envelopeSums
        K M first.1 second.1)
  have hleft : Q'.abs ((4 : Q') * cross) ≈
      (2 : Q') * Q'.abs ((2 : Q') * cross) := by
    refine Q'.eqv_trans _
      (Q'.abs (((2 : Q') * cross) * (2 : Q'))) _ ?_ ?_
    · exact abs_eqv_congr
        (Q'.eqv_trans _ ((2 : Q') * ((2 : Q') * cross)) _
          (four_mul_eqv_two_mul_two_mul cross) (by ring_qeqv))
    refine Q'.eqv_trans _
      (Q'.abs ((2 : Q') * cross) * (2 : Q')) _ ?_ ?_
    · exact YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        ((2 : Q') * cross) (by decide)
    · exact Q'.mul_comm_eqv _ _
  have hscaled :
      (2 : Q') * Q'.abs ((2 : Q') * cross) ≤
        (2 : Q') * envelope :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hfour
  exact Q'.le_of_mul_le_mul_left hscaled (Q'.ofNat_succ_pos 1)

/-! ## 6. Axiom audit -/

#print axioms finiteWeightedObservableNumerator
#print axioms finiteWeightedObservableCrossNumerator
#print axioms finiteWeightedObservableOrientedPairSum_eqv_crossNumerator
#print axioms finiteWeightedObservableAntisymmetricPairSum_eqv_two_crossNumerator
#print axioms positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
#print axioms positivePhysicalTiltedGibbsTwoRowRawObservableCross_eqv_localized
#print axioms localizedTiltedWeightDeterminant_eqv_factored
#print axioms localizedAntisymmetricConnectedObservableTerm_eqv_factored
#print axioms two_mul_positivePhysicalTiltedGibbsConnectedRawCross_eqv_localizedPairSum
#print axioms connectedRootGradientFullPairSum_eqv_active
#print axioms connectedTargetGradientFullPairSum_eqv_active
#print axioms four_mul_positivePhysicalTiltedGibbsConnectedRawCross_eqv_gradientActiveSums
#print axioms two_mul_positivePhysicalTiltedGibbsConnectedRawCross_abs_le_envelopeSums

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableTwoRowDeterminant
