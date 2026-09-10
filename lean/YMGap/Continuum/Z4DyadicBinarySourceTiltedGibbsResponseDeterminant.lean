/-
# Antisymmetric determinant of two localized tilted Gibbs rows

Two normalized tilted rows cannot be compared pointwise before their distinct
partition masses are accounted for.  This file clears those two positive
denominators exactly and rewrites the resulting raw cross on the square of
the common coarse physical carrier.

Antisymmetrization exposes the cancellation needed later: the common exterior
Gibbs factors occur symmetrically, while all source dependence is the finite
determinant of the two packet-disagreement tilts.  The observable enters only
through the difference of its two Boolean indicators.

This is exact finite change-of-measure algebra.  It does not estimate the
pair sum, construct a polymer expansion, prove volume-uniform smallness,
construct a continuum measure, or prove a mass gap.

Constructive contract: finite list sums and exact rational equivalence only;
no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSignedAverage
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt

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

private theorem listQSum_divPos_eqv_divPos_listQSum_local
    {A : Type} (value : A → Q') (denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    ∀ items : List A,
      listQSum
          (fun item => Q'.divPos (value item) denominator hdenominator)
          items ≈
        Q'.divPos (listQSum value items) denominator hdenominator
  | [] => by
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv (Q'.recipPos denominator hdenominator))
  | head :: tail => by
      unfold listQSum
      refine Q'.eqv_trans _
        (Q'.divPos (value head) denominator hdenominator +
          Q'.divPos (listQSum value tail) denominator hdenominator) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (listQSum_divPos_eqv_divPos_listQSum_local
            value denominator hdenominator tail)
      · unfold Q'.divPos
        exact Q'.eqv_symm
          (Q'.add_mul_eqv
            (value head) (listQSum value tail)
            (Q'.recipPos denominator hdenominator))

/-! ## 1. Raw event numerators and denominator clearing -/

/-- Exact rational indicator of a Boolean event. -/
def booleanEventIndicator {A : Type}
    (event : A → Bool) (state : A) : Q' :=
  if event state then 1 else 0

/-- Unnormalized event numerator of a finite rational weight. -/
def finiteWeightedEventNumerator {A : Type}
    (weight : A → Q') (states : List A)
    (event : A → Bool) : Q' :=
  listQSum
    (fun state => weight state * booleanEventIndicator event state)
    states

/-- The full-carrier raw event numerator of one positive tilted row. -/
def positivePhysicalSourceTiltedGibbsFullRawEventNumerator
    (S : SlabScalePair) (source : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) : Q' :=
  finiteWeightedEventNumerator
    (positivePhysicalSourceTiltedGibbsFullRawWeight S source)
    S.coarse.physicalLabellings event

/-- A normalized tilted-row event mass is its full-carrier raw numerator
divided by the original positive row mass. -/
theorem positivePhysicalSourceTiltedGibbsEventMass_eqv_fullRaw_divPos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling source event ≈
      Q'.divPos
        (positivePhysicalSourceTiltedGibbsFullRawEventNumerator
          S source event)
        (positivePhysicalSourceTiltedGibbsRowMass S source)
        (positivePhysicalSourceTiltedGibbsRowMass_pos
          S hfineCutoff hcoarseCoupling source) := by
  let denominator := positivePhysicalSourceTiltedGibbsRowMass S source
  let rawWeight :=
    positivePhysicalSourceTiltedGibbsFullRawWeight S source
  let hdenominator : (0 : Q') < denominator :=
    positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling source
  unfold positivePhysicalSourceTiltedGibbsEventMass
    positivePhysicalSourceTiltedGibbsKernel
  change
    finiteEventMass
        (fun targetState =>
          Q'.divPos (rawWeight targetState) denominator hdenominator)
        S.coarse.physicalLabellings event ≈
      Q'.divPos
        (positivePhysicalSourceTiltedGibbsFullRawEventNumerator
          S source event) denominator hdenominator
  unfold finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun targetState =>
        Q'.divPos
          (if event targetState then
            rawWeight targetState
          else 0)
          denominator hdenominator)
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro targetState
    cases hevent : event targetState with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        unfold Q'.divPos
        exact Q'.eqv_symm
          (Q'.zero_mul_eqv (Q'.recipPos denominator hdenominator))
    | true =>
        simp only [if_true]
        exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (Q'.divPos
      (listQSum
        (fun targetState =>
          if event targetState then rawWeight targetState else 0)
        S.coarse.physicalLabellings)
      denominator hdenominator) _ ?_ ?_
  · exact listQSum_divPos_eqv_divPos_listQSum_local
      (fun targetState =>
        if event targetState then rawWeight targetState else 0)
      denominator hdenominator S.coarse.physicalLabellings
  unfold positivePhysicalSourceTiltedGibbsFullRawEventNumerator
    finiteWeightedEventNumerator booleanEventIndicator
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (listQSum_congr (fun targetState => by
      cases hevent : event targetState with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact Q'.eqv_symm (Q'.mul_zero_eqv (rawWeight targetState))
      | true =>
          simp only [if_true]
          exact Q'.eqv_symm (Q'.mul_one_eqv (rawWeight targetState))) _)

/-- Difference of two positive finite ratios. -/
def twoPositiveRatioResponseDefect
    (firstNumerator secondNumerator firstMass secondMass : Q')
    (hfirstMass : (0 : Q') < firstMass)
    (hsecondMass : (0 : Q') < secondMass) : Q' :=
  Q'.divPos firstNumerator firstMass hfirstMass -
    Q'.divPos secondNumerator secondMass hsecondMass

/-- Denominator-cleared two-row response cross. -/
def twoPositiveRatioResponseCrossNumerator
    (firstNumerator secondNumerator firstMass secondMass : Q') : Q' :=
  firstNumerator * secondMass - secondNumerator * firstMass

/-- Clearing both positive denominators yields the raw cross exactly. -/
theorem twoPositiveRatioResponseDefect_mul_masses_eqv_crossNumerator
    (firstNumerator secondNumerator firstMass secondMass : Q')
    (hfirstMass : (0 : Q') < firstMass)
    (hsecondMass : (0 : Q') < secondMass) :
    twoPositiveRatioResponseDefect
        firstNumerator secondNumerator firstMass secondMass
        hfirstMass hsecondMass *
      (firstMass * secondMass) ≈
    twoPositiveRatioResponseCrossNumerator
      firstNumerator secondNumerator firstMass secondMass := by
  have hfirst :
      Q'.divPos firstNumerator firstMass hfirstMass *
          (firstMass * secondMass) ≈
        firstNumerator * secondMass := by
    refine Q'.eqv_trans _
      ((Q'.divPos firstNumerator firstMass hfirstMass * firstMass) *
        secondMass) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    · exact Q'.mul_eqv_congr_right _ _ secondMass
        (Q'.divPos_mul_eqv firstNumerator firstMass hfirstMass)
  have hsecond :
      Q'.divPos secondNumerator secondMass hsecondMass *
          (firstMass * secondMass) ≈
        secondNumerator * firstMass := by
    refine Q'.eqv_trans _
      ((Q'.divPos secondNumerator secondMass hsecondMass * secondMass) *
        firstMass) _ ?_ ?_
    · ring_qeqv
    · exact Q'.mul_eqv_congr_right _ _ firstMass
        (Q'.divPos_mul_eqv secondNumerator secondMass hsecondMass)
  unfold twoPositiveRatioResponseDefect
    twoPositiveRatioResponseCrossNumerator
  refine Q'.eqv_trans _
    (Q'.divPos firstNumerator firstMass hfirstMass *
        (firstMass * secondMass) -
      Q'.divPos secondNumerator secondMass hsecondMass *
        (firstMass * secondMass)) _ ?_ ?_
  · exact Q'.sub_mul_eqv _ _ _
  · exact sub_eqv_both_local hfirst hsecond

/-- The raw event cross of two positive tilted rows. -/
def positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) : Q' :=
  twoPositiveRatioResponseCrossNumerator
    (positivePhysicalSourceTiltedGibbsFullRawEventNumerator S first event)
    (positivePhysicalSourceTiltedGibbsFullRawEventNumerator S second event)
    (positivePhysicalSourceTiltedGibbsRowMass S first)
    (positivePhysicalSourceTiltedGibbsRowMass S second)

/-- The difference of the two normalized tilted event responses, multiplied
by both positive row masses, is the raw cross numerator. -/
theorem positivePhysicalTiltedGibbsEventResponseDifference_mul_masses_eqv_rawCross
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    (positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling first event -
        positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling second event) *
      (positivePhysicalSourceTiltedGibbsRowMass S first *
        positivePhysicalSourceTiltedGibbsRowMass S second) ≈
    positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
      S first second event := by
  let hfirst := positivePhysicalSourceTiltedGibbsRowMass_pos
    S hfineCutoff hcoarseCoupling first
  let hsecond := positivePhysicalSourceTiltedGibbsRowMass_pos
    S hfineCutoff hcoarseCoupling second
  refine Q'.eqv_trans _
    (twoPositiveRatioResponseDefect
      (positivePhysicalSourceTiltedGibbsFullRawEventNumerator S first event)
      (positivePhysicalSourceTiltedGibbsFullRawEventNumerator S second event)
      (positivePhysicalSourceTiltedGibbsRowMass S first)
      (positivePhysicalSourceTiltedGibbsRowMass S second)
      hfirst hsecond *
      (positivePhysicalSourceTiltedGibbsRowMass S first *
        positivePhysicalSourceTiltedGibbsRowMass S second)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (sub_eqv_both_local
        (positivePhysicalSourceTiltedGibbsEventMass_eqv_fullRaw_divPos
          S hfineCutoff hcoarseCoupling first event)
        (positivePhysicalSourceTiltedGibbsEventMass_eqv_fullRaw_divPos
          S hfineCutoff hcoarseCoupling second event))
  · exact twoPositiveRatioResponseDefect_mul_masses_eqv_crossNumerator
      _ _ _ _ hfirst hsecond

/-! ## 2. A generic square-carrier determinant identity -/

/-- Raw event cross for two weights on one common finite carrier. -/
def finiteWeightedResponseCrossNumerator {A : Type}
    (firstWeight secondWeight : A → Q') (states : List A)
    (event : A → Bool) : Q' :=
  finiteWeightedEventNumerator firstWeight states event *
      listQSum secondWeight states -
    finiteWeightedEventNumerator secondWeight states event *
      listQSum firstWeight states

/-- Oriented square-carrier presentation of the same response cross. -/
def finiteWeightedOrientedResponsePairSum {A : Type}
    (firstWeight secondWeight : A → Q') (states : List A)
    (event : A → Bool) : Q' :=
  listQSum
    (orientedPairDifferenceTerm
      firstWeight secondWeight (booleanEventIndicator event))
    (cartesian states states)

/-- Antisymmetric square-carrier presentation; it equals twice the response
cross and exposes the determinant of the two weights. -/
def finiteWeightedAntisymmetricResponsePairSum {A : Type}
    (firstWeight secondWeight : A → Q') (states : List A)
    (event : A → Bool) : Q' :=
  listQSum
    (antisymmetricPairDifferenceTerm
      firstWeight secondWeight (booleanEventIndicator event))
    (cartesian states states)

/-- The oriented square-carrier sum is exactly the raw event cross. -/
theorem finiteWeightedOrientedResponsePairSum_eqv_crossNumerator
    {A : Type} (firstWeight secondWeight : A → Q')
    (states : List A) (event : A → Bool) :
    finiteWeightedOrientedResponsePairSum
        firstWeight secondWeight states event ≈
      finiteWeightedResponseCrossNumerator
        firstWeight secondWeight states event := by
  let indicator := booleanEventIndicator event
  let leftTerm := fun pair : A × A =>
    (firstWeight pair.1 * indicator pair.1) * secondWeight pair.2
  let rightTerm := fun pair : A × A =>
    firstWeight pair.1 * (secondWeight pair.2 * indicator pair.2)
  unfold finiteWeightedOrientedResponsePairSum
    finiteWeightedResponseCrossNumerator
    finiteWeightedEventNumerator
  refine Q'.eqv_trans _
    (listQSum (fun pair => leftTerm pair - rightTerm pair)
      (cartesian states states)) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    unfold orientedPairDifferenceTerm leftTerm rightTerm indicator
    refine Q'.eqv_trans _
      (firstWeight pair.1 *
        (secondWeight pair.2 * booleanEventIndicator event pair.1 -
          secondWeight pair.2 * booleanEventIndicator event pair.2)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (mul_sub_expand_local
          (secondWeight pair.2)
          (booleanEventIndicator event pair.1)
          (booleanEventIndicator event pair.2))
    refine Q'.eqv_trans _
      (firstWeight pair.1 *
          (secondWeight pair.2 * booleanEventIndicator event pair.1) -
        firstWeight pair.1 *
          (secondWeight pair.2 * booleanEventIndicator event pair.2)) _ ?_ ?_
    · exact mul_sub_expand_local _ _ _
    · exact sub_eqv_both_local (by ring_qeqv) (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (listQSum leftTerm (cartesian states states) -
      listQSum rightTerm (cartesian states states)) _ ?_ ?_
  · exact listQSum_sub_local leftTerm rightTerm _
  apply sub_eqv_both_local
  · exact listQSum_cartesian_product
      (fun state =>
        firstWeight state * booleanEventIndicator event state)
      secondWeight states states
  · refine Q'.eqv_trans _
      (listQSum firstWeight states *
        listQSum
          (fun state =>
            secondWeight state * booleanEventIndicator event state)
          states) _ ?_ ?_
    · exact listQSum_cartesian_product firstWeight
        (fun state =>
          secondWeight state * booleanEventIndicator event state)
        states states
    · exact Q'.mul_comm_eqv _ _

/-- Antisymmetrization doubles the raw event cross on the common carrier. -/
theorem finiteWeightedAntisymmetricResponsePairSum_eqv_two_crossNumerator
    {A : Type} (firstWeight secondWeight : A → Q')
    (states : List A) (event : A → Bool) :
    finiteWeightedAntisymmetricResponsePairSum
        firstWeight secondWeight states event ≈
      (2 : Q') *
        finiteWeightedResponseCrossNumerator
          firstWeight secondWeight states event := by
  refine Q'.eqv_trans _
    ((2 : Q') *
      finiteWeightedOrientedResponsePairSum
        firstWeight secondWeight states event) _ ?_ ?_
  · unfold finiteWeightedAntisymmetricResponsePairSum
      finiteWeightedOrientedResponsePairSum
    exact listQSum_antisymmetricPairDifference_eqv_two_oriented
      states firstWeight secondWeight (booleanEventIndicator event)
  · exact Q'.mul_eqv_congr_left _ _ _
      (finiteWeightedOrientedResponsePairSum_eqv_crossNumerator
        firstWeight secondWeight states event)

/-! ## 3. The packet-local determinant -/

/-- Common exterior multiplicity times the coarse physical Gibbs weight. -/
def finePacketCommonExteriorGibbsWeight
    (S : SlabScalePair) (first second targetState : EdgeLabelling) : Q' :=
  Q'.ofNat
      (finePacketCommonExteriorMultiplicityProduct
        S first second targetState) *
    S.coarse.physicalTerm targetState

/-- Exact integer tilt supported on the packet-disagreement carrier. -/
def finePacketDisagreementTilt
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) : Q' :=
  Q'.ofNat
    (finePacketDisagreementMultiplicityProduct
      S source first second targetState)

/-- One localized row is common exterior Gibbs weight times its local
packet-disagreement tilt. -/
theorem finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    finePacketLocalizedTiltedGibbsRawWeight
        S source first second targetState ≈
      finePacketCommonExteriorGibbsWeight
          S first second targetState *
        finePacketDisagreementTilt
          S source first second targetState := by
  unfold finePacketLocalizedTiltedGibbsRawWeight
    finePacketCommonExteriorGibbsWeight finePacketDisagreementTilt
  ring_qeqv

/-- The antisymmetric localized pair term after the common background has
been factored out. -/
def finePacketLocalizedAntisymmetricResponsePairTerm
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  (finePacketCommonExteriorGibbsWeight S first second pair.1 *
      finePacketCommonExteriorGibbsWeight S first second pair.2) *
    ((finePacketDisagreementTilt S first first second pair.1 *
          finePacketDisagreementTilt S second first second pair.2 -
        finePacketDisagreementTilt S second first second pair.1 *
          finePacketDisagreementTilt S first first second pair.2) *
      (booleanEventIndicator event pair.1 -
        booleanEventIndicator event pair.2))

/-- Pointwise, the complete antisymmetric row determinant contains no
source dependence outside the finite packet-disagreement tilts. -/
private theorem localizedWeightDeterminant_eqv_factored
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
  let backgroundY := finePacketCommonExteriorGibbsWeight S first second y
  let d1x := finePacketDisagreementTilt S first first second x
  let d2x := finePacketDisagreementTilt S second first second x
  let d1y := finePacketDisagreementTilt S first first second y
  let d2y := finePacketDisagreementTilt S second first second y
  refine Q'.eqv_trans _
    ((bx * d1x) * (backgroundY * d2y) -
      (bx * d2x) * (backgroundY * d1y)) _ ?_ ?_
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
    ((bx * backgroundY) * (d1x * d2y) -
      (bx * backgroundY) * (d2x * d1y)) _ ?_ ?_
  · exact sub_eqv_both_local (by ring_qeqv) (by ring_qeqv)
  · exact Q'.eqv_symm
      (mul_sub_expand_local
        (bx * backgroundY) (d1x * d2y) (d2x * d1y))

/-- Pointwise, the complete antisymmetric row determinant contains no
source dependence outside the finite packet-disagreement tilts. -/
theorem localizedAntisymmetricResponsePairTerm_eqv_factored
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool)
    (pair : EdgeLabelling × EdgeLabelling) :
    antisymmetricPairDifferenceTerm
        (finePacketLocalizedTiltedGibbsRawWeight S first first second)
        (finePacketLocalizedTiltedGibbsRawWeight S second first second)
        (booleanEventIndicator event) pair ≈
      finePacketLocalizedAntisymmetricResponsePairTerm
        S first second event pair := by
  unfold antisymmetricPairDifferenceTerm
    finePacketLocalizedAntisymmetricResponsePairTerm
  refine Q'.eqv_trans _
    (((finePacketCommonExteriorGibbsWeight S first second pair.1 *
          finePacketCommonExteriorGibbsWeight S first second pair.2) *
        (finePacketDisagreementTilt S first first second pair.1 *
            finePacketDisagreementTilt S second first second pair.2 -
          finePacketDisagreementTilt S second first second pair.1 *
            finePacketDisagreementTilt S first first second pair.2)) *
      (booleanEventIndicator event pair.1 -
        booleanEventIndicator event pair.2)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (localizedWeightDeterminant_eqv_factored
        S first second pair.1 pair.2)
  · exact Q'.mul_assoc_eqv _ _ _

/-- The actual two-row raw cross is exactly the response cross of the two
localized weights on the one complete physical carrier. -/
private theorem firstFullRawEventNumerator_eqv_localized
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    positivePhysicalSourceTiltedGibbsFullRawEventNumerator
        S first event ≈
      finiteWeightedEventNumerator
        (finePacketLocalizedTiltedGibbsRawWeight
          S first.1 first.1 second.1)
        S.coarse.physicalLabellings event := by
  unfold positivePhysicalSourceTiltedGibbsFullRawEventNumerator
    finiteWeightedEventNumerator
  apply listQSum_congr
  intro targetState
  exact Q'.mul_eqv_congr_right _ _ _
    (firstTiltedGibbsRawWeight_eqv_localized
      S first.1 second.1 targetState)

private theorem secondFullRawEventNumerator_eqv_localized
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    positivePhysicalSourceTiltedGibbsFullRawEventNumerator
        S second event ≈
      finiteWeightedEventNumerator
        (finePacketLocalizedTiltedGibbsRawWeight
          S second.1 first.1 second.1)
        S.coarse.physicalLabellings event := by
  unfold positivePhysicalSourceTiltedGibbsFullRawEventNumerator
    finiteWeightedEventNumerator
  apply listQSum_congr
  intro targetState
  exact Q'.mul_eqv_congr_right _ _ _
    (secondTiltedGibbsRawWeight_eqv_localized
      S first.1 second.1 targetState)

private theorem firstTiltedGibbsRowMass_eqv_localized
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    positivePhysicalSourceTiltedGibbsRowMass S first ≈
      listQSum
        (finePacketLocalizedTiltedGibbsRawWeight
          S first.1 first.1 second.1)
        S.coarse.physicalLabellings := by
  refine Q'.eqv_trans _
    (listQSum
      (positivePhysicalSourceTiltedGibbsFullRawWeight S first)
      S.coarse.physicalLabellings) _
    (positivePhysicalSourceTiltedGibbsRowMass_eqv_fullCarrier
      S hfineCutoff first) ?_
  apply listQSum_congr
  intro targetState
  exact firstTiltedGibbsRawWeight_eqv_localized
    S first.1 second.1 targetState

private theorem secondTiltedGibbsRowMass_eqv_localized
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    positivePhysicalSourceTiltedGibbsRowMass S second ≈
      listQSum
        (finePacketLocalizedTiltedGibbsRawWeight
          S second.1 first.1 second.1)
        S.coarse.physicalLabellings := by
  refine Q'.eqv_trans _
    (listQSum
      (positivePhysicalSourceTiltedGibbsFullRawWeight S second)
      S.coarse.physicalLabellings) _
    (positivePhysicalSourceTiltedGibbsRowMass_eqv_fullCarrier
      S hfineCutoff second) ?_
  apply listQSum_congr
  intro targetState
  exact secondTiltedGibbsRawWeight_eqv_localized
    S first.1 second.1 targetState

theorem positivePhysicalTiltedGibbsTwoRowRawCrossNumerator_eqv_localized
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
        S first second event ≈
      finiteWeightedResponseCrossNumerator
        (finePacketLocalizedTiltedGibbsRawWeight
          S first.1 first.1 second.1)
        (finePacketLocalizedTiltedGibbsRawWeight
          S second.1 first.1 second.1)
        S.coarse.physicalLabellings event := by
  unfold positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
    twoPositiveRatioResponseCrossNumerator
    finiteWeightedResponseCrossNumerator
  exact sub_eqv_both_local
    (mul_eqv_both_local
      (firstFullRawEventNumerator_eqv_localized S first second event)
      (secondTiltedGibbsRowMass_eqv_localized
        S hfineCutoff first second))
    (mul_eqv_both_local
      (secondFullRawEventNumerator_eqv_localized S first second event)
      (firstTiltedGibbsRowMass_eqv_localized
        S hfineCutoff first second))

/-- Final exact cancellation form: twice the normalized-response raw cross
is a square-carrier sum of a common exterior background, the antisymmetric
local disagreement-tilt determinant, and the observable difference. -/
theorem two_mul_positivePhysicalTiltedGibbsRawCross_eqv_localizedPairSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    (2 : Q') *
        positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
          S first second event ≈
      listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm
          S first.1 second.1 event)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) := by
  let firstWeight := finePacketLocalizedTiltedGibbsRawWeight
    S first.1 first.1 second.1
  let secondWeight := finePacketLocalizedTiltedGibbsRawWeight
    S second.1 first.1 second.1
  refine Q'.eqv_trans _
    ((2 : Q') *
      finiteWeightedResponseCrossNumerator
        firstWeight secondWeight S.coarse.physicalLabellings event) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (positivePhysicalTiltedGibbsTwoRowRawCrossNumerator_eqv_localized
        S hfineCutoff first second event)
  refine Q'.eqv_trans _
    (finiteWeightedAntisymmetricResponsePairSum
      firstWeight secondWeight S.coarse.physicalLabellings event) _ ?_ ?_
  · exact Q'.eqv_symm
      (finiteWeightedAntisymmetricResponsePairSum_eqv_two_crossNumerator
        firstWeight secondWeight S.coarse.physicalLabellings event)
  unfold finiteWeightedAntisymmetricResponsePairSum firstWeight secondWeight
  apply listQSum_congr
  intro pair
  exact localizedAntisymmetricResponsePairTerm_eqv_factored
    S first.1 second.1 event pair

/-! ## 4. Axiom audit -/

#print axioms positivePhysicalSourceTiltedGibbsEventMass_eqv_fullRaw_divPos
#print axioms twoPositiveRatioResponseDefect_mul_masses_eqv_crossNumerator
#print axioms positivePhysicalTiltedGibbsEventResponseDifference_mul_masses_eqv_rawCross
#print axioms finiteWeightedOrientedResponsePairSum_eqv_crossNumerator
#print axioms finiteWeightedAntisymmetricResponsePairSum_eqv_two_crossNumerator
#print axioms finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
#print axioms localizedAntisymmetricResponsePairTerm_eqv_factored
#print axioms positivePhysicalTiltedGibbsTwoRowRawCrossNumerator_eqv_localized
#print axioms two_mul_positivePhysicalTiltedGibbsRawCross_eqv_localizedPairSum

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
