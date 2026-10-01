/-
# The actual finite centered transfer quadratic reaches the original bond norm

For a supplied single-slice Wilson expression, the moving finite odd-marginal
center is removed by an exact covariance identity. The adjacent product and
BOTH endpoint means use the same one-step window, action and partition.
Their existing fixed-source joint heat/time bounds give a computed rectangular
modulus for the actual normalized transfer quadratic. Its limit is the
zero-lag connected pairing on the EXISTING physical BondCompletion.

Nome and spatial width remain fixed. Single-slice oddVariance is not equated
with the adjacent bond norm. No angular limit, uniform physical scaling,
nonzero continuum excitation, canonical continuum OS root or QFT is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferCovariance
import YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay
import YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression unit chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
  (originalWindowScalar originalWindowScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap (windowRatio_bounds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferCovariance
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws (mirror_shift_timeZero)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd crossOdd_within)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (bondForm)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay (connected connected_source_pin)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
  (polynomialCap polynomialCap_nonnegative)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem connectedStream_converges {a b c : Nat → Q'} {A B C : CReal}
    (ha : ConvergesTo (fun s => ofQ' (a s)) A)
    (hb : ConvergesTo (fun s => ofQ' (b s)) B)
    (hc : ConvergesTo (fun s => ofQ' (c s)) C) :
    ConvergesTo (fun s => ofQ' (a s+-(b s*c s))) (CReal.sub A (CReal.mul B C)) := by
  have hm := Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hb hc
  have hs := TrigAddCReal.convergesTo_add ha (TrigAddCReal.convergesTo_neg hm)
  exact TrigAddCReal.convergesTo_congr_seq
    (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)) hs

/-- Radius-zero support is explicit input data; no multitime source is
silently presented as a one-slice observable. -/
def singleSlice {width : Nat} (e : WindowExpression width) (he : Within 0 e) :
    IntrinsicExpression width := ⟨0,e,he⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (e : WindowExpression width) (he : Within 0 e)

local notation "x" => singleSlice e he
local notation "u" => unit width
local notation "pairSource" => crossOdd x x
local notation "upperSource" => crossOdd x u
local notation "lowerSource" => crossOdd u x
local notation "W" k:arg t:arg p:arg =>
  windowRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) t 1 t p
local notation "J" k:arg t:arg f:arg => originalWindowScalar hw0 hw1 1 f k t t

attribute [local irreducible] originalWindowScalar windowRatio baseLinks

private theorem pair_shape : pairSource = .mul (shift 1 e) e := by
  change WindowExpression.mul (mirror 1 (shift 1 e)) (shift 0 e) =
    WindowExpression.mul (shift 1 e) e
  rw [mirror_shift_timeZero 1 1 e he, shift_zero]

private theorem upper_shape : upperSource = .mul (shift 1 e) .one := by
  change WindowExpression.mul (mirror 1 (shift 1 e)) .one =
    WindowExpression.mul (shift 1 e) .one
  rw [mirror_shift_timeZero 1 1 e he]

private theorem lower_shape : lowerSource = .mul .one e := by
  change WindowExpression.mul .one (shift 0 e) = WindowExpression.mul .one e
  rw [shift_zero]

private theorem within_pair : Within 1 pairSource := crossOdd_within x x
private theorem within_upper : Within 1 upperSource := crossOdd_within x u
private theorem within_lower : Within 1 lowerSource := crossOdd_within u x

include he in
private theorem single_support : SupportedQuaternionBlocks (N width) (sourcePolynomial e) := by
  simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 e he

private theorem pair_window_pin (k t : Nat) :
    W k t (polyMul (sourcePolynomial e) (liftBoundary (N width) (sourcePolynomial e))) ≈
      J k t pairSource := by
  have hf := single_support e he
  have hff : SupportedQuaternionBlocks ((1+1)*(N width))
      (polyMul (sourcePolynomial e) (liftBoundary (N width) (sourcePolynomial e))) := by
    apply supported_polyMul
    · intro a ha; exact Nat.le_trans (hf a ha) (by omega)
    · simpa only [show (1 : Nat)+1=2 by rfl, Nat.two_mul] using lift_supported hf (N width)
  have hsource : PaddedPolynomialCoeffEqv ((1+1)*(N width))
      (sourcePolynomial pairSource)
      (polyMul (sourcePolynomial e) (liftBoundary (N width) (sourcePolynomial e))) := by
    rw [pair_shape e he]
    change PaddedPolynomialCoeffEqv _
      (polyMul (sourcePolynomial (shift 1 e)) (sourcePolynomial e)) _
    have hl : PaddedPolynomialCoeffEqv ((1+1)*(N width))
        (sourcePolynomial (shift 1 e)) (liftBoundary (N width) (sourcePolynomial e)) := by
      simpa only [Nat.one_mul] using source_shift ((1+1)*(N width)) 1 e
    exact (hl.mul
      (PaddedPolynomialCoeffEqv.refl _ _)).trans
        (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_comm _ _))
  exact Q'.eqv_trans _ _ _
    (windowRatio_padded_congr hw0 hw1 _ width _ t 1 t hff
      (source_supported 1 pairSource (within_pair e he)) hsource.symm)
    (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 1 pairSource (within_pair e he) k t t))

private theorem upper_window_pin (k t : Nat) :
    W k t (liftBoundary (N width) (sourcePolynomial e)) ≈ J k t upperSource := by
  have hf := single_support e he
  have hsupport : SupportedQuaternionBlocks ((1+1)*(N width))
      (liftBoundary (N width) (sourcePolynomial e)) := by
    simpa only [show (1 : Nat)+1=2 by rfl, Nat.two_mul] using lift_supported hf (N width)
  have hsource : PaddedPolynomialCoeffEqv ((1+1)*(N width))
      (sourcePolynomial upperSource) (liftBoundary (N width) (sourcePolynomial e)) := by
    rw [upper_shape e he]
    change PaddedPolynomialCoeffEqv _ (polyMul (sourcePolynomial (shift 1 e)) polyOne) _
    exact (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_one _)).trans
      (by simpa only [Nat.one_mul] using source_shift ((1+1)*(N width)) 1 e)
  exact Q'.eqv_trans _ _ _
    (windowRatio_padded_congr hw0 hw1 _ width _ t 1 t hsupport
      (source_supported 1 upperSource (within_upper e he)) hsource.symm)
    (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 1 upperSource (within_upper e he) k t t))

private theorem lower_window_pin (k t : Nat) :
    W k t (sourcePolynomial e) ≈ J k t lowerSource := by
  have hc : RatPolyCoeffEqv (sourcePolynomial lowerSource) (sourcePolynomial e) := by
    rw [lower_shape e he]
    exact RatPolyCoeffEqv.one_mul _
  exact Q'.eqv_trans _ _ _
    (YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws.windowRatio_congr
      hw0 hw1 _ width _ t 1 t hc.symm)
    (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 1 lowerSource (within_lower e he) k t t))

/-- The original finite covariance uses ONE common chart and partition. -/
def connectedScalar (k t : Nat) : Q' :=
  J k t pairSource + -(J k t upperSource * J k t lowerSource)

/-- Actual finite centered transfer quadratic; cutoff and exterior-time depth
are independent regulators, while e, nome and width are fixed. -/
def finiteScalar (k t : Nat) : Q' :=
  normalizedCenteredTransferQuadratic hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) t (sourcePolynomial e)

/-- The moving finite mean is removed exactly, not replaced by its limit. -/
theorem finiteScalar_connected_pin (k t : Nat) :
    finiteScalar hw0 hw1 e k t ≈ connectedScalar hw0 hw1 e he k t := by
  have h := normalizedCenteredTransferQuadratic_covariance hw0 hw1 (headCutoff w+k)
    width (Nat.le_add_right _ _) t (single_support e he)
  have hm : W k t (sourcePolynomial e) * W k t (liftBoundary (N width) (sourcePolynomial e)) ≈
      J k t upperSource * J k t lowerSource :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (upper_window_pin hw0 hw1 e he k t))
        (Q'.mul_eqv_congr_left _ _ _ (lower_window_pin hw0 hw1 e he k t)))
  exact Q'.eqv_trans _ _ _ h
    (Q'.add_eqv_congr' (pair_window_pin hw0 hw1 e he k t) (Q'.neg_eqv_congr _ _ hm))

private def meanCap : Q' := Q'.max' 1
  (Q'.max' (polynomialCap (sourcePolynomial upperSource))
    (polynomialCap (sourcePolynomial lowerSource)))

private theorem meanCap_positive : (0 : Q') < meanCap e he :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (Q'.le_max'_left _ _)

private theorem original_abs_bound (f : WindowExpression width) (hf : Within 1 f) (k t : Nat) :
    Q'.abs (J k t f) ≤ polynomialCap (sourcePolynomial f) := by
  have hb := windowRatio_bounds hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _)
    t 1 t (sourcePolynomial f) (source_supported 1 f hf)
  have hp := originalWindowScalar_pin hw0 hw1 1 f hf k t t
  exact Q'.abs_le
    (Q'.le_trans' _ _ _ hb.1 (Q'.ge_of_eqv hp))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hb.2)

private theorem upper_abs (k t : Nat) : Q'.abs (J k t upperSource) ≤ meanCap e he :=
  Q'.le_trans' _ _ _ (original_abs_bound hw0 hw1 upperSource (within_upper e he) k t)
    (Q'.le_trans' _ _ _ (Q'.le_max'_left _ _) (Q'.le_max'_right _ _))

private theorem lower_abs (k t : Nat) : Q'.abs (J k t lowerSource) ≤ meanCap e he :=
  Q'.le_trans' _ _ _ (original_abs_bound hw0 hw1 lowerSource (within_lower e he) k t)
    (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _) (Q'.le_max'_right _ _))

private def errorDenominator : Q' := (1+meanCap e he)+meanCap e he
private theorem errorDenominator_positive : (0 : Q') < errorDenominator e he :=
  Q'.add_pos (Q'.add_pos (by decide) (meanCap_positive e he)) (meanCap_positive e he)

/-- The product error is paid before selecting the three fixed-source moduli. -/
def jointTolerance (epsilon : Q') : Q' :=
  Q'.divPos epsilon (errorDenominator e he) (errorDenominator_positive e he)

private theorem jointTolerance_positive {epsilon : Q'} (hp : (0 : Q') < epsilon) :
    (0 : Q') < jointTolerance e he epsilon := Q'.divPos_pos _ _ _ hp

private theorem tolerance_budget (epsilon : Q') :
    jointTolerance e he epsilon +
      (meanCap e he * jointTolerance e he epsilon + meanCap e he * jointTolerance e he epsilon) ≈
        epsilon := by
  let C := meanCap e he
  let d := jointTolerance e he epsilon
  have h : d+(C*d+C*d) ≈ d*((1+C)+C) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))))
      (.mul (.var 0) (.add (.add (.const 1) (.var 1)) (.var 1)))
      (by decide) (fun | 0 => d | _ => C)
  exact Q'.eqv_trans _ _ _ h (Q'.divPos_mul_eqv _ _ _)

/-- Separate computable heat and exterior-time cutoffs for the SAME covariance. -/
def cutoffThreshold (epsilon : Q') : Nat :=
  max (jointCutoffThreshold hw0 hw1 1 pairSource (jointTolerance e he epsilon))
    (max (jointCutoffThreshold hw0 hw1 1 upperSource (jointTolerance e he epsilon))
      (jointCutoffThreshold hw0 hw1 1 lowerSource (jointTolerance e he epsilon)))

def timeThreshold (epsilon : Q') : Nat :=
  max (jointTimeThreshold hw0 hw1 pairSource (jointTolerance e he epsilon))
    (max (jointTimeThreshold hw0 hw1 upperSource (jointTolerance e he epsilon))
      (jointTimeThreshold hw0 hw1 lowerSource (jointTolerance e he epsilon)))

private theorem covariance_close (epsilon : Q') (hp : (0 : Q') < epsilon)
    (a b c A B C : Q')
    (_hb : Q'.abs b ≤ meanCap e he) (hc : Q'.abs c ≤ meanCap e he)
    (hB : Q'.abs B ≤ meanCap e he) (_hC : Q'.abs C ≤ meanCap e he)
    (ha : a ≤ A+jointTolerance e he epsilon ∧ A ≤ a+jointTolerance e he epsilon)
    (hbb : b ≤ B+jointTolerance e he epsilon ∧ B ≤ b+jointTolerance e he epsilon)
    (hcc : c ≤ C+jointTolerance e he epsilon ∧ C ≤ c+jointTolerance e he epsilon) :
    a+-(b*c) ≤ (A+-(B*C))+epsilon := by
  let d := jointTolerance e he epsilon
  let P := meanCap e he
  have hprod := BoundedRationalCauchyProduct.product_close B b C c P d
    (Q'.le_of_lt (meanCap_positive e he)) (Q'.le_of_lt (jointTolerance_positive e he hp))
    hB hc hbb.symm hcc.symm
  have hs := Q'.add_le_add ha.1 (Q'.neg_le_neg_add hprod)
  have hr : (A+d)+(-(B*C)+(P*d+P*d)) ≈ (A+-(B*C))+(d+(P*d+P*d)) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
      (fun | 0 => A | 1 => d | 2 => -(B*C) | _ => P*d+P*d)
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hr
    (Q'.add_eqv_congr_left _ _ _ (tolerance_budget e he epsilon))))

/-- Independent late cutoff/time rectangles, not an interchange of limits. -/
theorem finiteScalar_rectangle (epsilon : Q') (hp : (0 : Q') < epsilon)
    (k t j s : Nat)
    (hk : cutoffThreshold hw0 hw1 e he epsilon ≤ k)
    (ht : timeThreshold hw0 hw1 e he epsilon ≤ t)
    (hj : cutoffThreshold hw0 hw1 e he epsilon ≤ j)
    (hs : timeThreshold hw0 hw1 e he epsilon ≤ s) :
    finiteScalar hw0 hw1 e k t ≤ finiteScalar hw0 hw1 e j s+epsilon ∧
      finiteScalar hw0 hw1 e j s ≤ finiteScalar hw0 hw1 e k t+epsilon := by
  have hd := jointTolerance_positive e he hp
  have hpq := originalJoint_rectangle hw0 hw1 1 pairSource (within_pair e he)
    (jointTolerance e he epsilon) hd k t j s
    (Nat.le_trans (Nat.le_max_left _ _) hk) (Nat.le_trans (Nat.le_max_left _ _) ht)
    (Nat.le_trans (Nat.le_max_left _ _) hj) (Nat.le_trans (Nat.le_max_left _ _) hs)
  have hu := originalJoint_rectangle hw0 hw1 1 upperSource (within_upper e he)
    (jointTolerance e he epsilon) hd k t j s
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) ht)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hj)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hs)
  have hl := originalJoint_rectangle hw0 hw1 1 lowerSource (within_lower e he)
    (jointTolerance e he epsilon) hd k t j s
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) ht)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hj)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hs)
  have forward := covariance_close e he epsilon hp _ _ _ _ _ _
    (upper_abs hw0 hw1 e he k t) (lower_abs hw0 hw1 e he k t)
    (upper_abs hw0 hw1 e he j s) (lower_abs hw0 hw1 e he j s) hpq hu hl
  have backward := covariance_close e he epsilon hp _ _ _ _ _ _
    (upper_abs hw0 hw1 e he j s) (lower_abs hw0 hw1 e he j s)
    (upper_abs hw0 hw1 e he k t) (lower_abs hw0 hw1 e he k t) hpq.symm hu.symm hl.symm
  have hkt := finiteScalar_connected_pin hw0 hw1 e he k t
  have hjs := finiteScalar_connected_pin hw0 hw1 e he j s
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hkt)
      (Q'.le_trans' _ _ _ forward (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjs))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hjs)
      (Q'.le_trans' _ _ _ backward (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hkt)))⟩

/-- Type-valued modulus for the actual finite transfer diagonal. -/
def transferCauchy : QCauchy (fun s => finiteScalar hw0 hw1 e s s) where
  M epsilon := max (cutoffThreshold hw0 hw1 e he epsilon) (timeThreshold hw0 hw1 e he epsilon)
  bound := fun epsilon hp i j hi hj => finiteScalar_rectangle hw0 hw1 e he epsilon hp i i j j
    (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_trans (Nat.le_max_right _ _) hi)
    (Nat.le_trans (Nat.le_max_left _ _) hj) (Nat.le_trans (Nat.le_max_right _ _) hj)

def transferLimit : CReal := ofQ'CauchySeq _ (transferCauchy hw0 hw1 e he)

/-- The limit controls the full independent rectangle with an exposed
representative cutoff, not only a diagonal propositional convergence. -/
theorem transferLimit_approx (epsilon : Q') (hp : (0 : Q') < epsilon) (k t p : Nat)
    (hk : cutoffThreshold hw0 hw1 e he epsilon ≤ k)
    (ht : timeThreshold hw0 hw1 e he epsilon ≤ t)
    (hrep : (transferCauchy hw0 hw1 e he).M epsilon ≤ p) :
    finiteScalar hw0 hw1 e k t ≤ (transferLimit hw0 hw1 e he).approx p+epsilon ∧
      (transferLimit hw0 hw1 e he).approx p ≤ finiteScalar hw0 hw1 e k t+epsilon := by
  let c := transferCauchy hw0 hw1 e he
  let s := QMhat _ c p
  have hsp : c.M epsilon ≤ s := Nat.le_trans hrep (self_le_QMhat _ c p)
  exact finiteScalar_rectangle hw0 hw1 e he epsilon hp k t s s hk ht
    (Nat.le_trans (Nat.le_max_left _ _) hsp) (Nat.le_trans (Nat.le_max_right _ _) hsp)

attribute [local irreducible] finiteScalar connectedScalar transferCauchy transferLimit originalJointLimit

private theorem transferLimit_connected :
    Equiv (transferLimit hw0 hw1 e he)
      (CReal.sub (originalJointLimit hw0 hw1 1 pairSource (within_pair e he))
        (CReal.mul (originalJointLimit hw0 hw1 1 upperSource (within_upper e he))
          (originalJointLimit hw0 hw1 1 lowerSource (within_lower e he)))) := by
  have hconnected : ConvergesTo (fun s => ofQ' (connectedScalar hw0 hw1 e he s s))
      (CReal.sub (originalJointLimit hw0 hw1 1 pairSource (within_pair e he))
        (CReal.mul (originalJointLimit hw0 hw1 1 upperSource (within_upper e he))
          (originalJointLimit hw0 hw1 1 lowerSource (within_lower e he)))) := by
    unfold connectedScalar
    exact connectedStream_converges
      (originalJoint_diagonal_converges hw0 hw1 1 pairSource (within_pair e he))
      (originalJoint_diagonal_converges hw0 hw1 1 upperSource (within_upper e he))
      (originalJoint_diagonal_converges hw0 hw1 1 lowerSource (within_lower e he))
  exact Equiv_of_limit_of_equal
    (fun s => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => finiteScalar_connected_pin hw0 hw1 e he s s))
    (by unfold transferLimit; exact convergesTo_ofQ'CauchySeq _ (transferCauchy hw0 hw1 e he)) hconnected

/-- SAME physical carrier, source, vacuum means and adjacent bond norm.
This is not an equality with the single-slice odd marginal variance. -/
theorem transferLimit_completed_pin :
    Quotient.mk crealSetoid (transferLimit hw0 hw1 e he) =
      connected hw0 hw1 0 (ofSource hw0 hw1 x) (ofSource hw0 hw1 x) := by
  rw [connected_source_pin, advance_zero]
  exact Quotient.sound (transferLimit_connected hw0 hw1 e he)

#print axioms singleSlice
#print axioms connectedScalar
#print axioms finiteScalar
#print axioms finiteScalar_connected_pin
#print axioms jointTolerance
#print axioms cutoffThreshold
#print axioms timeThreshold
#print axioms finiteScalar_rectangle
#print axioms transferCauchy
#print axioms transferLimit
#print axioms transferLimit_approx
#print axioms transferLimit_completed_pin

end YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
