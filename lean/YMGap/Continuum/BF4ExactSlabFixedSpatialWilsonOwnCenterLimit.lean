/-
# The finite OWN center reaches the SAME completed centered response

The odd-window mean is exactly the lower endpoint mean at lag one. Boundary
forgetting compares every lag mean with the original zero-window singleton;
its joint cutoff/time modulus and a geometric cutoff give a computed late
threshold. Both the moving OWN mean and each endpoint mean therefore approach
the SAME singleton limit. Expanding the centered product before taking limits
identifies its limit with the existing completed centered Wilson moment.

This pays the moving center in the denominator as well as the numerator.
Nome, width, complete radius-zero expression and lag remain fixed. No signed
relative estimate, changing family, physical spacing calibration or continuum
survival is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit
import YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse
import YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement
import YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
  (originalWindowScalar originalWindowScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (middleRatio_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit (raw_original_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit chart)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm intrinsicForm_chart commonForm)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse
  (centeredTimeMoment_chronological_pin)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (joint_congr equiv_sub)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
  (shift shift_zero source_shift)
open YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws
  (mirror_shift_timeZero timeZero_shift_within)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state lagMomentAt time_pairing_lag)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence (windowRatio_padded_congr)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

section Expression

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat} (e : WindowExpression width) (he : Within 0 e)

local notation "f" => sourcePolynomial e
local notation "Mean" => originalJointLimit hw0 hw1 0
  e he

attribute [local irreducible] baseLinks originalWindowScalar originalJointLimit
  middleRatio windowRatio rawPair centeredPair mixRate intrinsicForm

def expressionEndpointMean (stage n L : Nat) : Q' :=
  windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) n L n f

def expressionOwnMean (stage n : Nat) : Q' :=
  middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) (n+1) n f

include he in
private theorem single_support :
    SupportedQuaternionBlocks (N width) f := by
  simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 e he

include he in
private theorem pair_within (L : Nat) : Within L (.mul e (shift L e)) :=
  ⟨within_mono (Nat.zero_le L) e he, timeZero_shift_within L e he⟩

include he in
/-- The entire fixed radius-zero source is pinned before removing padding. -/
theorem expressionRaw_original_pin (stage n L : Nat) :
    rawPair hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) n L f ≈
      originalWindowScalar hw0 hw1 L (.mul e (shift L e)) stage n n := by
  have hf := single_support e he
  have hsize : N width ≤ (L+1)*(N width) := by
    rw [Nat.succ_mul]
    omega
  have hsupport : SupportedQuaternionBlocks ((L+1)*(N width))
      (polyMul f (liftBoundary (L*(N width)) f)) :=
    supported_polyMul
      (fun a ha => Nat.le_trans (hf a ha) (Nat.mul_le_mul_left 4 hsize))
      (by simpa only [Nat.succ_mul, Nat.add_comm] using lift_supported hf (L*(N width)))
  have hsource : PaddedPolynomialCoeffEqv ((L+1)*(N width))
      (sourcePolynomial (.mul e (shift L e)))
      (polyMul f (liftBoundary (L*(N width)) f)) :=
    (PaddedPolynomialCoeffEqv.refl _ f).mul (source_shift _ L e)
  simpa only [rawPair] using Q'.eqv_trans _ _ _
    (windowRatio_padded_congr hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) n L n hsupport
      (source_supported L (.mul e (shift L e)) (pair_within e he L)) hsource.symm)
    (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L (.mul e (shift L e))
      (pair_within e he L) stage n n))

/-- The SAME completed centered moment has the literal lower-first joint. -/
theorem expressionCenteredTimeMoment_chronological_pin (L : Nat) :
    Equiv (centeredTimeMoment hw0 hw1 L (state e he) (state e he))
      (sub (originalJointLimit hw0 hw1 L (.mul e (shift L e)) (pair_within e he L))
        (mul (intrinsicForm hw0 hw1 (state e he) (unit width))
          (intrinsicForm hw0 hw1 (state e he) (unit width)))) := by
  have horder := joint_congr hw0 hw1 L (.mul (shift L e) e) (.mul e (shift L e))
    ⟨timeZero_shift_within L e he, within_mono (Nat.zero_le L) e he⟩
    (pair_within e he L) (RatPolyCoeffEqv.mul_comm _ _)
  have hlag : Equiv (intrinsicForm hw0 hw1 (state e he)
      (BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance L (state e he)))
      (lagMomentAt hw0 hw1 e he L) := by
    simpa only [BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_zero,
      Nat.zero_add] using time_pairing_lag hw0 hw1 e he 0 L
  have hraw := hlag.trans (by
    simpa only [lagMomentAt, BF4WilsonAllNomeZeroRadiusIncrement.lagExpressionAt] using horder)
  exact equiv_sub hraw
    (Pivot2.mul_congr_right
      (BF4WilsonAllNomeReflectedForm.intrinsicForm_symm hw0 hw1 (unit width) (state e he)))

private theorem two_half_chain (epsilon x y z : Q')
    (hx : x ≤ y+HalfPow.half*epsilon) (hy : y ≤ z+HalfPow.half*epsilon) :
    x ≤ z+epsilon :=
  Q'.le_trans' _ _ _ hx
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half*epsilon) hy)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv z (HalfPow.half*epsilon) (HalfPow.half*epsilon))
        (Q'.add_eqv_congr_left z _ _ (ExpNeg.two_halves epsilon)))))

/-- Arbitrary endpoint lags reach the SAME original singleton. The stage
witness is a max of its existing joint modulus and a geometric cutoff. -/
def expressionEndpointMeanThreshold (epsilon : Q') : Nat :=
  max (jointModulus hw0 hw1 0 e (HalfPow.half*epsilon))
    (geometricCutoff (mixRate hw0 hw1 width)
      (polynomialCap f+polynomialCap f) (HalfPow.half*epsilon))

/-- The threshold is data; only fixed source/nome/width are claimed. -/
theorem expressionEndpointMean_approx (L : Nat) (epsilon : Q')
    (heps : (0 : Q') < epsilon) (k p : Nat)
    (hk : expressionEndpointMeanThreshold hw0 hw1 e epsilon ≤ k)
    (hp : jointModulus hw0 hw1 0 e (HalfPow.half*epsilon) ≤ p) :
    expressionEndpointMean hw0 hw1 e k k L ≤ (Mean).approx p+epsilon ∧
      (Mean).approx p ≤ expressionEndpointMean hw0 hw1 e k k L+epsilon := by
  let delta := HalfPow.half*epsilon
  have hd : (0 : Q') < delta := ExpNeg.half_mul_pos epsilon heps
  let C := polynomialCap f
  let q := mixRate hw0 hw1 width
  let J := jointModulus hw0 hw1 0 e delta
  let G := geometricCutoff q (C+C) delta
  have hkJ : J ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hkG : G ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hgeo : q^k*(C+C) ≤ delta := geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    (Q'.zero_le_add C C (polynomialCap_nonnegative f) (polynomialCap_nonnegative f))
    hd k hkG
  have hmeans := endpoint_mean_lags_commonTail hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) k L 0
    (polynomialInterval (List.length (baseLinks width)) f
      (single_support e he))
  have hupper : expressionEndpointMean hw0 hw1 e k k L ≤
      expressionEndpointMean hw0 hw1 e k k 0+delta :=
    Q'.le_trans' _ _ _ hmeans.1 (Q'.add_le_add_left _ _ _ hgeo)
  have hlower : expressionEndpointMean hw0 hw1 e k k 0 ≤
      expressionEndpointMean hw0 hw1 e k k L+delta :=
    Q'.le_trans' _ _ _ hmeans.2 (Q'.add_le_add_left _ _ _ hgeo)
  have hpin : originalWindowScalar hw0 hw1 0 e k k k ≈
      expressionEndpointMean hw0 hw1 e k k 0 := by
    simpa only [expressionEndpointMean] using
      originalWindowScalar_pin hw0 hw1 0 e he k k k
  have hraw := originalJoint_approx hw0 hw1 0 e he
    delta hd k k p
    (Nat.le_trans (Nat.le_max_right _ _) hkJ)
    (Nat.le_trans (Nat.le_max_left _ _) hkJ) hp
  have hbaseU : expressionEndpointMean hw0 hw1 e k k 0 ≤ (Mean).approx p+delta :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin) hraw.1
  have hbaseL : (Mean).approx p ≤ expressionEndpointMean hw0 hw1 e k k 0+delta :=
    Q'.le_trans' _ _ _ hraw.2
      (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ delta hpin))
  exact ⟨two_half_chain epsilon _ _ _ hupper hbaseU,
    two_half_chain epsilon _ _ _ hbaseL hlower⟩

/-- Legacy convergence is packaged from the named computed threshold. -/
theorem expressionEndpointMean_converges (L : Nat) :
    ConvergesTo (fun k => ofQ' (expressionEndpointMean hw0 hw1 e k k L)) Mean := by
  intro epsilon heps
  exact ⟨expressionEndpointMeanThreshold hw0 hw1 e epsilon, fun k hk =>
    ⟨jointModulus hw0 hw1 0 e (HalfPow.half*epsilon), fun p hp =>
      expressionEndpointMean_approx hw0 hw1 e he L epsilon heps k p hk hp⟩⟩

include he in
private theorem expressionOwnMean_endpoint_one (stage n : Nat) :
    expressionOwnMean hw0 hw1 e stage n ≈ expressionEndpointMean hw0 hw1 e stage n 1 :=
  Q'.eqv_trans _ _ _ (middleRatio_swap hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) (n+1) n f)
    (Q'.eqv_symm (lower_endpoint_mean hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) n 1 (single_support e he)))

/-- The actual odd-window center, not a supplied stationary mean. -/
theorem expressionOwnMean_converges :
    ConvergesTo (fun k => ofQ' (expressionOwnMean hw0 hw1 e k k)) Mean :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun k => ofQ' (expressionEndpointMean hw0 hw1 e k k 1))
    (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (expressionOwnMean_endpoint_one hw0 hw1 e he k k)))
    (expressionEndpointMean_converges hw0 hw1 e he 1)

private theorem mean_pin :
    Equiv (intrinsicForm hw0 hw1 (state e he) (unit width)) Mean := by
  have hchart := intrinsicForm_chart hw0 hw1 (state e he) (unit width) 0
    (Nat.le_refl 0) (Nat.le_refl 0)
  have hcongr := joint_congr hw0 hw1 0
    (.mul (mirror 0 e) .one) e
    ⟨by simpa only [Nat.zero_mul] using mirror_within 0 e, True.intro⟩ he (by
      rw [show mirror 0 e = e by
        simpa only [Nat.mul_zero, Nat.zero_sub, shift_zero] using
          mirror_shift_timeZero 0 0 e he]
      exact RatPolyCoeffEqv.mul_one _)
  exact hchart.trans (by
    simpa only [commonForm, state,
      BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit, chart,
      Nat.zero_sub, shift_zero] using hcongr)

/-- The denominator-side centered pair has the SAME existing centered
moment as its limit. The moving mean is expanded at finite stage first. -/
theorem expressionOwn_centeredPair_converges (L : Nat) :
    ConvergesTo (fun k => ofQ'
      (centeredPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k L f
        (middleRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) (k+1) k f)))
      (centeredTimeMoment hw0 hw1 L (state e he) (state e he)) := by
  let Joint := originalJointLimit hw0 hw1 L (.mul e (shift L e)) (pair_within e he L)
  have hp : ConvergesTo (fun k => ofQ'
      (rawPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k L f)) Joint :=
    TrigAddCReal.convergesTo_congr_seq
      (s := fun k => ofQ' (originalWindowScalar hw0 hw1 L
        (.mul e (shift L e)) k k k))
      (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
        Q'.eqv_symm (expressionRaw_original_pin hw0 hw1 e he k k L)))
      (originalJoint_diagonal_converges hw0 hw1 L
        (.mul e (shift L e)) (pair_within e he L))
  have hc := expressionOwnMean_converges hw0 hw1 e he
  have hm := expressionEndpointMean_converges hw0 hw1 e he L
  have h := TrigAddCReal.convergesTo_add
    (TrigAddCReal.convergesTo_add hp
      (TrigAddCReal.convergesTo_neg
        (convergesTo_mul_general (TrigAddCReal.convergesTo_add hc hc) hm)))
    (convergesTo_mul_general hc hc)
  have hfinite := TrigAddCReal.convergesTo_congr_seq
    (s := fun k => add
      (add (ofQ' (rawPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k L f))
        (neg (mul (add (ofQ' (expressionOwnMean hw0 hw1 e k k))
          (ofQ' (expressionOwnMean hw0 hw1 e k k))) (ofQ' (expressionEndpointMean hw0 hw1 e k k L)))))
      (mul (ofQ' (expressionOwnMean hw0 hw1 e k k)) (ofQ' (expressionOwnMean hw0 hw1 e k k))))
    (t := fun k => ofQ' (centeredPair hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) k L f (expressionOwnMean hw0 hw1 e k k)))
    (hs := h)
    (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (centered_pair_pin hw0 hw1 (headCutoff w+k) width
        (Nat.le_add_right _ _) k L (single_support e he)
        (expressionOwnMean hw0 hw1 e k k))))
  have halgebra : Equiv
      (add (add Joint (neg (mul (add Mean Mean) Mean))) (mul Mean Mean))
      (sub Joint (mul Mean Mean)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun p => poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.add (.var 1) (.var 1)) (.var 1))))
        (.mul (.var 1) (.var 1)))
      (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))) (by decide)
      (fun | 0 => Joint.approx p | _ => (Mean).approx p))
  have hmoment : Equiv (centeredTimeMoment hw0 hw1 L (state e he) (state e he))
      (sub Joint (mul Mean Mean)) :=
    (expressionCenteredTimeMoment_chronological_pin hw0 hw1 e he L).trans
      (equiv_sub (Equiv.refl _) ((Pivot2.mul_congr_left (mean_pin hw0 hw1 e he)).trans
        (Pivot2.mul_congr_right (mean_pin hw0 hw1 e he))))
  exact ArctanTrigConvergesProof.convergesTo_of_equiv hfinite
    (halgebra.trans hmoment.symm)

end Expression

/-- Backward-compatible single fundamental-loop endpoint API. -/
theorem endpointMean_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (loop : SourceLoop width) (L : Nat) :
    ConvergesTo (fun k => ofQ' (windowRatio hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) k L k (sourceCharacter width loop.edges 1)))
      (originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)) := by
  simpa only [expressionEndpointMean, sourcePolynomial, Nat.zero_mul, liftBoundary] using
    expressionEndpointMean_converges hw0 hw1 (.loop 0 loop 1) (Nat.le_refl 0) L

/-- Backward-compatible actual odd-window loop mean API. -/
theorem ownMean_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (loop : SourceLoop width) :
    ConvergesTo (fun k => ofQ' (middleRatio hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) (k+1) k (sourceCharacter width loop.edges 1)))
      (originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)) := by
  simpa only [expressionOwnMean, sourcePolynomial, Nat.zero_mul, liftBoundary] using
    expressionOwnMean_converges hw0 hw1 (.loop 0 loop 1) (Nat.le_refl 0)

/-- Existing loop consumers retain their exact SAME centered moment. -/
theorem own_centeredPair_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width : Nat} (loop : SourceLoop width) (L : Nat) :
    ConvergesTo (fun k => ofQ'
      (centeredPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k L
        (sourceCharacter width loop.edges 1)
        (middleRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) (k+1) k
          (sourceCharacter width loop.edges 1))))
      (centeredTimeMoment hw0 hw1 L (loopState loop) (loopState loop)) := by
  simpa only [expressionOwnMean, sourcePolynomial, Nat.zero_mul, liftBoundary, state, loopState] using
    expressionOwn_centeredPair_converges hw0 hw1 (.loop 0 loop 1) (Nat.le_refl 0) L

#print axioms expressionEndpointMean
#print axioms expressionOwnMean
#print axioms expressionRaw_original_pin
#print axioms expressionCenteredTimeMoment_chronological_pin
#print axioms expressionEndpointMeanThreshold
#print axioms expressionEndpointMean_approx
#print axioms expressionEndpointMean_converges
#print axioms expressionOwnMean_converges
#print axioms expressionOwn_centeredPair_converges
#print axioms endpointMean_converges
#print axioms ownMean_converges
#print axioms own_centeredPair_converges

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
