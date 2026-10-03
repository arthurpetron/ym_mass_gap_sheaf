/-
# The finite OWN center reaches the SAME completed centered response

The odd-window mean is exactly the lower endpoint mean at lag one. Boundary
forgetting compares every lag mean with the original zero-window singleton;
its joint cutoff/time modulus and a geometric cutoff give a computed late
threshold. Both the moving OWN mean and each endpoint mean therefore approach
the SAME singleton limit. Expanding the centered product before taking limits
identifies its limit with the existing completed centered Wilson moment.

This pays the moving center in the denominator as well as the numerator.
Nome, width, loop and lag remain fixed. No signed relative estimate, changing
family, physical spacing calibration or continuum survival is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit
import YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse

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

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat} (loop : SourceLoop width)

local notation "f" => sourceCharacter width loop.edges 1
local notation "Mean" => originalJointLimit hw0 hw1 0
  (WindowExpression.loop 0 loop 1) (Nat.le_refl 0)

attribute [local irreducible] baseLinks originalWindowScalar originalJointLimit
  middleRatio windowRatio rawPair centeredPair mixRate intrinsicForm

private def endpointMean (stage n L : Nat) : Q' :=
  windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) n L n f

private def ownMean (stage n : Nat) : Q' :=
  middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) (n+1) n f

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
theorem endpointMean_converges (L : Nat) :
    ConvergesTo (fun k => ofQ' (endpointMean hw0 hw1 loop k k L)) Mean := by
  intro epsilon he
  let delta := HalfPow.half*epsilon
  have hd : (0 : Q') < delta := ExpNeg.half_mul_pos epsilon he
  let C := polynomialCap f
  let q := mixRate hw0 hw1 width
  let J := jointModulus hw0 hw1 0 (.loop 0 loop 1) delta
  let G := geometricCutoff q (C+C) delta
  refine ⟨max J G, fun k hk => ⟨J, fun p hp => ?_⟩⟩
  have hkJ : J ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hkG : G ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hgeo : q^k*(C+C) ≤ delta := geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    (Q'.zero_le_add C C (polynomialCap_nonnegative f) (polynomialCap_nonnegative f))
    hd k hkG
  have hmeans := endpoint_mean_lags_commonTail hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) k L 0
    (polynomialInterval (List.length (baseLinks width)) f
      (sourceCharacter_supported width loop.edges 1))
  have hupper : endpointMean hw0 hw1 loop k k L ≤
      endpointMean hw0 hw1 loop k k 0+delta :=
    Q'.le_trans' _ _ _ hmeans.1 (Q'.add_le_add_left _ _ _ hgeo)
  have hlower : endpointMean hw0 hw1 loop k k 0 ≤
      endpointMean hw0 hw1 loop k k L+delta :=
    Q'.le_trans' _ _ _ hmeans.2 (Q'.add_le_add_left _ _ _ hgeo)
  have hpin : originalWindowScalar hw0 hw1 0 (.loop 0 loop 1) k k k ≈
      endpointMean hw0 hw1 loop k k 0 := by
    simpa only [endpointMean, sourcePolynomial, Nat.zero_mul,
      SU2QuaternionPartialFactorizedHaar.liftBoundary] using
      originalWindowScalar_pin hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0) k k k
  have hraw := originalJoint_approx hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)
    delta hd k k p
    (Nat.le_trans (Nat.le_max_right _ _) hkJ)
    (Nat.le_trans (Nat.le_max_left _ _) hkJ) hp
  have hbaseU : endpointMean hw0 hw1 loop k k 0 ≤ (Mean).approx p+delta :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin) hraw.1
  have hbaseL : (Mean).approx p ≤ endpointMean hw0 hw1 loop k k 0+delta :=
    Q'.le_trans' _ _ _ hraw.2
      (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ delta hpin))
  exact ⟨two_half_chain epsilon _ _ _ hupper hbaseU,
    two_half_chain epsilon _ _ _ hbaseL hlower⟩

private theorem ownMean_endpoint_one (stage n : Nat) :
    ownMean hw0 hw1 loop stage n ≈ endpointMean hw0 hw1 loop stage n 1 :=
  Q'.eqv_trans _ _ _ (middleRatio_swap hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) (n+1) n f)
    (Q'.eqv_symm (lower_endpoint_mean hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) n 1 (sourceCharacter_supported width loop.edges 1)))

/-- The actual odd-window center, not a supplied stationary mean. -/
theorem ownMean_converges :
    ConvergesTo (fun k => ofQ' (ownMean hw0 hw1 loop k k)) Mean :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun k => ofQ' (endpointMean hw0 hw1 loop k k 1))
    (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (ownMean_endpoint_one hw0 hw1 loop k k)))
    (endpointMean_converges hw0 hw1 loop 1)

private theorem mean_pin :
    Equiv (intrinsicForm hw0 hw1 (loopState loop) (unit width)) Mean := by
  have hchart := intrinsicForm_chart hw0 hw1 (loopState loop) (unit width) 0
    (Nat.le_refl 0) (Nat.le_refl 0)
  have hcongr := joint_congr hw0 hw1 0
    (.mul (mirror 0 (.loop 0 loop 1)) .one) (.loop 0 loop 1)
    ⟨Nat.le_refl 0, True.intro⟩ (Nat.le_refl 0) (by
      simp only [mirror, mapOffsets, sourcePolynomial]
      exact RatPolyCoeffEqv.mul_one _)
  exact hchart.trans (by
    simpa only [commonForm, loopState,
      BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit, chart,
      Nat.zero_sub, BF4ExactSlabFixedSpatialWilsonCenteredWindow.shift_zero] using hcongr)

/-- The denominator-side centered pair has the SAME existing centered
moment as its limit. The moving mean is expanded at finite stage first. -/
theorem own_centeredPair_converges (L : Nat) :
    ConvergesTo (fun k => ofQ'
      (centeredPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k L f
        (middleRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) (k+1) k f)))
      (centeredTimeMoment hw0 hw1 L (loopState loop) (loopState loop)) := by
  let Joint := originalJointLimit hw0 hw1 L
    (.mul (.loop 0 loop 1) (.loop L loop 1)) ⟨Nat.zero_le L, Nat.le_refl L⟩
  have hp : ConvergesTo (fun k => ofQ'
      (rawPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k L f)) Joint :=
    TrigAddCReal.convergesTo_congr_seq
      (s := fun k => ofQ' (originalWindowScalar hw0 hw1 L
        (.mul (.loop 0 loop 1) (.loop L loop 1)) k k k))
      (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
        Q'.eqv_symm (raw_original_pin hw0 hw1 width loop k k L)))
      (originalJoint_diagonal_converges hw0 hw1 L
        (.mul (.loop 0 loop 1) (.loop L loop 1)) ⟨Nat.zero_le L, Nat.le_refl L⟩)
  have hc := ownMean_converges hw0 hw1 loop
  have hm := endpointMean_converges hw0 hw1 loop L
  have h := TrigAddCReal.convergesTo_add
    (TrigAddCReal.convergesTo_add hp
      (TrigAddCReal.convergesTo_neg
        (convergesTo_mul_general (TrigAddCReal.convergesTo_add hc hc) hm)))
    (convergesTo_mul_general hc hc)
  have hfinite := TrigAddCReal.convergesTo_congr_seq
    (s := fun k => add
      (add (ofQ' (rawPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k L f))
        (neg (mul (add (ofQ' (ownMean hw0 hw1 loop k k))
          (ofQ' (ownMean hw0 hw1 loop k k))) (ofQ' (endpointMean hw0 hw1 loop k k L)))))
      (mul (ofQ' (ownMean hw0 hw1 loop k k)) (ofQ' (ownMean hw0 hw1 loop k k))))
    (t := fun k => ofQ' (centeredPair hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) k L f (ownMean hw0 hw1 loop k k)))
    (hs := h)
    (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (centered_pair_pin hw0 hw1 (headCutoff w+k) width
        (Nat.le_add_right _ _) k L (sourceCharacter_supported width loop.edges 1)
        (ownMean hw0 hw1 loop k k))))
  have halgebra : Equiv
      (add (add Joint (neg (mul (add Mean Mean) Mean))) (mul Mean Mean))
      (sub Joint (mul Mean Mean)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun p => poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.add (.var 1) (.var 1)) (.var 1))))
        (.mul (.var 1) (.var 1)))
      (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))) (by decide)
      (fun | 0 => Joint.approx p | _ => (Mean).approx p))
  have hmoment : Equiv (centeredTimeMoment hw0 hw1 L (loopState loop) (loopState loop))
      (sub Joint (mul Mean Mean)) :=
    (centeredTimeMoment_chronological_pin hw0 hw1 loop L).trans
      (equiv_sub (Equiv.refl _) ((Pivot2.mul_congr_left (mean_pin hw0 hw1 loop)).trans
        (Pivot2.mul_congr_right (mean_pin hw0 hw1 loop))))
  exact ArctanTrigConvergesProof.convergesTo_of_equiv hfinite
    (halgebra.trans hmoment.symm)

#print axioms endpointMean_converges
#print axioms ownMean_converges
#print axioms own_centeredPair_converges

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
