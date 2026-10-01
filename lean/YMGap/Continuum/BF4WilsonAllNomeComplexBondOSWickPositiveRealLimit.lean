/-
# Actual positive-real Euclidean/Cayley Wick remainder on the Wilson bond

The rational Wick identity is passed to one SUPPLIED positive-real time datum.
Both the original Euclidean action and the constructed Cayley action are
compared with their OWN rational samples on the SAME original physical bond
carrier.  The source graph point and numerical time datum provide every
Type-valued rate.  This is a dimensionless fixed-carrier tangent estimate,
not Wick analytic continuation or physical-clock calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickSlopeComparison
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSEuclideanSampleLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDomainDisplacement
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
import YMGap.Continuum.RationalScalarTwoSidedError
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
import YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.EffMassConvergence
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickPositiveRealLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime sample rational)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue realValue_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (add_assoc add_comm add_zero zero_add neg_add add_neg add_right_cancel
    normSq_imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_symm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (sample_positive timeRows_pin timeLimitRate timeLimit_bound positiveAction_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDomainDisplacement
  (pointRows pointRows_input)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSEuclideanSampleLimit
  (euclideanSampleRate euclidean_sample_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickSlopeComparison
  (wickRadius wickRadius_positive wickRemainder_pin wick_remainder_bound
    rational_time_value)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_add completedSmul_mul completedSmul_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "I" => imagScale hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "Dist" => distance hw0 hw1
local notation "Neg" => cneg hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem rat_mul (a b : Q') : RCmul (rat a) (rat b) = rat (a*b) :=
  (Quotient.sound (CRealAlg.ofQ'_mul a b)).symm

private theorem scale_rat (a b : Q') : RCscale a (rat b) = rat (a*b) :=
  (Quotient.sound (CRealAlg.ofQ'_mul a b)).symm

private theorem rat_add (a b : Q') : RCadd (rat a) (rat b) = rat (a+b) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_refl (a+b)))

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

private theorem add_exchange (a b c d : H) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  calc
    A (A a b) (A c d) = A a (A b (A c d)) := add_assoc hw0 hw1 _ _ _
    _ = A a (A c (A b d)) := by
      rw [← add_assoc hw0 hw1 b c d,add_comm hw0 hw1 b c,
        add_assoc hw0 hw1 c b d]
    _ = A (A a c) (A b d) := (add_assoc hw0 hw1 _ _ _).symm

private theorem neg_additive (x y : H) : Neg (A x y) = A (Neg x) (Neg y) := by
  apply add_right_cancel hw0 hw1 _ _ (A x y)
  rw [← add_exchange hw0 hw1 (Neg x) x (Neg y) y]
  simp only [neg_add,zero_add]

private theorem neg_neg (x : H) : Neg (Neg x) = x := by
  apply add_right_cancel hw0 hw1 _ _ (Neg x)
  rw [neg_add,add_neg]

private theorem diff_add (a b c d : H) :
    diff hw0 hw1 (A a b) (A c d) =
      A (diff hw0 hw1 a c) (diff hw0 hw1 b d) := by
  unfold diff
  rw [neg_additive]
  exact add_exchange hw0 hw1 a b (Neg c) (Neg d)

private theorem diff_shared_right (a b c : H) :
    diff hw0 hw1 (diff hw0 hw1 a c) (diff hw0 hw1 b c) =
      diff hw0 hw1 a b := by
  unfold diff
  rw [neg_additive,neg_neg]
  rw [add_exchange hw0 hw1 a (Neg c) (Neg b) c,neg_add,add_zero]

private theorem diff_shared_left (a b c : H) :
    diff hw0 hw1 (diff hw0 hw1 a b) (diff hw0 hw1 a c) =
      diff hw0 hw1 c b := by
  unfold diff
  rw [neg_additive,neg_neg]
  rw [add_exchange hw0 hw1 a (Neg b) (Neg a) c,add_neg,zero_add]
  exact add_comm hw0 hw1 _ _

private theorem add_diff (a b : H) : A (diff hw0 hw1 a b) b = a := by
  unfold diff
  rw [add_assoc,neg_add,add_zero]

private theorem real_scale_add (c : Q')
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) :
    BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y) =
      BF4WilsonAllNomeBondOSLinear.add hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 c _ _

private theorem real_neg_additive
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) :
    BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y) =
      BF4WilsonAllNomeBondOSLinear.add hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x)
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add,bondValue_negate]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem real_scale_neg (c : Q')
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) :
    BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x) =
      BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change BF4WilsonAllNomeLinear.completedSmul hw0 hw1 c
      (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1) (bondValue hw0 hw1 x)) =
    BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1)
      (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 c (bondValue hw0 hw1 x))
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv c (-1)) _

private theorem imag_add (c : Q') (x y : H) :
    I c (A x y) = A (I c x) (I c y) := by
  apply Prod.ext
  · exact (congrArg (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1)
      (real_scale_add hw0 hw1 c x.2 y.2)).trans
      (real_neg_additive hw0 hw1 _ _)
  · exact real_scale_add hw0 hw1 c x.1 y.1

private theorem imag_neg (c : Q') (x : H) : I c (Neg x) = Neg (I c x) := by
  apply Prod.ext
  · exact congrArg (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1)
      (real_scale_neg hw0 hw1 c x.2)
  · exact real_scale_neg hw0 hw1 c x.1

private theorem imag_diff (c : Q') (x y : H) :
    diff hw0 hw1 (I c x) (I c y) = I c (diff hw0 hw1 x y) := by
  unfold diff
  rw [imag_add,imag_neg]

/-- The actual positive-real remainder uses the original Wilson transfer
action and the constructed positive-real Cayley action on the SAME graph input. -/
def realWickRemainder (p : P) (D : PositiveTime) : H :=
  let u := input hw0 hw1 (ofPoint hw0 hw1 p)
  A (diff hw0 hw1
      (BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime.positiveAction
        hw0 hw1 D u) u)
    (I 2 (diff hw0 hw1 u
      (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1 (timeValue D) u)))

private def rationalWickRemainder (p : P) (D : PositiveTime) (n : Nat) : H :=
  let u := input hw0 hw1 (ofPoint hw0 hw1 p)
  let q := sample D n
  A (diff hw0 hw1 (F q (sample_positive D n) u) u)
    (I 2 (diff hw0 hw1 u
      (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
        (timeValue (rational q (sample_positive D n))) u)))

private theorem rationalWick_pin (p : P) (D : PositiveTime) (n : Nat) :
    rationalWickRemainder hw0 hw1 p D n =
      BF4WilsonAllNomeComplexBondOSWickSlopeComparison.wickRemainder
        hw0 hw1 p (sample D n) (sample_positive D n) :=
  (wickRemainder_pin hw0 hw1 p (sample D n) (sample_positive D n)).symm

private theorem real_sample_distance (p : P) (D : PositiveTime)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : max
      (timeLimitRate hw0 hw1 D (pointRows hw0 hw1 p) e)
      (euclideanSampleRate hw0 hw1 p D e) ≤ n) :
    RCle (Dist (realWickRemainder hw0 hw1 p D)
      (rationalWickRemainder hw0 hw1 p D n)) (rat (10*e)) := by
  let X := pointRows hw0 hw1 p
  let u := input hw0 hw1 (ofPoint hw0 hw1 p)
  let U := BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime.positiveAction
    hw0 hw1 D u
  let Un := F (sample D n) (sample_positive D n) u
  let S := BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1 (timeValue D) u
  let Sn := BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
    (timeValue (rational (sample D n) (sample_positive D n))) u
  have hu : ofRows hw0 hw1 X = u := pointRows_input hw0 hw1 p
  have hU : RCle (Dist U Un) (rat e) := by
    rw [distance_symm]
    have h := timeLimit_bound hw0 hw1 D X e he n
      (Nat.le_trans (Nat.le_max_left _ _) hn)
    rw [timeRows_pin,← positiveAction_ofRows,hu] at h
    exact h
  have hS : RCle (Dist S Sn) (rat e) :=
    euclidean_sample_bound hw0 hw1 p D e he n
      (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hexact : diff hw0 hw1 (realWickRemainder hw0 hw1 p D)
      (rationalWickRemainder hw0 hw1 p D n) =
      A (diff hw0 hw1 U Un) (I 2 (diff hw0 hw1 Sn S)) := by
    unfold realWickRemainder rationalWickRemainder
    rw [diff_add,diff_shared_right,imag_diff,diff_shared_left]
  rw [distance_eq_norm_difference,hexact]
  have hnorm := normSq_add_le hw0 hw1
    (diff hw0 hw1 U Un) (I 2 (diff hw0 hw1 Sn S))
  have hphase : RCle (N (I 2 (diff hw0 hw1 Sn S))) (rat (4*e)) := by
    rw [normSq_imagScale,← distance_eq_norm_difference,distance_symm]
    have h := RCscale_mono (by decide : (0 : Q') ≤ (2 : Q')*2) hS
    have hfour : rat (((2 : Q')*2)*e) = rat (4*e) :=
      Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
        Q'.mul_eqv_congr_right _ _ e (by decide)))
    rwa [scale_rat,hfour] at h
  have hsum := RCle_trans hnorm
    (RCadd_le_add (RCadd_le_add
      (by rw [← distance_eq_norm_difference]; exact hU)
      (by rw [← distance_eq_norm_difference]; exact hU))
      (RCadd_le_add hphase hphase))
  change RCle _
    (RCadd (RCadd (rat e) (rat e))
      (RCadd (rat (4*e)) (rat (4*e)))) at hsum
  have hcollapse : RCadd (RCadd (rat e) (rat e))
      (RCadd (rat (4*e)) (rat (4*e))) = rat (10*e) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0))
          (.add (.mul (.const 4) (.var 0)) (.mul (.const 4) (.var 0))))
        (.mul (.const 10) (.var 0)) (by decide) (fun _ => e)))
  rwa [hcollapse] at hsum

/- The remaining scalar closure is supplied below without identifying the
two operator sample streams. -/

private theorem sample_converges (D : PositiveTime) :
    CReal.ConvergesTo (fun n => ofQ' (sample D n)) D.real := by
  intro e he
  refine ⟨D.cauchy.M e,fun n hn => ⟨D.cauchy.M e,fun j hj => ?_⟩⟩
  exact D.cauchy.bound e he (D.start+n) j
    (Nat.le_trans hn (Nat.le_add_left _ _)) hj

private def sampleSquare (D : PositiveTime) (e : Q') (n : Nat) : CReal :=
  CReal.mul (CReal.mul (ofQ' (sample D n)) (ofQ' (sample D n))) (ofQ' e)

private def realSquare (D : PositiveTime) (e : Q') : CReal :=
  CReal.mul (CReal.mul D.real D.real) (ofQ' e)

private theorem sampleSquare_converges (D : PositiveTime) (e : Q') :
    CReal.ConvergesTo (sampleSquare D e) (realSquare D e) := by
  have htime := sample_converges D
  have hpair :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      htime htime
  have hconst := CReal.convergesTo_const (ofQ' e)
  exact Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
    hpair hconst

private theorem sampleSquare_pin (D : PositiveTime) (e : Q') (n : Nat) :
    Quotient.mk crealSetoid (sampleSquare D e n) =
      rat (((sample D n)*(sample D n))*e) := by
  change RCmul (RCmul (rat (sample D n)) (rat (sample D n))) (rat e) = _
  rw [rat_mul,rat_mul]

private theorem double_half_square (D : PositiveTime) (e : Q') :
    RCadd
      (Quotient.mk crealSetoid (realSquare D (HalfPow.half*e)))
      (Quotient.mk crealSetoid (realSquare D (HalfPow.half*e))) =
    RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat e) := by
  rw [realValue_pin]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_add_eqv
        (D.real.approx n*D.real.approx n)
        (HalfPow.half*e) (HalfPow.half*e)))
      (Q'.mul_eqv_congr_left (D.real.approx n*D.real.approx n)
        _ _ (ExpNeg.two_halves e))))

private theorem rc_add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro aa bb
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (aa.approx n) (bb.approx n)))

private theorem rc_limit_le (a : RC) (s : Nat → CReal) (L : CReal)
    (hs : CReal.ConvergesTo s L) (k : Nat)
    (h : ∀ n, k ≤ n → RCle a (Quotient.mk crealSetoid (s n))) :
    RCle a (Quotient.mk crealSetoid L) := by
  revert h
  refine Quotient.inductionOn a ?_
  intro aa h
  exact BF4ExactSlabThermodynamicScalarRows.limit_le_of_eventual
    (CReal.convergesTo_const aa) hs k
    (fun n hn => h n hn)

private theorem sample_below_radius (D : PositiveTime) (r : Q')
    (hr : (0 : Q') < r)
    (hclock : RCle (realValue (timeValue D)) (rat (HalfPow.half*r))) :
    ∃ k : Nat, ∀ n, k ≤ n → sample D n ≤ r := by
  rw [realValue_pin] at hclock
  change CReal.leEv D.real (ofQ' (HalfPow.half*r)) at hclock
  have hh : (0 : Q') < HalfPow.half*r := ExpNeg.half_mul_pos r hr
  obtain ⟨k,hk⟩ := hclock (HalfPow.half*r) hh
  refine ⟨k,fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (hk (D.start+n) (Nat.le_trans hn (Nat.le_add_left _ _)))
    (Q'.le_of_eqv (ExpNeg.two_halves r))

private theorem twenty_twentieths (e : Q') :
    Q'.eqv (20*((Q'.mkPos 1 20 (by decide))*e)) e := by
  let c : Q' := Q'.mkPos 1 20 (by decide)
  have hc : Q'.eqv (20*c) 1 := by decide
  have ha : Q'.eqv (20*(c*e)) ((20*c)*e) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  exact Q'.eqv_trans _ _ _ ha
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.one_mul_eqv e))

/-- The radius is computed solely from the supplied represented graph point.
Only the bound proof, never the radius construction, eliminates RC order data. -/
def realWickRadius (p : P) (e : Q') (he : (0 : Q') < e) : Q' :=
  HalfPow.half * wickRadius hw0 hw1 p (HalfPow.half*e)
    (ExpNeg.half_mul_pos e he)

theorem realWickRadius_positive (p : P) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < realWickRadius hw0 hw1 p e he :=
  ExpNeg.half_mul_pos _
    (wickRadius_positive hw0 hw1 p (HalfPow.half*e)
      (ExpNeg.half_mul_pos e he))

/-- Original positive-real Cayley/Euclidean Wick remainder, with its exact
dimensionless factor two and its supplied numerical time value. The bound is on the
SAME fixed Wilson carrier; no physical-spacing calibration is asserted. -/
theorem real_wick_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (D : PositiveTime)
    (hclock : RCle (realValue (timeValue D))
      (rat (realWickRadius hw0 hw1 p e he))) :
    RCle (N (realWickRemainder hw0 hw1 p D))
      (RCmul (RCmul (realValue (timeValue D))
        (realValue (timeValue D))) (rat e)) := by
  let eta := HalfPow.half*e
  have heta : (0 : Q') < eta := ExpNeg.half_mul_pos e he
  let r := wickRadius hw0 hw1 p eta heta
  have hr : (0 : Q') < r := wickRadius_positive hw0 hw1 p eta heta
  have hsample := sample_below_radius D r hr hclock
  obtain ⟨kr,hkr⟩ := hsample
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon hepsilon
  let delta : Q' := (Q'.mkPos 1 20 (by decide))*epsilon
  have hdelta : (0 : Q') < delta := Q'.mul_pos (by decide) hepsilon
  let X := pointRows hw0 hw1 p
  let k := max kr
    (max (timeLimitRate hw0 hw1 D X delta)
      (euclideanSampleRate hw0 hw1 p D delta))
  let sq n := sampleSquare D eta n
  let Sq := realSquare D eta
  let rhs n := CReal.add (ofQ' (20*delta)) (CReal.add (sq n) (sq n))
  let RHS := CReal.add (ofQ' (20*delta)) (CReal.add Sq Sq)
  have hsq : CReal.ConvergesTo sq Sq := sampleSquare_converges D eta
  have hsum : CReal.ConvergesTo (fun n => CReal.add (sq n) (sq n))
      (CReal.add Sq Sq) :=
    YMGap.Constructive.TrigAddCReal.convergesTo_add hsq hsq
  have hrhs : CReal.ConvergesTo rhs RHS :=
    YMGap.Continuum.EffMassConvergence.convergesTo_add_left _ hsum
  have hfinite (n : Nat) (hn : k ≤ n) :
      RCle (N (realWickRemainder hw0 hw1 p D))
        (Quotient.mk crealSetoid (rhs n)) := by
    have hnr : kr ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hnother : max (timeLimitRate hw0 hw1 D X delta)
        (euclideanSampleRate hw0 hw1 p D delta) ≤ n :=
      Nat.le_trans (Nat.le_max_right _ _) hn
    have hdist := real_sample_distance hw0 hw1 p D delta hdelta n hnother
    have hqn : sample D n ≤ r := hkr n hnr
    have hwick : RCle (N (rationalWickRemainder hw0 hw1 p D n))
        (rat (((sample D n)*(sample D n))*eta)) := by
      rw [rationalWick_pin]
      exact wick_remainder_bound hw0 hw1 p eta heta
        (sample D n) (sample_positive D n) hqn
    have hnorm := normSq_add_le hw0 hw1
      (diff hw0 hw1 (realWickRemainder hw0 hw1 p D)
        (rationalWickRemainder hw0 hw1 p D n))
      (rationalWickRemainder hw0 hw1 p D n)
    rw [add_diff] at hnorm
    have hbounds := RCle_trans hnorm
      (RCadd_le_add
        (RCadd_le_add (by rw [← distance_eq_norm_difference]; exact hdist)
          (by rw [← distance_eq_norm_difference]; exact hdist))
        (RCadd_le_add hwick hwick))
    have htwo : RCadd (rat (10*delta)) (rat (10*delta)) = rat (20*delta) :=
      Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
        poly_identity_of_normal_eq
          (.add (.mul (.const 10) (.var 0)) (.mul (.const 10) (.var 0)))
          (.mul (.const 20) (.var 0)) (by decide) (fun _ => delta)))
    rw [htwo] at hbounds
    simp only [← sampleSquare_pin D eta n] at hbounds
    exact hbounds
  have hlim := rc_limit_le
    (N (realWickRemainder hw0 hw1 p D)) rhs RHS hrhs k hfinite
  change RCle _ (RCadd (rat (20*delta))
    (RCadd (Quotient.mk crealSetoid Sq) (Quotient.mk crealSetoid Sq))) at hlim
  rw [double_half_square D e,
    rc_add_comm (rat (20*delta))
      (RCmul (RCmul (realValue (timeValue D))
        (realValue (timeValue D))) (rat e))] at hlim
  have hbudget : rat (20*delta) = rat epsilon :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => twenty_twentieths epsilon))
  rwa [hbudget] at hlim

#print axioms realWickRemainder
#print axioms realWickRadius
#print axioms realWickRadius_positive
#print axioms real_wick_bound

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickPositiveRealLimit
