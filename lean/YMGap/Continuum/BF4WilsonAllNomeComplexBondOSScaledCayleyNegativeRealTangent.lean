/-
# The actual negative-real tangent on the original physical graph

Division by signed time -t makes the negative quotient the inverse action
applied to the positive quotient.  Its residual is the transported positive
residual plus 2i times the displacement of the SAME graph output.  Isometry
and the output's computed continuity radius therefore suffice; no new
analytic input, derivative-domain assumption on the output, or physical
clock calibration is introduced.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTimeContinuity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeTangent

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeRealTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.PositiveTimeReciprocalData (reciprocalReal reciprocalRealCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (Point ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction signedAction_positiveTime signedAction_neg_left signedAction_neg_right
    signedAction_pairing_preserved signedAction_distance signedAction_add_state)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation
  (signedAction_realScalar signedAction_imagScale signedAction_diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
  (realScalar differenceQuotient normalizedResidual quotient_error_pin normalized_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealTangent
  (realTangentRadius realTangentRadius_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeTangent
  (outputRows outputRows_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeContinuity
  (parameterDelta parameterDelta_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTimeContinuity
  (signedAction_near_zero_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency (imagScale cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq normSq_add_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (add_assoc add_comm add_zero neg_add add_neg add_right_cancel normSq_imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit (distance_symm)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_smul bondValue_negate)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_add completedSmul_mul completedSmul_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "RH" => BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
  (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "G" => signedAction hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "I" => imagScale hw0 hw1
local notation "Neg" => cneg hw0 hw1
local notation "RA" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "RS" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "RN" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def quarter : Q' := Q'.mkPos 1 4 (by decide)
private def sixteenth : Q' := Q'.mkPos 1 16 (by decide)
private def posClock (D : PositiveTime) : SignedRealTimeData.SignedTimeValue :=
  SignedRealTimeData.positiveTime (timeValue D)

/-- The actual signed numerical time -D.real, not a new physical clock. -/
def negativeClock (D : PositiveTime) : SignedRealTimeData.SignedTimeValue :=
  SignedRealTimeData.negTime (posClock D)

theorem negativeClock_value (D : PositiveTime) :
    SignedRealTimeData.realValue (negativeClock D) =
      RCsub RCzero (realValue (timeValue D)) := by
  unfold negativeClock posClock
  rw [SignedRealTimeData.realValue_negTime,SignedRealTimeData.realValue_positiveTime]

private theorem cneg_cneg (x : H) : Neg (Neg x) = x := by
  apply add_right_cancel hw0 hw1 _ _ (Neg x)
  rw [neg_add,add_neg]

private theorem cancel_middle (a b c : H) : A (A a c) (diff hw0 hw1 b c) = A a b := by
  unfold diff
  calc
    A (A a c) (A b (Neg c)) = A a (A c (A b (Neg c))) := add_assoc hw0 hw1 a c _
    _ = A a (A (A c b) (Neg c)) := by rw [← add_assoc hw0 hw1 c b (Neg c)]
    _ = A a (A (A b c) (Neg c)) := by rw [add_comm hw0 hw1 c b]
    _ = A a (A b (A c (Neg c))) := by rw [add_assoc hw0 hw1 b c _]
    _ = A a b := by rw [add_neg,add_zero]

private theorem rational_add (q : Q') (x y : RH) :
    RS q (RA x y) = RA (RS q x) (RS q y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 q _ _

private theorem negate_add (x y : RH) : RN (RA x y) = RA (RN x) (RN y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate,bondValue_add]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem rational_neg (q : Q') (x : RH) : RS q (RN x) = RN (RS q x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change BF4WilsonAllNomeLinear.completedSmul hw0 hw1 q
      (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1)
        (BF4WilsonAllNomeBondOSTime.bondValue hw0 hw1 x)) =
    BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1)
      (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 q
        (BF4WilsonAllNomeBondOSTime.bondValue hw0 hw1 x))
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv q (-1)) _

private theorem imag_diff (q : Q') (x y : H) :
    I q (diff hw0 hw1 x y) = diff hw0 hw1 (I q x) (I q y) := by
  have ha (u v : H) : I q (A u v) = A (I q u) (I q v) :=
    Prod.ext ((congrArg RN (rational_add hw0 hw1 q u.2 v.2)).trans
      (negate_add hw0 hw1 _ _)) (rational_add hw0 hw1 q u.1 v.1)
  have hn (u : H) : I q (Neg u) = Neg (I q u) :=
    Prod.ext (congrArg RN (rational_neg hw0 hw1 q u.2)) (rational_neg hw0 hw1 q u.1)
  unfold diff
  rw [ha,hn]

private theorem posAction_pin (D : PositiveTime) (x : H) :
    G (posClock D) x = positiveAction hw0 hw1 D x := by
  unfold posClock
  rw [signedAction_positiveTime,positiveRealAction_pin]

/-- Division by signed time -t reverses the numerator. This is the ACTUAL
negative action increment, scaled by the supplied positive reciprocal. -/
def negativeDifferenceQuotient (p : P) (D : PositiveTime) : H :=
  realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
    (diff hw0 hw1 (input hw0 hw1 (ofPoint hw0 hw1 p))
      (G (negativeClock D) (input hw0 hw1 (ofPoint hw0 hw1 p))))

/-- No minus sign remains: the denominator itself is -t. -/
theorem negative_quotient_pin (p : P) (D : PositiveTime) :
    negativeDifferenceQuotient hw0 hw1 p D =
      G (negativeClock D) (differenceQuotient hw0 hw1 p D) := by
  unfold negativeDifferenceQuotient differenceQuotient
  rw [signedAction_realScalar,signedAction_diff]
  have hinv : G (negativeClock D)
      (positiveAction hw0 hw1 D (input hw0 hw1 (ofPoint hw0 hw1 p))) =
      input hw0 hw1 (ofPoint hw0 hw1 p) := by
    rw [← posAction_pin]
    exact signedAction_neg_left hw0 hw1 (posClock D) _
  rw [hinv]

def negativeResidual (p : P) (D : PositiveTime) : H :=
  diff hw0 hw1 (negativeDifferenceQuotient hw0 hw1 p D)
    (Neg (I 2 (output hw0 hw1 (ofPoint hw0 hw1 p))))

/-- The residual joins the transported positive error and actual OUTPUT
displacement, not an assumed derivative-domain property of the output. -/
theorem negative_error_identity (p : P) (D : PositiveTime) :
    negativeResidual hw0 hw1 p D =
      A (G (negativeClock D) (normalizedResidual hw0 hw1 p D))
        (I 2 (diff hw0 hw1 (output hw0 hw1 (ofPoint hw0 hw1 p))
          (G (negativeClock D) (output hw0 hw1 (ofPoint hw0 hw1 p))))) := by
  have htransport : G (negativeClock D) (normalizedResidual hw0 hw1 p D) =
      A (negativeDifferenceQuotient hw0 hw1 p D)
        (I 2 (G (negativeClock D) (output hw0 hw1 (ofPoint hw0 hw1 p)))) := by
    rw [← quotient_error_pin]
    unfold diff
    rw [cneg_cneg,signedAction_add_state,signedAction_imagScale,← negative_quotient_pin]
  rw [htransport,imag_diff,cancel_middle]
  unfold negativeResidual diff
  rw [cneg_cneg]

def negativeRealRadius (p : P) (e : Q') (he : (0 : Q') < e) : Q' :=
  Q'.min'
    (realTangentRadius hw0 hw1 p (quarter*e) (Q'.mul_pos (by decide) he))
    (parameterDelta hw0 hw1 (outputRows hw0 hw1 p) (sixteenth*e)
      (Q'.mul_pos (by decide) he))

theorem negativeRealRadius_positive (p : P) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < negativeRealRadius hw0 hw1 p e he :=
  CReal.min_pos (realTangentRadius_positive hw0 hw1 p _ _)
    (parameterDelta_positive hw0 hw1 (outputRows hw0 hw1 p) _ _)

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

private theorem negative_time_upper (D : PositiveTime) (r : Q') (hr : (0 : Q') < r) :
    RCle (SignedRealTimeData.realValue (negativeClock D)) (rat r) := by
  rw [negativeClock_value]
  intro e he
  refine ⟨D.start,fun n hn => ?_⟩
  change (0 : Q') + -(D.real.approx n) ≤ r+e
  rw [Q'.zero_add']
  have ht : (0 : Q') ≤ D.real.approx n :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt D.floor_positive) (D.lower n hn)
  exact Q'.le_trans' _ _ _ (Q'.nonpos_neg_of_nonneg ht)
    (Q'.le_trans' _ _ _ (Q'.le_of_lt hr)
      (Q'.add_le_self_of_nonneg r e (Q'.le_of_lt he)))

private theorem inverse_displacement (D : PositiveTime) (x : H) :
    distance hw0 hw1 (G (negativeClock D) x) x =
      distance hw0 hw1 (G (posClock D) x) x := by
  calc
    distance hw0 hw1 (G (negativeClock D) x) x =
        distance hw0 hw1 (G (posClock D) (G (negativeClock D) x)) (G (posClock D) x) :=
      (signedAction_distance hw0 hw1 (posClock D) _ _).symm
    _ = distance hw0 hw1 x (G (posClock D) x) := by
      unfold negativeClock
      rw [signedAction_neg_right]
    _ = distance hw0 hw1 (G (posClock D) x) x := distance_symm hw0 hw1 _ _

private theorem output_displacement (p : P) (D : PositiveTime) (e : Q') (he : (0 : Q') < e)
    (ht : RCle (realValue (timeValue D))
      (rat (parameterDelta hw0 hw1 (outputRows hw0 hw1 p) e he))) :
    RCle (distance hw0 hw1 (G (negativeClock D) (output hw0 hw1 (ofPoint hw0 hw1 p)))
      (output hw0 hw1 (ofPoint hw0 hw1 p))) (rat e) := by
  rw [inverse_displacement,← outputRows_pin]
  apply signedAction_near_zero_ofRows hw0 hw1 (posClock D) (outputRows hw0 hw1 p) e he
  · change RCle (SignedRealTimeData.realValue
      (SignedRealTimeData.positiveTime (timeValue D))) _
    rwa [SignedRealTimeData.realValue_positiveTime]
  · exact negative_time_upper D _ (parameterDelta_positive hw0 hw1 _ e he)

private theorem error_budget (e : Q') :
    RCadd (RCadd (rat (quarter*e)) (rat (quarter*e)))
      (RCadd (RCscale (2*2) (rat (sixteenth*e)))
        (RCscale (2*2) (rat (sixteenth*e)))) = rat e := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => by
    have hp := poly_identity_of_normal_eq
      (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))
        (.add (.mul (.mul (.const 2) (.const 2)) (.mul (.var 2) (.var 0)))
          (.mul (.mul (.const 2) (.const 2)) (.mul (.var 2) (.var 0)))))
      (.mul (.add (.add (.var 1) (.var 1))
        (.add (.mul (.mul (.const 2) (.const 2)) (.var 2))
          (.mul (.mul (.const 2) (.const 2)) (.var 2)))) (.var 0))
      (by decide) (fun | 0 => e | 1 => quarter | _ => sixteenth)
    have hc : Q'.eqv ((quarter+quarter)+((2*2)*sixteenth+(2*2)*sixteenth)) 1 := by decide
    exact Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e hc) (Q'.one_mul_eqv e))))

/-- The SAME -2i graph slope holds for all sufficiently small supplied NEGATIVE
real increments, with a computed positive radius and actual signed denominator. -/
theorem negative_normalized_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (D : PositiveTime)
    (ht : RCle (realValue (timeValue D)) (rat (negativeRealRadius hw0 hw1 p e he))) :
    RCle (N (negativeResidual hw0 hw1 p D)) (rat e) := by
  have hplus := normalized_bound hw0 hw1 p (quarter*e) (Q'.mul_pos (by decide) he) D
    (RCle_trans ht (rat_le (Q'.min_le_left' _ _)))
  have hnorm : N (G (negativeClock D) (normalizedResidual hw0 hw1 p D)) =
      N (normalizedResidual hw0 hw1 p D) :=
    congrArg Prod.fst (signedAction_pairing_preserved hw0 hw1 (negativeClock D) _ _)
  have houtput := output_displacement hw0 hw1 p D (sixteenth*e)
    (Q'.mul_pos (by decide) he) (RCle_trans ht (rat_le (Q'.min_le_right' _ _)))
  have hcorrection : RCle
      (N (I 2 (diff hw0 hw1 (output hw0 hw1 (ofPoint hw0 hw1 p))
        (G (negativeClock D) (output hw0 hw1 (ofPoint hw0 hw1 p))))))
      (RCscale (2*2) (rat (sixteenth*e))) := by
    rw [normSq_imagScale,← distance_eq_norm_difference,distance_symm]
    exact RCscale_mono (by decide) houtput
  rw [negative_error_identity]
  have htriangle := normSq_add_le hw0 hw1
    (G (negativeClock D) (normalizedResidual hw0 hw1 p D))
    (I 2 (diff hw0 hw1 (output hw0 hw1 (ofPoint hw0 hw1 p))
      (G (negativeClock D) (output hw0 hw1 (ofPoint hw0 hw1 p)))))
  rw [hnorm] at htriangle
  have hbudget := RCadd_le_add (RCadd_le_add hplus hplus)
    (RCadd_le_add hcorrection hcorrection)
  rw [error_budget] at hbudget
  exact RCle_trans htriangle hbudget

def negativeRealTangentCertificate (p : P) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ D : PositiveTime, RCle (realValue (timeValue D)) (rat r) →
        RCle (N (negativeResidual hw0 hw1 p D)) (rat e)) :=
  ⟨negativeRealRadius hw0 hw1 p e he,negativeRealRadius_positive hw0 hw1 p e he,
    negative_normalized_bound hw0 hw1 p e he⟩

/-- ONE source-computed radius controls BOTH signed directions of the actual
quotient on supplied positive-time data. No sign of an arbitrary real is
decided, and no representative or modulus is selected from its quotient. -/
def twoSidedTangentCertificate (p : P) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ D : PositiveTime, RCle (realValue (timeValue D)) (rat r) →
        (RCle (N (normalizedResidual hw0 hw1 p D)) (rat e)) ×'
        (RCle (N (negativeResidual hw0 hw1 p D)) (rat e))) :=
  ⟨Q'.min' (realTangentRadius hw0 hw1 p e he) (negativeRealRadius hw0 hw1 p e he),
    CReal.min_pos (realTangentRadius_positive hw0 hw1 p e he)
      (negativeRealRadius_positive hw0 hw1 p e he),
    fun D ht =>
      ⟨normalized_bound hw0 hw1 p e he D (RCle_trans ht (rat_le (Q'.min_le_left' _ _))),
        negative_normalized_bound hw0 hw1 p e he D
          (RCle_trans ht (rat_le (Q'.min_le_right' _ _)))⟩⟩

#print axioms negativeClock
#print axioms negativeClock_value
#print axioms negativeDifferenceQuotient
#print axioms negative_quotient_pin
#print axioms negativeResidual
#print axioms negative_error_identity
#print axioms negativeRealRadius
#print axioms negativeRealRadius_positive
#print axioms negative_normalized_bound
#print axioms negativeRealTangentCertificate
#print axioms twoSidedTangentCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeRealTangent
