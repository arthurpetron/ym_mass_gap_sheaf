/-
# Real-time Taylor derivative on the original Wilson transfer range

The actual dyadic Taylor remainders have supplied original Cauchy rows.
Their limit is Tx-S(t)Tx-t*A x, using the previously constructed original
real-time action and real scalar multiplication. Eventual dyadic estimates
pass to that limit without discarding the factor t^2 or selecting inverses.

For every supplied original input and positive epsilon, a computed positive
radius controls every supplied positive real increment below it. Time is
still measured in original T(1) units. The closed generator domain,
self-adjointness, physical calibration, scaling and Clay target remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeMeshDerivative
import YMGap.Continuum.BF4WilsonAllNomeRowLinear
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins

namespace YMGap.Continuum.BF4WilsonAllNomeRealDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeRowLinear
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (action_embed)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction derivativeCertificate)
open YMGap.Continuum.BF4WilsonAllNomeMeshDerivative
open YMGap.Continuum.CRealSeminormPairingCompletion (representativeInner)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Order passage compares already-constructed limits; no witness is extracted. -/
private theorem limit_le_of_eventual {a b : Nat → CReal} {L M : CReal}
    (ha : ConvergesTo a L) (hb : ConvergesTo b M) (N : Nat)
    (h : ∀ n, N≤n → leEv (a n) (b n)) : leEv L M := by
  have shift {f : Nat → CReal} {l : CReal} (hf : ConvergesTo f l) :
      ConvergesTo (fun n => f (max n N)) l := by
    intro epsilon he
    obtain ⟨K,hK⟩ := hf epsilon he
    exact ⟨K,fun n hn => hK (max n N) (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le (shift ha) (shift hb)
    (fun n => h (max n N) (Nat.le_max_right _ _))

/-- The existing explicit pairing modulus supplies the convergence stage. -/
theorem pairing_converges (R S : RepresentedCauchy hw0 hw1 (width := width)) :
    ConvergesTo (fun n => representativeInner (pairingData hw0 hw1) (R.row n) (S.row n))
      (pairingRepresentative hw0 hw1 R S) := by
  intro epsilon he
  let d := HalfPow.half*epsilon
  have hd : (0 : Q')<d := ExpNeg.half_mul_pos epsilon he
  refine ⟨pairingModulus hw0 hw1 R S d,fun n hn => ?_⟩
  have hb := row_pairing_bound hw0 hw1 R S d hd n hn
  obtain ⟨N,hN⟩ := hb.1 d hd
  obtain ⟨M,hM⟩ := hb.2 d hd
  refine ⟨max N M,fun j hj => ?_⟩
  have budget (q : Q') : Q'.eqv ((q+d)+d) (q+epsilon) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))
  exact ⟨Q'.le_trans' _ _ _ (hN j (Nat.le_trans (Nat.le_max_left _ _) hj))
      (Q'.le_of_eqv (budget _)),
    Q'.le_trans' _ _ _ (hM j (Nat.le_trans (Nat.le_max_right _ _) hj))
      (Q'.le_of_eqv (budget _))⟩

def derivativeRepresentative (X : (PD).Cauchy) : (PD).Cauchy :=
  (derivativeCertificate hw0 hw1 X).fst

theorem derivativeRepresentative_pin (X : (PD).Cauchy) :
    Class (derivativeRepresentative hw0 hw1 X) = A (Class X) :=
  (derivativeCertificate hw0 hw1 X).snd.snd.fst

def realRemainder (D : PositiveTime) (x : V) : V :=
  completedSub hw0 hw1
    (completedSub hw0 hw1 (T 1 x) (realTimeAction hw0 hw1 (timeValue D) (T 1 x)))
    (completedRealSmul hw0 hw1 D.real D.cauchy (A x))

theorem realRemainder_time_congr (D E : PositiveTime) (h : Equiv D.real E.real) (x : V) :
    realRemainder hw0 hw1 D x = realRemainder hw0 hw1 E x := by
  have ht : timeValue D = timeValue E := Quotient.sound h
  unfold realRemainder
  rw [ht,completedRealSmul_congr hw0 hw1 _ _ _ _ h]

def remainderRows (D : PositiveTime) (X : (PD).Cauchy) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  differenceRows hw0 hw1
    (differenceRows hw0 hw1
      (constantRows hw0 hw1 ((timeNonexpansive hw0 hw1 1).mapCauchy X))
      (timeRows hw0 hw1 D ((timeNonexpansive hw0 hw1 1).mapCauchy X)))
    (scalarRows hw0 hw1 (approximationReal D) (approximationCauchy D)
      (derivativeRepresentative hw0 hw1 X))

theorem remainderRows_pin (D : PositiveTime) (X : (PD).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (remainderRows hw0 hw1 D X) n =
      meshRemainder hw0 hw1 (approximation D n).depth (approximation D n).steps (Class X) := by
  unfold remainderRows
  rw [differenceRows_pin,differenceRows_pin,constantRows_point,timeRows_pin,
    scalarRows_pin,action_embed,derivativeRepresentative_pin]
  rfl

theorem remainderRows_limit (D : PositiveTime) (X : (PD).Cauchy) :
    limit hw0 hw1 (remainderRows hw0 hw1 D X) = realRemainder hw0 hw1 D (Class X) := by
  unfold remainderRows
  rw [rowLimit_difference,rowLimit_difference,limit_constantRows,scalarRows_limit,
    derivativeRepresentative_pin,
    completedRealSmul_congr hw0 hw1 _ _ _ D.cauchy (approximationReal_equiv D)]
  rfl

def realRadius (X : (PD).Cauchy) (epsilon : Q') : Q' :=
  HalfPow.half*meshRadius hw0 hw1 X epsilon

theorem realRadius_positive (X : (PD).Cauchy) (epsilon : Q') :
    (0 : Q')<realRadius hw0 hw1 X epsilon :=
  ExpNeg.half_mul_pos _ (meshRadius_positive hw0 hw1 X epsilon)

/-- Every supplied small positive REAL increment, with the time-squared factor retained. -/
theorem real_taylor_bound (X : (PD).Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (D : PositiveTime)
    (ht : RCle (realValue (timeValue D)) (rat (realRadius hw0 hw1 X epsilon))) :
    RCle (B (realRemainder hw0 hw1 D (Class X)) (realRemainder hw0 hw1 D (Class X)))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon)) := by
  have htime : Quotient.mk crealSetoid (approximationReal D)=realValue (timeValue D) :=
    Quotient.sound (approximationReal_equiv D)
  have hap : RCle (Quotient.mk crealSetoid (approximationReal D))
      (rat (realRadius hw0 hw1 X epsilon)) := by
    rw [htime]
    exact ht
  change leEv (approximationReal D) (ofQ' (realRadius hw0 hw1 X epsilon)) at hap
  obtain ⟨N,hN⟩ := hap (realRadius hw0 hw1 X epsilon) (realRadius_positive hw0 hw1 X epsilon)
  have hsmall (n : Nat) (hn : N≤n) : value (approximation D n)≤meshRadius hw0 hw1 X epsilon :=
    Q'.le_trans' _ _ _ (hN n hn)
      (Q'.le_of_eqv (ExpNeg.two_halves (meshRadius hw0 hw1 X epsilon)))
  let R := remainderRows hw0 hw1 D X
  have hleft := pairing_converges hw0 hw1 R R
  have hright : ConvergesTo
      (fun n => CReal.mul (CReal.mul (ofQ' (value (approximation D n)))
        (ofQ' (value (approximation D n)))) (ofQ' epsilon))
      (CReal.mul (CReal.mul (approximationReal D) (approximationReal D)) (ofQ' epsilon)) :=
    convergesTo_mul_general
      (convergesTo_mul_general (convergesTo_self (approximationReal D))
        (convergesTo_self (approximationReal D))) (convergesTo_const _)
  have h := limit_le_of_eventual hleft hright N (by
    intro n hn
    change RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 R n))
      (rat ((value (approximation D n)*value (approximation D n))*epsilon))
    rw [show R=remainderRows hw0 hw1 D X from rfl,remainderRows_pin]
    exact mesh_taylor_bound hw0 hw1 X epsilon he
      (approximation D n).depth (approximation D n).steps (hsmall n hn))
  change RCle (B (limit hw0 hw1 R) (limit hw0 hw1 R))
    (RCmul (RCmul (Quotient.mk crealSetoid (approximationReal D))
      (Quotient.mk crealSetoid (approximationReal D))) (rat epsilon)) at h
  rw [show R=remainderRows hw0 hw1 D X from rfl,remainderRows_limit,htime] at h
  exact h

def realTaylorCertificate (X : (PD).Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' radius : Q', ((0 : Q')<radius) ×'
      (∀ D : PositiveTime, RCle (realValue (timeValue D)) (rat radius) →
        RCle (B (realRemainder hw0 hw1 D (Class X)) (realRemainder hw0 hw1 D (Class X)))
          (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon))) :=
  ⟨realRadius hw0 hw1 X epsilon,realRadius_positive hw0 hw1 X epsilon,
    fun D ht => real_taylor_bound hw0 hw1 X epsilon he D ht⟩

#print axioms pairing_converges
#print axioms derivativeRepresentative
#print axioms derivativeRepresentative_pin
#print axioms realRemainder
#print axioms realRemainder_time_congr
#print axioms remainderRows
#print axioms remainderRows_pin
#print axioms remainderRows_limit
#print axioms realRadius
#print axioms realRadius_positive
#print axioms real_taylor_bound
#print axioms realTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeRealDerivative
