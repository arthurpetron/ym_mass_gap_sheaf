/-
# Euclidean action commutes with the original physical Cayley graph

The constructed original positive-time action transports every witnessed
physical derivative-domain class.  Its actual linearity therefore transports
both imaginary shifts and commutes with the finite scaled Cayley map on the
SAME complex Wilson bond completion.  This is not a physical-time calibration
or a continuum generator identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivativeTime
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
import YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub bondValue_smul bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
  (positiveAction_add positiveAction_sub positiveAction_smul positiveAction_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivativeTime
  (timeDomain realTimeDomain_input realTimeDomain_output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts
  (plus minus plusDomain plus_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayley
  (cayley plus_left)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BF4WilsonAllNomeBondOSCompletion.BondCompletion
  hw0 hw1 (width := width)
local notation "H" => BF4WilsonAllNomeComplexBondOSCompletion.ComplexBondCompletion
  hw0 hw1 (width := width)
local notation "D" => BF4WilsonAllNomeComplexBondOSDerivative.Domain
  hw0 hw1 (width := width)
local notation "RS" => BF4WilsonAllNomeBondOSRealTime.action hw0 hw1
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
local notation "RAdd" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "RSub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "RScale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "RRealScale" => BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1
local notation "RIn" => BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
local notation "ROut" => BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
local notation "RTD" => BF4WilsonAllNomeComplexBondOSDerivativeTime.realTimeDomain hw0 hw1

private theorem real_action_add (s : PositiveTime) (x y : RH) :
    RS (timeValue s) (RAdd x y) =
      RAdd (RS (timeValue s) x) (RS (timeValue s) y) := by
  apply bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSRealTime.action_value,bondValue_add,realTimeAction_pin,
    positiveAction_add,bondValue_add,
    BF4WilsonAllNomeBondOSRealTime.action_value,
    BF4WilsonAllNomeBondOSRealTime.action_value,realTimeAction_pin,realTimeAction_pin]

private theorem real_action_sub (s : PositiveTime) (x y : RH) :
    RS (timeValue s) (RSub x y) =
      RSub (RS (timeValue s) x) (RS (timeValue s) y) := by
  apply bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSRealTime.action_value,bondValue_sub,realTimeAction_pin,
    positiveAction_sub,bondValue_sub,
    BF4WilsonAllNomeBondOSRealTime.action_value,
    BF4WilsonAllNomeBondOSRealTime.action_value,realTimeAction_pin,realTimeAction_pin]

private theorem real_action_smul (s : PositiveTime) (a : Q') (x : RH) :
    RS (timeValue s) (RScale a x) =
      RScale a (RS (timeValue s) x) := by
  apply bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSRealTime.action_value,bondValue_smul,realTimeAction_pin,
    positiveAction_smul,bondValue_smul,
    BF4WilsonAllNomeBondOSRealTime.action_value,realTimeAction_pin]

private theorem real_action_realSmul (s : PositiveTime) (a : CReal)
    (ca : QCauchy a.approx) (x : RH) :
    RS (timeValue s) (RRealScale a ca x) =
      RRealScale a ca (RS (timeValue s) x) := by
  apply bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSRealTime.action_value,bondValue_realSmul,realTimeAction_pin,
    positiveAction_realSmul,bondValue_realSmul,
    BF4WilsonAllNomeBondOSRealTime.action_value,realTimeAction_pin]

/-- Original Euclidean action preserves complex addition on the physical bond. -/
theorem action_add (s : PositiveTime) (x y : H) :
    S (timeValue s) (BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 x y) =
      BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
        (S (timeValue s) x) (S (timeValue s) y) :=
  Prod.ext (real_action_add hw0 hw1 s x.1 y.1)
    (real_action_add hw0 hw1 s x.2 y.2)

/-- Both supplied constructive scalar moduli survive Euclidean action. -/
theorem action_smul (s : PositiveTime) (a b : CReal)
    (ca : QCauchy a.approx) (cb : QCauchy b.approx) (x : H) :
    S (timeValue s) (BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 a b ca cb x) =
      BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 a b ca cb
        (S (timeValue s) x) := by
  apply Prod.ext
  · change RS (timeValue s) (RSub (RRealScale a ca x.1) (RRealScale b cb x.2)) =
      RSub (RRealScale a ca (RS (timeValue s) x.1))
        (RRealScale b cb (RS (timeValue s) x.2))
    rw [real_action_sub,real_action_realSmul,real_action_realSmul]
  · change RS (timeValue s) (RAdd (RRealScale b cb x.1) (RRealScale a ca x.2)) =
      RAdd (RRealScale b cb (RS (timeValue s) x.1))
        (RRealScale a ca (RS (timeValue s) x.2))
    rw [real_action_add,real_action_realSmul,real_action_realSmul]

/-- The actual transported graph carries the plus imaginary shift. -/
theorem plus_timeDomain (t : Q') (s : PositiveTime) (d : D) :
    plus hw0 hw1 t (timeDomain hw0 hw1 s d) =
      S (timeValue s) (plus hw0 hw1 t d) := by
  apply Prod.ext
  · change RSub (RIn (RTD s d.1)) (RScale t (ROut (RTD s d.2))) =
      RS (timeValue s) (RSub (RIn d.1) (RScale t (ROut d.2)))
    rw [realTimeDomain_input,realTimeDomain_output,real_action_sub,real_action_smul]
  · change RAdd (RIn (RTD s d.2)) (RScale t (ROut (RTD s d.1))) =
      RS (timeValue s) (RAdd (RIn d.2) (RScale t (ROut d.1)))
    rw [realTimeDomain_input,realTimeDomain_output,real_action_add,real_action_smul]

/-- The actual transported graph carries the minus imaginary shift. -/
theorem minus_timeDomain (t : Q') (s : PositiveTime) (d : D) :
    minus hw0 hw1 t (timeDomain hw0 hw1 s d) =
      S (timeValue s) (minus hw0 hw1 t d) := by
  apply Prod.ext
  · change RAdd (RIn (RTD s d.1)) (RScale t (ROut (RTD s d.2))) =
      RS (timeValue s) (RAdd (RIn d.1) (RScale t (ROut d.2)))
    rw [realTimeDomain_input,realTimeDomain_output,real_action_add,real_action_smul]
  · change RSub (RIn (RTD s d.2)) (RScale t (ROut (RTD s d.1))) =
      RS (timeValue s) (RSub (RIn d.2) (RScale t (ROut d.1)))
    rw [realTimeDomain_input,realTimeDomain_output,real_action_sub,real_action_smul]

/-- The finite Cayley map and the original Euclidean action commute on
EVERY physical complex bond class, using the same maximal graph. -/
theorem cayley_action_commute (t : Q') (ht : (0 : Q') < t)
    (s : PositiveTime) (x : H) :
    cayley hw0 hw1 t ht (S (timeValue s) x) =
      S (timeValue s) (cayley hw0 hw1 t ht x) := by
  let d := plusDomain hw0 hw1 t ht x
  have hp : plus hw0 hw1 t (timeDomain hw0 hw1 s d) = S (timeValue s) x := by
    rw [plus_timeDomain,plus_right]
  have hd : plusDomain hw0 hw1 t ht (S (timeValue s) x) =
      timeDomain hw0 hw1 s d := by
    calc
      plusDomain hw0 hw1 t ht (S (timeValue s) x) =
          plusDomain hw0 hw1 t ht (plus hw0 hw1 t (timeDomain hw0 hw1 s d)) :=
        congrArg (plusDomain hw0 hw1 t ht) hp.symm
      _ = timeDomain hw0 hw1 s d := plus_left hw0 hw1 t ht _
  unfold cayley
  rw [hd]
  exact minus_timeDomain hw0 hw1 t s d

/-- Every finite original Cayley power retains the same Euclidean symmetry. -/
theorem iterate_action_commute (t : Q') (ht : (0 : Q') < t)
    (s : PositiveTime) (x : H) (n : Nat) :
    BF4WilsonAllNomeComplexBondOSScaledCayleyRows.iterate hw0 hw1 t ht
        (S (timeValue s) x) n =
      S (timeValue s)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyRows.iterate hw0 hw1 t ht x n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change cayley hw0 hw1 t ht
          (BF4WilsonAllNomeComplexBondOSScaledCayleyRows.iterate hw0 hw1 t ht
            (S (timeValue s) x) n) =
        S (timeValue s)
          (cayley hw0 hw1 t ht
            (BF4WilsonAllNomeComplexBondOSScaledCayleyRows.iterate hw0 hw1 t ht x n))
      rw [ih,cayley_action_commute]

#print axioms action_add
#print axioms action_smul
#print axioms plus_timeDomain
#print axioms minus_timeDomain
#print axioms cayley_action_commute
#print axioms iterate_action_commute

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanCommutation
