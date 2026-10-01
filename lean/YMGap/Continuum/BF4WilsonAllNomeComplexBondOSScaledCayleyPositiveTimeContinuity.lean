/-
# Source-dependent continuity of actual positive-real Cayley time

The original supplied physical Rows compute the rational Cayley parameter
radius. Two close ACTUAL numerical time values have eventually close raw
rational samples: the pre-existing numerical order lemma handles their real
values, while the supplied dyadic approximation bound and a computed
half-power cutoff handle the raw samples. The original rational parameter
estimate and both constructed time-limit rates then control the SAME squared
physical distance. Logical eventual-order witnesses are used only within a
proof of a bound; the public radius is Type-level data computed from Rows.

This is fixed nome and width. It asserts no signed-time group, generator,
physical-clock calibration, continuum survival, or Yang--Mills mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeAddition
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime sample approximation approximation_error)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue realValue)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity
  (time_close_eventually)
open YMGap.Continuum.RegularLinearGeometricModulus
  (halfCutoff halfCutoff_spec)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (sample_positive timeRows timeRows_pin timeLimitRows timeLimitRate timeLimit_bound
    positiveAction positiveAction_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction positiveRealAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeAddition
  (tolerance tolerance_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
  (radius radius_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity
  (parameter_close_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle distance_symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def oneSixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- One source-computed radius works for any TWO actual positive-real times.
The extra sixteenth reserves room for numerical-order slack and dyadic mesh
rounding before the original rational parameter radius is used. -/
def parameterDelta (X : R) (e : Q') (he : (0 : Q') < e) : Q' :=
  oneSixteenth * radius hw0 hw1 X (tolerance e) (tolerance_positive e he)

theorem parameterDelta_positive (X : R) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < parameterDelta hw0 hw1 X e he :=
  Q'.mul_pos (by decide)
    (radius_positive hw0 hw1 X (tolerance e) (tolerance_positive e he))

private theorem three_delta_within_radius (a r : Q') (hr : (0 : Q') ≤ r) :
    (a + oneSixteenth*r) + ((oneSixteenth*r) + (oneSixteenth*r)) ≤ a+r := by
  let c := oneSixteenth
  have hc : 3*c ≤ (1 : Q') := by decide
  have hmul : (3*c)*r ≤ (1 : Q')*r :=
    Q'.mul_le_mul_of_nonneg_right _ _ r hc hr
  have hthree : 3*(c*r) ≤ r :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv r)))
  have hform : Q'.eqv ((a+c*r)+((c*r)+(c*r))) (a+3*(c*r)) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 1)))
      (.add (.var 0) (.mul (.const 3) (.var 1)))
      (by decide) (fun | 0 => a | _ => c*r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hform)
    (Q'.add_le_add_left a _ _ hthree)

/-- A numerical-only adapter: actual RC time-value order, the EXISTING
dyadic approximation error, and a computed half-power cutoff imply eventual
closeness of the raw samples consumed by the Wilson Cayley map. No physical
legacy carrier is transported. -/
private theorem raw_samples_close_eventually (s t : PositiveTime) (r : Q')
    (hr : (0 : Q') < r)
    (hst : RCle (realValue (timeValue s))
      (RCadd (realValue (timeValue t)) (rat (oneSixteenth*r)))) :
    ∃ N : Nat, ∀ n, N ≤ n → sample s n ≤ sample t n+r := by
  let d := oneSixteenth*r
  have hd : (0 : Q') < d := Q'.mul_pos (by decide) hr
  obtain ⟨N,hN⟩ := time_close_eventually s t d hd hst
  refine ⟨max N (halfCutoff d),fun n hn => ?_⟩
  have hnN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnCut : halfCutoff d ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hpow : HalfPow.half^n ≤ d :=
    Q'.le_trans' _ _ _ (half_pow_antitone _ n hnCut)
      (halfCutoff_spec d hd)
  have happrox : value (approximation t n) ≤ sample t n+d :=
    Q'.le_trans' _ _ _ (approximation_error t n).2
      (Q'.add_le_add_left _ _ _ hpow)
  have hshift := Q'.add_le_add_right _ _ (d+d) happrox
  have hraw : sample s n ≤ (sample t n+d)+(d+d) :=
    Q'.le_trans' _ _ _ (approximation_error s n).1
      (Q'.le_trans' _ _ _ (hN n hnN) hshift)
  exact Q'.le_trans' _ _ _ hraw
    (three_delta_within_radius (sample t n) r (Q'.le_of_lt hr))

private theorem rational_bound {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro d hd
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b d (Q'.le_of_lt hd))⟩

private theorem tolerance_budget (e : Q') (he : (0 : Q') < e) :
    10*tolerance e ≤ e := by
  have hc : 10*(Q'.mkPos 1 16 (by decide)) ≤ (1 : Q') := by decide
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ e hc (Q'.le_of_lt he)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv e)))

/-- Two original time-limit errors and one rational-parameter error cost ten
copies of the chosen tolerance in squared physical distance. -/
private theorem three_physical_bridges (a b c d : H) (q : Q')
    (hab : RCle (D a b) (rat q))
    (hbc : RCle (D b c) (rat q))
    (hcd : RCle (D c d) (rat q)) :
    RCle (D a d) (rat (10*q)) := by
  have hinner := RCle_trans (distance_triangle hw0 hw1 b c d)
    (RCadd_le_add (RCadd_le_add hbc hbc) (RCadd_le_add hcd hcd))
  have houter := RCle_trans (distance_triangle hw0 hw1 a b d)
    (RCadd_le_add (RCadd_le_add hab hab) (RCadd_le_add hinner hinner))
  have hcoeff : RCadd (RCadd (rat q) (rat q))
      (RCadd
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))) =
      rat (10*q) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0))
          (.add
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))))
        (.mul (.const 10) (.var 0)) (by decide) (fun _ => q)))
  rwa [hcoeff] at houter

/-- TWO positive times close as actual RC values act closely on the SAME
original Rows class. Both original source-dependent time-limit rates are
retained; there is no assumed bound on all samples. -/
theorem positiveAction_parameter_close_ofRows (s t : PositiveTime)
    (X : R) (e : Q') (he : (0 : Q') < e)
    (hst : RCle (realValue (timeValue s))
      (RCadd (realValue (timeValue t)) (rat (parameterDelta hw0 hw1 X e he))))
    (hts : RCle (realValue (timeValue t))
      (RCadd (realValue (timeValue s)) (rat (parameterDelta hw0 hw1 X e he)))) :
    RCle (D (positiveAction hw0 hw1 s (ofRows hw0 hw1 X))
        (positiveAction hw0 hw1 t (ofRows hw0 hw1 X))) (rat e) := by
  let q := tolerance e
  have hq : (0 : Q') < q := tolerance_positive e he
  let r := radius hw0 hw1 X q hq
  have hr : (0 : Q') < r := radius_positive hw0 hw1 X q hq
  obtain ⟨Ns,hNs⟩ := raw_samples_close_eventually s t r hr hst
  obtain ⟨Nt,hNt⟩ := raw_samples_close_eventually t s r hr hts
  let n := max (max Ns Nt)
    (max (timeLimitRate hw0 hw1 s X q) (timeLimitRate hw0 hw1 t X q))
  have hns : Ns ≤ n := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hnt : Nt ≤ n := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hrateS : timeLimitRate hw0 hw1 s X q ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrateT : timeLimitRate hw0 hw1 t X q ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hs : RCle
      (D (positiveAction hw0 hw1 s (ofRows hw0 hw1 X))
        (ofRows hw0 hw1 (timeRows hw0 hw1 s X n))) (rat q) := by
    rw [positiveAction_ofRows,distance_symm]
    exact timeLimit_bound hw0 hw1 s X q hq n hrateS
  have ht : RCle
      (D (ofRows hw0 hw1 (timeRows hw0 hw1 t X n))
        (positiveAction hw0 hw1 t (ofRows hw0 hw1 X))) (rat q) := by
    rw [positiveAction_ofRows]
    exact timeLimit_bound hw0 hw1 t X q hq n hrateT
  have hmiddle : RCle
      (D (ofRows hw0 hw1 (timeRows hw0 hw1 s X n))
        (ofRows hw0 hw1 (timeRows hw0 hw1 t X n))) (rat q) := by
    rw [timeRows_pin,timeRows_pin]
    exact parameter_close_bound hw0 hw1 X q hq
      (sample s n) (sample t n) (sample_positive s n) (sample_positive t n)
      (hNs n hns) (hNt n hnt)
  exact RCle_trans
    (three_physical_bridges hw0 hw1 _ _ _ _ q hs hmiddle ht)
    (rational_bound (tolerance_budget e he))

/-- Quotient-facing continuity depends only on ACTUAL positive-real time
values, not their Cauchy presentations. -/
theorem positiveRealAction_parameter_close_ofRows (s t : PositiveTimeValue)
    (X : R) (e : Q') (he : (0 : Q') < e)
    (hst : RCle (realValue s)
      (RCadd (realValue t) (rat (parameterDelta hw0 hw1 X e he))))
    (hts : RCle (realValue t)
      (RCadd (realValue s) (rat (parameterDelta hw0 hw1 X e he)))) :
    RCle (D (positiveRealAction hw0 hw1 s (ofRows hw0 hw1 X))
        (positiveRealAction hw0 hw1 t (ofRows hw0 hw1 X))) (rat e) := by
  revert hst hts
  refine Quotient.inductionOn₂ s t ?_
  intro S T hST hTS
  exact positiveAction_parameter_close_ofRows hw0 hw1 S T X e he hST hTS

/-- Type-level source-computed time radius and the original physical bound;
only the logical EVENTUAL order witnesses are erased. -/
def parameterContinuityCertificate (X : R) (e : Q') (he : (0 : Q') < e) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ s t : PositiveTimeValue,
        RCle (realValue s) (RCadd (realValue t) (rat delta)) →
        RCle (realValue t) (RCadd (realValue s) (rat delta)) →
        RCle (D (positiveRealAction hw0 hw1 s (ofRows hw0 hw1 X))
          (positiveRealAction hw0 hw1 t (ofRows hw0 hw1 X))) (rat e)) :=
  ⟨parameterDelta hw0 hw1 X e he,parameterDelta_positive hw0 hw1 X e he,
    fun s t hst hts =>
      positiveRealAction_parameter_close_ofRows hw0 hw1 s t X e he hst hts⟩

#print axioms parameterDelta
#print axioms parameterDelta_positive
#print axioms positiveAction_parameter_close_ofRows
#print axioms positiveRealAction_parameter_close_ofRows
#print axioms parameterContinuityCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeContinuity
