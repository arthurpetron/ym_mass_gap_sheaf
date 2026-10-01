/-
# Addition of constructed original positive-real Cayley time

The existing numerical sum-time samples use upward dyadic rounding.
An explicit half-power cutoff bounds their discrepancy from the sum of
the two original raw samples. Actual rational addition/isometry and the
two ORIGINAL forward time-limit rates then identify the sum-time limit
with composition on the SAME completed physical Wilson bond.

All comparison rates are computed from supplied time data and original
Rows. No continuity, group law, quotient representative, physical spacing
or continuum Hamiltonian is assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeAddition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime sample approximation_error)
open YMGap.Continuum.PositiveRealDyadicTimeAddition
  (sumTime sumTime_sample sumSample half_sum_bound)
open YMGap.Continuum.RegularLinearGeometricModulus (halfCutoff halfCutoff_spec)
open YMGap.Continuum (half_pow_antitone)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (PositiveTimeValue)
-- Reuse only numerical time addition, never the legacy operator/carrier.
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup
  (addTime addTime_comm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (sample_positive parameterRadius parameterRadius_pin timeRows timeRows_pin
    timeSequence timeLimitRows timeLimitRate timeLimit_bound positiveAction positiveAction_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap rows_limit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitAddition
  (limitMap_add_parameter limitMap_commute)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
  (limitMap_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity
  (parameter_close_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
  (radius radius_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit (distance_triangle)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Only upward rounding is compared; no numerical Cauchy rate is needed. -/
theorem sum_sample_close (s t : PositiveTime) (r : Q') (hr : (0 : Q') < r)
    (n : Nat) (hn : halfCutoff (HalfPow.half*r) ≤ n) :
    sample (sumTime s t) n ≤ (sample s n+sample t n)+r ∧
      sample s n+sample t n ≤ sample (sumTime s t) n+r := by
  have hpower : HalfPow.half^n ≤ HalfPow.half*r :=
    Q'.le_trans' _ _ _ (half_pow_antitone _ n hn)
      (halfCutoff_spec _ (ExpNeg.half_mul_pos r hr))
  have hs := approximation_error s n
  have ht := approximation_error t n
  have hs' := Q'.le_trans' _ _ _ hs.2 (Q'.add_le_add_left _ _ _ hpower)
  have ht' := Q'.le_trans' _ _ _ ht.2 (Q'.add_le_add_left _ _ _ hpower)
  rw [sumTime_sample]
  exact ⟨half_sum_bound _ _ _ _ r hs' ht',
    Q'.le_trans' _ _ _ (Q'.add_le_add hs.1 ht.1)
      (Q'.add_le_self_of_nonneg _ r (Q'.le_of_lt hr))⟩

def tolerance (e : Q') : Q' := (Q'.mkPos 1 16 (by decide))*e

theorem tolerance_positive (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < tolerance e := Q'.mul_pos (by decide) he

/-- Mesh alignment and BOTH original forward rates remain computable. -/
def additionRate (s t : PositiveTime) (X : R) (e : Q') : Nat :=
  max (halfCutoff (HalfPow.half*parameterRadius hw0 hw1 X (tolerance e)))
    (max (timeLimitRate hw0 hw1 t X (tolerance e))
      (timeLimitRate hw0 hw1 s (timeLimitRows hw0 hw1 t X) (tolerance e)))

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

private theorem three_bridge (a b c d : H) (q : Q')
    (hab : RCle (D a b) (rat q)) (hbc : RCle (D b c) (rat q))
    (hcd : RCle (D c d) (rat q)) : RCle (D a d) (rat (10*q)) := by
  have hi := RCle_trans (distance_triangle hw0 hw1 b c d)
    (RCadd_le_add (RCadd_le_add hbc hbc) (RCadd_le_add hcd hcd))
  have ho := RCle_trans (distance_triangle hw0 hw1 a b d)
    (RCadd_le_add (RCadd_le_add hab hab) (RCadd_le_add hi hi))
  have hc : RCadd (RCadd (rat q) (rat q))
      (RCadd
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))) = rat (10*q) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0))
          (.add
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))))
        (.mul (.const 10) (.var 0)) (by decide) (fun _ => q)))
  rwa [hc] at ho

private theorem tolerance_budget (e : Q') (he : (0 : Q') < e) :
    10*tolerance e ≤ e := by
  have hc : 10*(Q'.mkPos 1 16 (by decide)) ≤ (1 : Q') := by decide
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ e hc (Q'.le_of_lt he)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv e)))

/-- Actual sum-time samples converge to the actual two-stage original output.
No sum-time forward rate is needed in addition to these constructed rates. -/
theorem sum_composition_limit_bound (s t : PositiveTime) (X : R)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : additionRate hw0 hw1 s t X e ≤ n) :
    RCle (D (ofRows hw0 hw1 (timeRows hw0 hw1 (sumTime s t) X n))
      (ofRows hw0 hw1 (timeLimitRows hw0 hw1 s (timeLimitRows hw0 hw1 t X))))
      (rat e) := by
  let q := tolerance e
  have hq : (0 : Q') < q := tolerance_positive e he
  let Y := timeLimitRows hw0 hw1 t X
  let a := sample s n
  let b := sample t n
  have ha : (0 : Q') < a := sample_positive s n
  have hb : (0 : Q') < b := sample_positive t n
  have hmesh : halfCutoff (HalfPow.half*radius hw0 hw1 X q hq) ≤ n := by
    have h := Nat.le_trans (Nat.le_max_left _ _) hn
    change halfCutoff (HalfPow.half*parameterRadius hw0 hw1 X q) ≤ n at h
    rwa [parameterRadius_pin hw0 hw1 X q hq] at h
  have hnumeric := sum_sample_close s t (radius hw0 hw1 X q hq)
    (radius_positive hw0 hw1 X q hq) n hmesh
  have hfirst := parameter_close_bound hw0 hw1 X q hq
    (sample (sumTime s t) n) (a+b) (sample_positive (sumTime s t) n)
    (Q'.add_pos ha hb) hnumeric.1 hnumeric.2
  have hinner := timeLimit_bound hw0 hw1 t X q hq n
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hn))
  rw [timeRows_pin] at hinner
  have hsecond : RCle
      (D (F (a+b) (Q'.add_pos ha hb) (ofRows hw0 hw1 X))
        (F a ha (ofRows hw0 hw1 Y))) (rat q) := by
    rw [limitMap_add_parameter hw0 hw1 a b ha hb,
      limitMap_commute hw0 hw1 a b ha hb,limitMap_distance]
    exact hinner
  have hthird := timeLimit_bound hw0 hw1 s Y q hq n
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hn))
  rw [timeRows_pin] at hthird
  rw [timeRows_pin]
  exact RCle_trans (three_bridge hw0 hw1 _ _ _ _ q hfirst hsecond hthird)
    (rat_le (tolerance_budget e he))

theorem positiveAction_sum_ofRows (s t : PositiveTime) (X : R) :
    positiveAction hw0 hw1 (sumTime s t) (ofRows hw0 hw1 X) =
      positiveAction hw0 hw1 s (positiveAction hw0 hw1 t (ofRows hw0 hw1 X)) := by
  rw [positiveAction_ofRows,positiveAction_ofRows,positiveAction_ofRows]
  apply rows_limit_unique hw0 hw1 (timeSequence hw0 hw1 (sumTime s t) X)
    (timeLimitRows hw0 hw1 s (timeLimitRows hw0 hw1 t X))
    (additionRate hw0 hw1 s t X)
  intro e he n hn
  exact sum_composition_limit_bound hw0 hw1 s t X e he n hn

theorem positiveAction_sum (s t : PositiveTime) (x : H) :
    positiveAction hw0 hw1 (sumTime s t) x =
      positiveAction hw0 hw1 s (positiveAction hw0 hw1 t x) := by
  rcases x with ⟨u,v⟩
  refine Quotient.inductionOn₂ u v ?_
  intro X Y
  exact positiveAction_sum_ofRows hw0 hw1 s t (X,Y)

theorem positiveRealAction_addTime (s t : PositiveTimeValue) (x : H) :
    positiveRealAction hw0 hw1 (addTime s t) x =
      positiveRealAction hw0 hw1 s (positiveRealAction hw0 hw1 t x) := by
  refine Quotient.inductionOn₂ s t ?_
  intro S T
  exact positiveAction_sum hw0 hw1 S T x

theorem positiveRealAction_commute (s t : PositiveTimeValue) (x : H) :
    positiveRealAction hw0 hw1 s (positiveRealAction hw0 hw1 t x) =
      positiveRealAction hw0 hw1 t (positiveRealAction hw0 hw1 s x) := by
  rw [← positiveRealAction_addTime,← positiveRealAction_addTime,addTime_comm]

#print axioms sum_sample_close
#print axioms tolerance_positive
#print axioms additionRate
#print axioms sum_composition_limit_bound
#print axioms positiveAction_sum_ofRows
#print axioms positiveAction_sum
#print axioms positiveRealAction_addTime
#print axioms positiveRealAction_commute

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeAddition
