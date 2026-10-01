/-
# Numerical presentation independence of original positive Cayley time

Equivalent constructive-real times give the same action on the original
completed Wilson bond.  The equivalence witness is eliminated only in the
proof of equality; the action and all its limit rates were constructed from
the supplied Type-level numerical Cauchy data in `PositiveTime`.

This is fixed-nome, fixed-width time indexing, not a physical clock or a
continuum Hamiltonian identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
import YMGap.Continuum.CRealSeminormCauchyRows
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime sample half_chain rational)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue timeSetoid)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows rowState value value_injective value_ofRows
    distance distance_value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (sample_positive timeRows timeRows_pin timeLimitRows timeLimitRate timeLimit_bound
    positiveAction positiveAction_ofRows positiveAction_rational)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
  (radius radius_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity
  (parameter_close_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle distance_symm)
open YMGap.Continuum.BF4WilsonAllNomeComplexTimeSector
  (distance_fst_le distance_snd_le)
open YMGap.Continuum.BF4WilsonAllNomeDistance (distanceData)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

/-- A comparison modulus is used only inside the proposition proving
presentation equality.  No computational rate is extracted from `Equiv`. -/
private theorem sample_close (time other : PositiveTime)
    (h : Equiv time.real other.real) (r : Q') (hr : (0 : Q') < r) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      sample time n ≤ sample other n + r ∧
      sample other n ≤ sample time n + r := by
  let d := HalfPow.half*r
  have hd : (0 : Q') < d := ExpNeg.half_mul_pos r hr
  obtain ⟨N,hN⟩ := h d hd
  refine ⟨max N (other.cauchy.M d),fun n hn => ?_⟩
  have hnN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnM : other.cauchy.M d ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have heq := hN (time.start+n) (Nat.le_trans hnN (Nat.le_add_left _ _))
  have hc := other.cauchy.bound d hd (time.start+n) (other.start+n)
    (Nat.le_trans hnM (Nat.le_add_left _ _))
    (Nat.le_trans hnM (Nat.le_add_left _ _))
  exact ⟨half_chain _ _ _ r heq.1 hc.1,
    half_chain _ _ _ r hc.2 heq.2⟩

private theorem three_samples (a b c d : H) (q : Q')
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
        (.mul (.const 10) (.var 0))
        (by decide) (fun _ => q)))
  rwa [hcoeff] at houter

private theorem ten_sixteenths (e : Q') (he : (0 : Q') < e) :
    10*((Q'.mkPos 1 16 (by decide))*e) ≤ e := by
  let c : Q' := Q'.mkPos 1 16 (by decide)
  have hcoeff : 10*c ≤ (1 : Q') := by decide
  have hleft : Q'.eqv (10*(c*e)) ((10*c)*e) :=
    poly_identity_of_normal_eq
      (.mul (.const 10) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 10) (.var 0)) (.var 1))
      (by decide) (fun | 0 => c | _ => e)
  have hright : Q'.eqv ((1 : Q')*e) e := Q'.one_mul_eqv e
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ e hcoeff (Q'.le_of_lt he))
      (Q'.le_of_eqv hright))

/-- Definiteness of the SAME two-component original completed distance. -/
private theorem rows_eq_of_distance_small (X Y : R)
    (h : ∀ e : Q', (0 : Q') < e →
      RCle (D (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y)) (rat e)) :
    ofRows hw0 hw1 X = ofRows hw0 hw1 Y := by
  apply value_injective hw0 hw1
  rw [value_ofRows,value_ofRows]
  apply Prod.ext
  · apply CRealSeminormCauchyRows.completed_eq_of_small
      (distanceData hw0 hw1 (width := width))
    intro e he
    have hf := distance_fst_le hw0 hw1 (rowState hw0 hw1 X) (rowState hw0 hw1 Y)
    have hs := h e he
    rw [distance_value,value_ofRows,value_ofRows] at hs
    exact RCle_trans hf hs
  · apply CRealSeminormCauchyRows.completed_eq_of_small
      (distanceData hw0 hw1 (width := width))
    intro e he
    have hf := distance_snd_le hw0 hw1 (rowState hw0 hw1 X) (rowState hw0 hw1 Y)
    have hs := h e he
    rw [distance_value,value_ofRows,value_ofRows] at hs
    exact RCle_trans hf hs

/-- The original physical Cayley positive-time action depends only on the
supplied numerical constructive real, not its floor or starting index. -/
theorem positiveAction_time_congr (time other : PositiveTime)
    (h : Equiv time.real other.real) (x : H) :
    positiveAction hw0 hw1 time x = positiveAction hw0 hw1 other x := by
  rcases x with ⟨u,v⟩
  refine Quotient.inductionOn₂ u v ?_
  intro X Y
  let Z : R := (X,Y)
  change positiveAction hw0 hw1 time (ofRows hw0 hw1 Z) =
    positiveAction hw0 hw1 other (ofRows hw0 hw1 Z)
  rw [positiveAction_ofRows,positiveAction_ofRows]
  apply rows_eq_of_distance_small hw0 hw1
  intro e he
  let c : Q' := Q'.mkPos 1 16 (by decide)
  let q : Q' := c*e
  have hq : (0 : Q') < q := Q'.mul_pos (by decide) he
  let r := radius hw0 hw1 Z q hq
  have hr : (0 : Q') < r := radius_positive hw0 hw1 Z q hq
  obtain ⟨N,hN⟩ := sample_close time other h r hr
  let n := max (max (timeLimitRate hw0 hw1 time Z q)
    (timeLimitRate hw0 hw1 other Z q)) N
  have hnT : timeLimitRate hw0 hw1 time Z q ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hnO : timeLimitRate hw0 hw1 other Z q ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hnN : N ≤ n := Nat.le_max_right _ _
  have hleft := timeLimit_bound hw0 hw1 time Z q hq n hnT
  have hright := timeLimit_bound hw0 hw1 other Z q hq n hnO
  have hmiddle := parameter_close_bound hw0 hw1 Z q hq
    (sample time n) (sample other n)
    (sample_positive time n) (sample_positive other n)
    (hN n hnN).1 (hN n hnN).2
  rw [distance_symm] at hleft
  have hthree := three_samples hw0 hw1
    (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Z))
    (ofRows hw0 hw1 (timeRows hw0 hw1 time Z n))
    (ofRows hw0 hw1 (timeRows hw0 hw1 other Z n))
    (ofRows hw0 hw1 (timeLimitRows hw0 hw1 other Z))
    q hleft (by simpa only [timeRows_pin] using hmiddle) hright
  exact RCle_trans hthree (rat_le (ten_sixteenths e he))

/-- Quotient by the already defined numerical positive-time setoid. -/
def positiveRealAction (t : PositiveTimeValue) (x : H) : H :=
  Quotient.lift (fun time => positiveAction hw0 hw1 time x)
    (fun time other h => positiveAction_time_congr hw0 hw1 time other h x) t

theorem positiveRealAction_pin (time : PositiveTime) (x : H) :
    positiveRealAction hw0 hw1 (timeValue time) x =
      positiveAction hw0 hw1 time x := rfl

theorem positiveRealAction_rational (q : Q') (hq : (0 : Q') < q) (x : H) :
    positiveRealAction hw0 hw1 (timeValue (rational q hq)) x =
      BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 q hq x :=
  positiveAction_rational hw0 hw1 q hq x

#print axioms positiveAction_time_congr
#print axioms positiveRealAction
#print axioms positiveRealAction_pin
#print axioms positiveRealAction_rational

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
