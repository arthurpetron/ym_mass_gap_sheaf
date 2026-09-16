/-
# Odd response is bounded by the preceding even response on the SAME carrier

Positivity of the actual difference x-Tx and original time contraction give
2 B(x,Tx) <= N(x)+N(Tx) <= 2 N(x). Rational halving and time balance then
give B(v,T_(2n+1)v) <= B(v,T_(2n)v) on the existing spatial union completion.

The immediate consumer is the corrected positive-response comparison: the old
bond-reflected plaquette response has physical separation THREE. A lower floor
transported to union lag three therefore supplies the same floor at lag two.
The required transport between the two original finite-action exhaustions is
not proved here. Neither positivity of one-step time nor a continuum claim is
assumed or concluded.
-/

import YMGap.Continuum.BF4SpatialUnionCompletedDistance
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4SpatialUnionOddEvenResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionCompletedDistance
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem midpoint_cancel (a b c : RC) :
    RCadd (RCadd b b) (RCsub (RCsub a b) (RCsub b c)) = RCadd a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 1))
        (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2))))))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem half_double (a : RC) : RCscale HalfPow.half (RCadd a a) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (A.approx n) (A.approx n))
      (ExpNeg.two_halves (A.approx n))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "Sub" => completedSub hw0 hw1 hsmall hd hs

/-- Original physical time is norm-contracting on every completed vector. -/
theorem completedTime_norm_le (n : Nat) (x : V) :
    RCle (B (T n x) (T n x)) (B x x) := by
  have hz : T n Z = Z := by
    apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
    intro y
    rw [completedInner_time_balance, completedInner_zero_left, completedInner_zero_left]
  have h := completedDist_time_contraction hw0 hw1 hsmall hd hs n x Z
  simp only [completedDist, hz, completedSub_zero] at h
  exact h

/-- Difference positivity supplies a signed form bound; no positivity of T_n. -/
theorem completedTime_form_le (n : Nat) (x : V) :
    RCle (B x (T n x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (RCadd (B x (T n x)) (B x (T n x))))
    (completedInner_nonnegative hw0 hw1 hsmall hd hs (Sub x (T n x)))
  rw [rc_add_zero, completedInner_sub_left, completedInner_sub_right,
    completedInner_sub_right, completedInner_symm hw0 hw1 hsmall hd hs (T n x) x,
    midpoint_cancel] at h
  have hdouble := RCle_trans h (RCadd_le_add (RCle_refl (B x x))
    (completedTime_norm_le hw0 hw1 hsmall hd hs n x))
  have hhalf := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) hdouble
  simpa only [half_double] using hhalf

/-- An odd-time moment never exceeds the preceding even-time moment. -/
theorem odd_response_le_even (n : Nat) (x : V) :
    RCle (B x (T (2*n+1) x)) (B x (T (2*n) x)) := by
  have h := completedTime_form_le hw0 hw1 hsmall hd hs 1 (T n x)
  rw [completedInner_time_balance, completedInner_time_balance,
    ← completedTime_add, ← completedTime_add, ← completedTime_add] at h
  simpa only [Nat.add_assoc, show n+(1+n) = 2*n+1 by omega,
    show n+n = 2*n by omega] using h

/-- A supplied lower floor at physical lag three transfers without loss to lag two. -/
theorem lagTwo_floor_of_lagThree (x : V) (floor : RC)
    (hfloor : RCle floor (B x (T 3 x))) : RCle floor (B x (T 2 x)) :=
  RCle_trans hfloor (odd_response_le_even hw0 hw1 hsmall hd hs 1 x)

end YMGap.Continuum.BF4SpatialUnionOddEvenResponse

#print axioms YMGap.Continuum.BF4SpatialUnionOddEvenResponse.completedTime_norm_le
#print axioms YMGap.Continuum.BF4SpatialUnionOddEvenResponse.completedTime_form_le
#print axioms YMGap.Continuum.BF4SpatialUnionOddEvenResponse.odd_response_le_even
#print axioms YMGap.Continuum.BF4SpatialUnionOddEvenResponse.lagTwo_floor_of_lagThree
