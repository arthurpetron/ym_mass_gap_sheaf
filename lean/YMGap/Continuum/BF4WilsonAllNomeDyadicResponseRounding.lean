/-
# Bounded integer-time rounding of the SAME normalized Wilson response

Positive actual mixed moments give
  0 <= R(n)-R(n+j) <= j/(n+1) * B(x,x).
For the constructed dyadic unit state, its norm is exactly one. At lags
n>=side(scale), every bounded offset therefore has a computed tolerance
modulus uniform in nome and width, without a relative-energy hypothesis.

This controls rounding within each SAME state and time operator. It does
not compare states across scales, prove zero-time continuity or survival,
or calibrate the assigned geometric spacing as physical Yang--Mills time.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicResponseRounding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.ContinuousTransferCalculus
open YMGap.Continuum.OSReconstructionProgress

local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem add_assoc (a b c : RC) :
    RCadd (RCadd a b) c = RCadd a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n)))

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem scale_add (a b : Q') (x : RC) :
    RCadd (RCscale a x) (RCscale b x) = RCscale (a+b) x := by
  refine Quotient.inductionOn x ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => (Q'.add_mul_eqv a b (X.approx n)).symm))

private theorem coefficient_succ (j : Nat) (c : Q') :
    Q'.eqv (c+Q'.ofNat j*c) (Q'.ofNat (j+1)*c) :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.var 1) (.var 0)))
      (.mul (.add (.var 1) (.const 1)) (.var 0))
      (by decide) (fun | 0 => c | _ => Q'.ofNat j))
    (Q'.mul_eqv_congr_right _ _ c (Q'.eqv_symm (Q'.ofNat_add_eqv j 1)))

private theorem scale_rational_one (q : Q') : RCscale q (Rq 1) = Rq q := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.mul_one_eqv q))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => mixedMoment hw0 hw1

/-- Exact actual response decreases along every finite integer shift. -/
theorem response_shift_decreasing (x : V) (n : Nat) : ∀ j : Nat,
    RCle (B x (T (n+j) x)) (B x (T n x))
  | 0 => RCle_refl _
  | j+1 => by
      simpa only [Nat.add_assoc, mixedMoment_zero] using RCle_trans
        (mixedMoment_time_decreasing hw0 hw1 x (n+j) 0)
        (response_shift_decreasing x n j)

/-- A bounded rounding error relative to the actual norm; no state or
analytic estimate is supplied in place of the ORIGINAL operator. -/
theorem response_shift_upper (x : V) (n : Nat) : ∀ j : Nat,
    RCle (B x (T n x))
      (RCadd (B x (T (n+j) x))
        (RCscale (Q'.ofNat j*Q'.invSucc n) (B x x)))
  | 0 => by
      simp only [Nat.add_zero, show Q'.ofNat 0 = (0 : Q') from rfl]
      rw [RCSignedPairBudget.scale_congr (Q'.zero_mul_eqv (Q'.invSucc n)),
        scale_zero, add_zero]
      exact RCle_refl _
  | j+1 => by
      have hd := mixedMoment_column_bound hw0 hw1 x 0 0 (n+j)
      simp only [Nat.zero_add, mixedMoment_zero] at hd
      have hc := RCscale_scalar_mono
        (ExpNeg.invSucc_le_of_le (Nat.le_add_right n j))
        (completedInner_nonnegative hw0 hw1 x)
      have hs := RCadd_le_add (RCle_refl (M x (n+j+1) 0))
        (RCle_trans hd hc)
      rw [← mixedMoment_split] at hs
      have hh := RCle_trans (response_shift_upper x n j)
        (RCadd_le_add hs (RCle_refl
          (RCscale (Q'.ofNat j*Q'.invSucc n) (B x x))))
      rw [add_assoc, scale_add,
        RCSignedPairBudget.scale_congr (coefficient_succ j (Q'.invSucc n))] at hh
      simpa only [Nat.add_assoc, mixedMoment_zero] using hh

variable (scale : Nat) (hwidth : side scale < width)

local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "R" n:arg => dyadicUnitResponse hw0 hw1 scale width hwidth n

/-- SAME normalized response, with a rational rounding ceiling independent
of nome, width, cutoff and terminal depth. -/
theorem dyadicUnitResponse_shift_bounds (n j : Nat) :
    leEv (R (n+j)) (R n) ∧
      leEv (R n) (CReal.add (R (n+j)) (ofQ' (Q'.ofNat j*Q'.invSucc n))) := by
  have hlo := response_shift_decreasing hw0 hw1 u n j
  have hhi := response_shift_upper hw0 hw1 u n j
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin] at hlo
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin,
    dyadicUnitExcitation_norm, scale_rational_one] at hhi
  exact ⟨hlo,hhi⟩

private theorem scale_le_side : ∀ k : Nat, k ≤ side k
  | 0 => Nat.zero_le _
  | k+1 => by
      have hp := side_positive k
      have h := scale_le_side k
      change k+1 ≤ 2^(k+1)
      rw [Nat.pow_succ]
      change k+1 ≤ side k*2
      omega

/-- Type-level tolerance cutoff for bounded offsets; its arguments name
exactly the uniformity parameters. No changing-family Cauchy claim. -/
def roundingModulus (maxShift : Nat) (epsilon : Q') : Nat :=
  (HKConv.divPos epsilon (Q'.ofNat maxShift+1)).den

private theorem rounding_coefficient_small (maxShift : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (k n j : Nat)
    (hk : roundingModulus maxShift epsilon ≤ k) (hn : side k ≤ n)
    (hj : j ≤ maxShift) : Q'.ofNat j*Q'.invSucc n ≤ epsilon := by
  let d := Q'.ofNat maxShift+1
  let delta := HKConv.divPos epsilon d
  have hd : (0 : Q') < d := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 (Q'.ofNat maxShift)
      (Q'.ofNat_nonneg maxShift)) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hdelta : (0 : Q') < delta := HKConv.divPos_pos ((zero_lt_iff_num_pos epsilon).mp he)
  have hindex : delta.den ≤ n := Nat.le_trans hk
    (Nat.le_trans (scale_le_side k) hn)
  have hi : Q'.invSucc n ≤ delta := Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hindex) (HalfPow.invSucc_den_le delta hdelta)
  have hjd : Q'.ofNat j ≤ d := Q'.le_trans' _ _ _
    (CReal.ofNat_le_ofNat hj) (Q'.add_le_self_of_nonneg _ _ (by decide : (0 : Q') ≤ 1))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hi (Q'.ofNat_nonneg j))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hjd (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv d delta)
        (HKConv.divPos_mul_eqv ((zero_lt_iff_num_pos d).mp hd)))))

/-- Every bounded shift is small at assigned positive-time lags, uniformly
over ALL strict nomes and widths. This is NOT cross-scale convergence. -/
theorem dyadicUnitResponse_rounding_small (maxShift : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n j : Nat)
    (hk : roundingModulus maxShift epsilon ≤ scale) (hn : side scale ≤ n)
    (hj : j ≤ maxShift) :
    leEv (R (n+j)) (R n) ∧ leEv (R n) (CReal.add (R (n+j)) (ofQ' epsilon)) := by
  have h := dyadicUnitResponse_shift_bounds hw0 hw1 scale hwidth n j
  exact ⟨h.1, leEv_trans h.2 (leEv_add (leEv_refl _)
    (leEv_of_le (ofQ'_le_ofQ'
      (rounding_coefficient_small maxShift epsilon he scale n j hk hn hj))))⟩

#print axioms response_shift_decreasing
#print axioms response_shift_upper
#print axioms dyadicUnitResponse_shift_bounds
#print axioms roundingModulus
#print axioms dyadicUnitResponse_rounding_small

end YMGap.Continuum.BF4WilsonAllNomeDyadicResponseRounding
