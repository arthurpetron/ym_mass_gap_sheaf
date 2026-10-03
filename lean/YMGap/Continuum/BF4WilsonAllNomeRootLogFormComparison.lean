/-
The ORIGINAL finite quotient/logPartial diagonal comparison.
The error is the retained original root tail minus the ORIGINAL S-form.
S/F positivity, literal coarse/map pins and the retained moment telescope
produce the two estimates; no comparison premise is supplied by the caller.
Positive log cutoffs suffice for the limit. No operator inverse, boundary
kernel exclusion, spectral substitution or physical scaling is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootLogMapPins
import YMGap.Continuum.BF4WilsonAllNomeRootLogSignedBudget
import YMGap.Continuum.BF4WilsonAllNomeRootMomentTelescope
import YMGap.Continuum.BF4WilsonAllNomeRootLogTail

namespace YMGap.Continuum.BF4WilsonAllNomeRootLogFormComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyFiniteLogDerivative
open YMGap.Constructive.QPolyRootLogDifference
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RCPolynomialFunctional
open YMGap.Continuum.RCSignedPairBudget (neg_mono)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (moment)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (differenceQuotient)
open YMGap.Continuum.BF4WilsonAllNomeLogPartial (logPartial)
open YMGap.Continuum.BF4WilsonAllNomeRootPolynomialForm
open YMGap.Continuum.BF4WilsonAllNomeRootLogMapPins
open YMGap.Continuum.BF4WilsonAllNomeRootLogSignedBudget
open YMGap.Continuum.BF4WilsonAllNomeRootMomentTelescope
open YMGap.Continuum.BF4WilsonAllNomeRootLogTail (root_quadratic_tail_bound)

private theorem rc_add_assoc (a b c : RC) :
    RCadd (RCadd a b) c = RCadd a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n)))

private theorem rc_neg_zero : RCneg RCzero = RCzero := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => (by decide : ((-0) : Q').eqv 0)))

private theorem error_identity (a b t : RC) :
    RCsub b a = RCsub t (RCsub (RCadd a t) b) := by
  refine Quotient.inductionOn₃ a b t ?_
  intro A B T
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.var 1) (.neg (.var 0)))
      (.add (.var 2) (.neg (.add (.add (.var 0) (.var 2)) (.neg (.var 1)))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => T.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "M" => moment hw0 hw1
local notation "Phi" => form hw0 hw1

private theorem form_coordinate_power (depth : Nat) (x : V) (k j : Nat) :
    Phi depth x k (polynomialPower coordinate j) 0 = M depth x k j := by
  have h := form_monomial hw0 hw1 depth x k 0 0 j
  have hp := form_coeffEqv hw0 hw1 depth x k 0
    (coeffEqv_pmul_one_left (polynomialPower coordinate j))
  exact hp.symm.trans (by simpa only [Nat.add_zero, Nat.zero_add] using h)

/-- Separate the degree-one term from the ACTUAL finite root series. -/
theorem finiteLog_root_tail_pin (depth : Nat) (x : V) (k r : Nat) :
    Phi depth x k (finiteLog coordinate (r+1)) 0 =
      RCadd (M depth x k 1) (weightedMomentTail hw0 hw1 depth x k r) := by
  induction r with
  | zero =>
      change Phi depth x k (padd []
        (pscale (Q'.invSucc 0) (polynomialPower coordinate 1))) 0 = _
      rw [form_padd, form_pscale, form_coordinate_power]
      change RCadd RCzero (RCscale (Q'.invSucc 0) (M depth x k 1)) =
        RCadd (M depth x k 1) RCzero
      rw [rc_zero_add, rc_scale_congr (by decide : (Q'.invSucc 0).eqv 1),
        RCscale_one, rc_add_zero]
  | succ r ih =>
      change Phi depth x k (padd (finiteLog coordinate (r+1))
        (pscale (Q'.invSucc (r+1)) (polynomialPower coordinate (r+1+1)))) 0 = _
      rw [form_padd, form_pscale, form_coordinate_power, ih]
      simpa only [weightedMomentTail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using rc_add_assoc (M depth x k 1)
          (weightedMomentTail hw0 hw1 depth x k r)
          (RCscale (Q'.invSucc (r+1)) (M depth x k (r+1+1)))

/-- ORIGINAL S-form equals quotient diagonal plus retained tail minus log diagonal. -/
theorem original_s_diagonal_pin (depth : Nat) (x : V) (m : Nat) (hm : 0 < m) :
    Phi depth x (2^depth) (rootLogDifference (2^depth-1) m) 0 =
      RCsub (RCadd (B x (differenceQuotient hw0 hw1 depth x))
        (originalTail hw0 hw1 depth x (2^depth) (2^depth*m-1)))
        (B x (logPartial hw0 hw1 m x)) := by
  have hN : 0 < 2^depth := Nat.pow_pos (by decide)
  have hn : (2^depth-1)+1 = 2^depth := by omega
  have hL : 2^depth*m-1+1 = 2^depth*m := by
    have hp := Nat.mul_pos hN hm
    omega
  have htail := finiteLog_root_tail_pin hw0 hw1 depth x (2^depth) (2^depth*m-1)
  rw [hL] at htail
  unfold rootLogDifference
  rw [hn]
  change formFrom _ (psub _ _) 0 = _
  rw [formFrom_psub]
  change RCsub
    (Phi depth x (2^depth) (pscale (Q'.ofNat (2^depth)) (finiteLog coordinate (2^depth*m))) 0)
    (Phi depth x (2^depth) (finiteLog (rootDefect (2^depth-1)) m) 0) = _
  rw [form_pscale, htail, RCscale_RCadd, finiteLog_diagonal_pin,
    ← differenceQuotient_diagonal_pin]
  rfl

/-- The literal finite difference, in the ORIGINAL completed pairing. -/
def diagonalError (depth m : Nat) (x : V) : RC :=
  B x (completedSub hw0 hw1 (logPartial hw0 hw1 m x)
    (differenceQuotient hw0 hw1 depth x))

/-- Exact signed decomposition; both terms are original moment data. -/
theorem diagonalError_pin (depth : Nat) (x : V) (m : Nat) (hm : 0 < m) :
    diagonalError hw0 hw1 depth m x =
      RCsub (originalTail hw0 hw1 depth x (2^depth) (2^depth*m-1))
        (Phi depth x (2^depth) (rootLogDifference (2^depth-1) m) 0) := by
  rw [original_s_diagonal_pin hw0 hw1 depth x m hm]
  unfold diagonalError
  rw [completedInner_sub_right]
  exact error_identity _ _ _

/-- Computed upper error at depth d+2, independently of positive log cutoff. -/
theorem diagonalError_upper (d : Nat) (x : V) (m : Nat) (hm : 0 < m) :
    RCle (diagonalError hw0 hw1 (d+2) m x) (RCscale (2*half^d) (B x x)) := by
  rw [diagonalError_pin hw0 hw1 (d+2) x m hm]
  have hs := neg_mono (original_s_nonnegative hw0 hw1 (d+2) x (2^(d+2)) 0
    (2^(d+2)-1) m)
  have h := RCadd_le_add
    (RCle_refl (originalTail hw0 hw1 (d+2) x (2^(d+2)) (2^(d+2)*m-1))) hs
  rw [rc_neg_zero, rc_add_zero] at h
  exact RCle_trans h (RCle_trans
    (originalTail_quadratic_bound hw0 hw1 (d+2) x (2^(d+2))
      (2^(d+2)*m-1) (Nat.pow_pos (by decide)))
    (root_quadratic_tail_bound hw0 hw1 d x))

/-- Computed lower error retains the ACTUAL original F budget. -/
theorem diagonalError_lower (depth : Nat) (x : V) (m : Nat) (hm : 0 < m) :
    RCle (RCneg (RCscale (Q'.invSucc m) (B x x))) (diagonalError hw0 hw1 depth m x) := by
  rw [diagonalError_pin hw0 hw1 depth x m hm]
  have ht := RCscale_mono (SU3CharFactor.ofNat_nonneg (2^depth))
    (weightedMomentTail_nonnegative hw0 hw1 depth x (2^depth) (2^depth*m-1))
  rw [RCscale_RCzero] at ht
  have h := RCadd_le_add ht (neg_mono (original_s_form_upper hw0 hw1 depth x m))
  simpa only [rc_zero_add, originalTail, RCsub] using h

#print axioms finiteLog_root_tail_pin
#print axioms original_s_diagonal_pin
#print axioms diagonalError
#print axioms diagonalError_pin
#print axioms diagonalError_upper
#print axioms diagonalError_lower

end YMGap.Continuum.BF4WilsonAllNomeRootLogFormComparison
