/-
# The signed root-log budget on the ORIGINAL Wilson completion

At the full original root stride N=2^depth, the actual polynomial S is
nonnegative and its form is at most ||x||^2/(m+1). The upper bound follows
from the constructed positive F row and the ORIGINAL coarse defect moments.
Every m, including zero, and every state, including the boundary kernel,
is retained. This module uses neither MapPins nor an operator inverse.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootCoarseMoment
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail

namespace YMGap.Continuum.BF4WilsonAllNomeRootLogSignedBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower complement)
open YMGap.Constructive.QPolyRootLogDifference (rootPower rootDefect rootLogDifference)
open YMGap.Constructive.QPolyRootLogInitial (rootLogRemainder)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RCPolynomialFunctional (formFrom formFrom_psub rc_zero_add)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (moment)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment mixedMoment_zero)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail (mixedMoment_defect_decreasing)
open YMGap.Continuum.BF4WilsonAllNomeRootPolynomialForm
open YMGap.Continuum.BF4WilsonAllNomeRootCoarseMoment

private theorem sub_add_restore (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
      (fun | 0 => A.approx n | _ => B.approx n)))

private theorem le_of_sub_nonnegative {a b : RC} (h : RCnonneg (RCsub a b)) :
    RCle b a := by
  have hh := RCadd_le_add h (RCle_refl b)
  rwa [rc_zero_add, sub_add_restore] at hh

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Phi" => form hw0 hw1
local notation "C" => mixedMoment hw0 hw1

/-- Increasing the ORIGINAL coarse defect power never exceeds the original
state's squared norm; no positive-time preimage is selected. -/
theorem coarseMoment_norm_bound (x : V) (j : Nat) :
    RCle (C x 0 j) (B x x) := by
  induction j with
  | zero =>
      rw [mixedMoment_zero]
      exact RCle_refl _
  | succ j ih =>
      exact RCle_trans (mixedMoment_defect_decreasing hw0 hw1 x 0 j) ih

/-- The literal original F form retains precisely the signed S term at the
full root stride and the actual coarse defect moment at exponent m+1. -/
theorem original_f_form_pin (depth : Nat) (x : V) (m : Nat) :
    Phi depth x 0 (rootLogRemainder (2^depth-1) m) 0 =
      RCsub (RCscale (Q'.invSucc m) (C x 0 (m+1)))
        (Phi depth x (2^depth) (rootLogDifference (2^depth-1) m) 0) := by
  have hpos : 0 < 2^depth := Nat.pow_pos (by decide)
  have hn : (2^depth-1)+1 = 2^depth := by omega
  have hp : rootPower (2^depth-1) = polynomialPower complement (2^depth) := by
    unfold rootPower
    rw [hn]
  have hc : Phi depth x 0
      (polynomialPower (rootDefect (2^depth-1)) (m+1)) 0 = C x 0 (m+1) := by
    simpa only [Nat.zero_mul] using
      form_coarseDefectPower hw0 hw1 depth x 0 (m+1)
  unfold rootLogRemainder
  change formFrom (fun i => moment hw0 hw1 depth x 0 i) (psub _ _) 0 = _
  rw [formFrom_psub]
  change RCsub
    (Phi depth x 0
      (pscale (Q'.invSucc m) (polynomialPower (rootDefect (2^depth-1)) (m+1))) 0)
    (Phi depth x 0
      (pmul (rootPower (2^depth-1)) (rootLogDifference (2^depth-1) m)) 0) = _
  rw [form_pscale, hc, hp, form_power_complement_mul, Nat.zero_add]

/-- The actual signed S form is bounded by the explicit ORIGINAL norm budget
1/(m+1), with no restriction m>0 and no kernel exclusion. -/
theorem original_s_form_upper (depth : Nat) (x : V) (m : Nat) :
    RCle (Phi depth x (2^depth) (rootLogDifference (2^depth-1) m) 0)
      (RCscale (Q'.invSucc m) (B x x)) := by
  have hf := original_f_nonnegative hw0 hw1 depth x 0 0 (2^depth-1) m
  rw [original_f_form_pin] at hf
  exact RCle_trans (le_of_sub_nonnegative hf)
    (RCscale_mono (Q'.invSucc_nonneg m) (coarseMoment_norm_bound hw0 hw1 x (m+1)))

/-- Both signs of the actual S budget on the SAME original completion. -/
theorem original_s_signed_budget (depth : Nat) (x : V) (m : Nat) :
    RCnonneg (Phi depth x (2^depth) (rootLogDifference (2^depth-1) m) 0) ∧
      RCle (Phi depth x (2^depth) (rootLogDifference (2^depth-1) m) 0)
        (RCscale (Q'.invSucc m) (B x x)) :=
  ⟨original_s_nonnegative hw0 hw1 depth x (2^depth) 0 (2^depth-1) m,
    original_s_form_upper hw0 hw1 depth x m⟩

#print axioms coarseMoment_norm_bound
#print axioms original_f_form_pin
#print axioms original_s_form_upper
#print axioms original_s_signed_budget

end YMGap.Continuum.BF4WilsonAllNomeRootLogSignedBudget
