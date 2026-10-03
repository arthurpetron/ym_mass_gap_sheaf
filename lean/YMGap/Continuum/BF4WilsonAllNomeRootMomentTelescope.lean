/-
# A retained finite telescope on the ORIGINAL root/defect moments

The exact split telescopes in the defect index, retaining the last positive
moment.  The weighted tail starts at defect degree two, with its actual
finite-log coefficients 1/(i+2).  Empty sums are included.  The consumer
sets the count to N*M-1 and then uses the existing original-root 8/N budget.
No scalar spectral substitution, inverse root or new carrier is introduced.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
import YMGap.Continuum.ContinuousTransferCalculus
import YMGap.Constructive.ExpNeg

namespace YMGap.Continuum.BF4WilsonAllNomeRootMomentTelescope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_add_assoc (a b c : RC) :
    RCadd (RCadd a b) c = RCadd a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "M" => moment hw0 hw1

/-- The literal finite sum of r consecutive actual defect moments. -/
def finiteMomentSum (depth : Nat) (x : V) (k l : Nat) : Nat → RC
  | 0 => RCzero
  | r+1 => RCadd (finiteMomentSum depth x k l r) (M depth x k (l+r))

/-- Exact telescope, including the original positive final moment. -/
theorem finiteMomentSum_retained (depth : Nat) (x : V) (k l r : Nat) :
    RCadd (finiteMomentSum hw0 hw1 depth x (k+1) l r)
      (M depth x k (l+r)) = M depth x k l := by
  induction r with
  | zero =>
      simpa only [finiteMomentSum, Nat.add_zero] using
        rc_zero_add (M depth x k l)
  | succ r ih =>
      change RCadd
        (RCadd (finiteMomentSum hw0 hw1 depth x (k+1) l r)
          (M depth x (k+1) (l+r)))
        (M depth x k (l+(r+1))) = _
      rw [show l+(r+1) = (l+r)+1 by omega, rc_add_assoc,
        ← moment_split hw0 hw1 depth x k (l+r)]
      exact ih

theorem finiteMomentSum_nonnegative (depth : Nat) (x : V) (k l r : Nat) :
    RCnonneg (finiteMomentSum hw0 hw1 depth x k l r) := by
  induction r with
  | zero =>
      exact RCle_refl RCzero
  | succ r ih =>
      change RCle RCzero (RCadd (finiteMomentSum hw0 hw1 depth x k l r)
        (M depth x k (l+r)))
      have h := RCadd_le_add ih (moment_nonnegative hw0 hw1 depth x k (l+r))
      simpa only [rc_zero_add] using h

/-- Remove only the nonnegative retained endpoint. -/
theorem finiteMomentSum_le (depth : Nat) (x : V) (k l r : Nat) :
    RCle (finiteMomentSum hw0 hw1 depth x (k+1) l r) (M depth x k l) := by
  have h := RCadd_le_add
    (RCle_refl (finiteMomentSum hw0 hw1 depth x (k+1) l r))
    (moment_nonnegative hw0 hw1 depth x k (l+r))
  simpa only [rc_add_zero, finiteMomentSum_retained] using h

/-- The actual log-tail weights at degrees 2 through r+1. -/
def weightedMomentTail (depth : Nat) (x : V) (k : Nat) : Nat → RC
  | 0 => RCzero
  | r+1 => RCadd (weightedMomentTail depth x k r)
      (RCscale (Q'.invSucc (r+1)) (M depth x k (2+r)))

theorem weightedMomentTail_nonnegative (depth : Nat) (x : V) (k r : Nat) :
    RCnonneg (weightedMomentTail hw0 hw1 depth x k r) := by
  induction r with
  | zero =>
      exact RCle_refl RCzero
  | succ r ih =>
      have ht := RCscale_mono (Q'.invSucc_nonneg (r+1))
        (moment_nonnegative hw0 hw1 depth x k (2+r))
      rw [RCscale_RCzero] at ht
      have h := RCadd_le_add ih ht
      simpa only [weightedMomentTail, rc_zero_add] using h

/-- Every coefficient in this degree-two tail is at most one half. -/
theorem weightedMomentTail_half_bound (depth : Nat) (x : V) (k r : Nat) :
    RCle (weightedMomentTail hw0 hw1 depth x k r)
      (RCscale half (finiteMomentSum hw0 hw1 depth x k 2 r)) := by
  induction r with
  | zero =>
      simp only [weightedMomentTail, finiteMomentSum, RCscale_RCzero]
      exact RCle_refl RCzero
  | succ r ih =>
      have hc : Q'.invSucc (r+1) ≤ half :=
        ExpNeg.invSucc_le_of_le (show 1 ≤ r+1 by omega)
      have ht := RCscale_scalar_mono hc (moment_nonnegative hw0 hw1 depth x k (2+r))
      have h := RCadd_le_add ih ht
      simpa only [weightedMomentTail, finiteMomentSum, RCscale_RCadd] using h

/-- The finite ORIGINAL root-series tail, without an infinite series. -/
def originalTail (depth : Nat) (x : V) (N r : Nat) : RC :=
  RCscale (Q'.ofNat N) (weightedMomentTail hw0 hw1 depth x N r)

/-- The retained telescope pays the weighted original tail at every positive
root stride N, including an empty tail. -/
theorem originalTail_quadratic_bound (depth : Nat) (x : V) (N r : Nat)
    (hN : 0 < N) :
    RCle (originalTail hw0 hw1 depth x N r)
      (RCscale (Q'.ofNat N * half) (M depth x (N-1) 2)) := by
  have hsum := finiteMomentSum_le hw0 hw1 depth x (N-1) 2 r
  rw [show N-1+1 = N by omega] at hsum
  have htail := RCle_trans (weightedMomentTail_half_bound hw0 hw1 depth x N r)
    (RCscale_mono half_nonneg hsum)
  have h := RCscale_mono (ofNat_nonneg N) htail
  simpa only [originalTail, RCscale_RCscale] using h

#print axioms finiteMomentSum
#print axioms finiteMomentSum_retained
#print axioms finiteMomentSum_nonnegative
#print axioms finiteMomentSum_le
#print axioms weightedMomentTail
#print axioms weightedMomentTail_nonnegative
#print axioms weightedMomentTail_half_bound
#print axioms originalTail
#print axioms originalTail_quadratic_bound

end YMGap.Continuum.BF4WilsonAllNomeRootMomentTelescope
