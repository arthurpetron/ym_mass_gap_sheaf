/-
# All-integer response lower bound on the original all-nome completion

Positivity of every power of the actual completed one-step time map propagates
an initial Rayleigh floor to every integer lag.  The floor is supplied for a
particular state; this module neither constructs a state nor gives an upper
gap, changing-width estimate, or physical-time limit.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeResponseLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => completedSmul hw0 hw1

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem rc_sub_nonnegative_of_le {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [rc_sub_self] at h'

private theorem rc_sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (C.approx n)))

private theorem rc_le_of_sub_nonnegative {a b : RC}
    (h : RCnonneg (RCsub a b)) : RCle b a := by
  have h' := RCadd_le_add h (RCle_refl b)
  rwa [rc_zero_add, rc_sub_add] at h'

private theorem rc_scale_sub (rho : Q') (a b : RC) :
    RCscale rho (RCsub a b) =
      RCsub (RCscale rho a) (RCscale rho b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 0) (.var 2))))
      (by decide)
      (fun | 0 => rho | 1 => A.approx n | _ => C.approx n)))

/-- Positivity of the actual time power gives
`e_(n+1) >= rho*e_n` for `e_n=r_(n+1)-rho*r_n`.  No sign assumption on
`rho` is needed for this second-difference statement. -/
theorem response_second_difference (x : V) (rho : Q') (n : Nat) :
    RCle
      (RCscale rho (RCsub (B x (T (n+1) x))
        (RCscale rho (B x (T n x)))))
      (RCsub (B x (T (n+2) x))
        (RCscale rho (B x (T (n+1) x)))) := by
  let y := completedSub hw0 hw1 (T 1 x) (S rho x)
  have h := mixedMoment_nonnegative hw0 hw1 y n 0
  change RCnonneg (B y (T n y)) at h
  dsimp only [y] at h
  rw [completedTime_sub, completedTime_smul,
    ← completedTime_add hw0 hw1 n 1 x] at h
  simp only [completedInner_sub_left, completedInner_sub_right,
    completedInner_smul_left, completedInner_smul_right,
    completedInner_time_sum] at h
  have h1 : 1+n = n+1 := by omega
  have h2 : 1+(n+1) = n+2 := by omega
  rw [h2, h1] at h
  simp only [rc_scale_sub] at h ⊢
  exact rc_le_of_sub_nonnegative h

/-- A supplied lag-one Rayleigh floor propagates to each adjacent response
of the SAME completed state. -/
theorem response_step_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x x)) (B x (T 1 x))) : ∀ n : Nat,
    RCle (RCscale rho (B x (T n x))) (B x (T (n+1) x))
  | 0 => by
      simpa only [completedTime_zero, Nat.zero_add] using hfloor
  | n+1 => by
      have h := RCscale_mono hrho
        (rc_sub_nonnegative_of_le (response_step_lower x rho hrho hfloor n))
      rw [RCscale_RCzero] at h
      exact rc_le_of_sub_nonnegative (RCle_trans h
        (response_second_difference hw0 hw1 x rho n))

/-- Every integer lag inherits the supplied lag-one floor on the ORIGINAL
all-nome Wilson completion.  No spatial-union carrier or small-nome premise
is used. -/
theorem response_geometric_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x x)) (B x (T 1 x))) : ∀ n : Nat,
    RCle (RCscale (rho^n) (B x x)) (B x (T n x))
  | 0 => by
      rw [completedTime_zero, show rho^0 = (1 : Q') from rfl, RCscale_one]
      exact RCle_refl _
  | n+1 => by
      have h := RCle_trans
        (RCscale_mono hrho (response_geometric_lower x rho hrho hfloor n))
        (response_step_lower hw0 hw1 x rho hrho hfloor n)
      rw [RCscale_RCscale] at h
      exact h

#print axioms response_second_difference
#print axioms response_step_lower
#print axioms response_geometric_lower

end YMGap.Continuum.BF4WilsonAllNomeResponseLower
