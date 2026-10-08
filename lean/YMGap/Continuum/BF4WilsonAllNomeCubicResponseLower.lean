/-
# Signed cubic lower bound for the ORIGINAL completed response

The exact original split M(n,l)=M(n+1,l)+M(n,l+1) and its positivity
give alternating zeroth/first/second/third truncation bounds by one
simultaneous induction in n. Pascal's recurrence supplies the coefficients.
Every state, width and integer lag (including 0..3) is retained.

No spectral measure, source filter, norm inverse or analytic premise is used.
A useful changing-family cubic margin is still unproduced. This finite-time
estimate asserts no continuum survival or physical Hamiltonian gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
import YMGap.Continuum.PNPaths
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeCubicResponseLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "M" => mixedMoment hw0 hw1
attribute [local irreducible] mixedMoment completedInner completedTime

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (X.approx n)))

private theorem add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun X Z => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (X.approx n) (Z.approx n)))

private theorem scale_coeff_add (a b : Q') (r : RC) :
    RCscale (a+b) r = RCadd (RCscale a r) (RCscale b r) := by
  refine Quotient.inductionOn r ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv a b (X.approx n)))

private theorem scale_nat_succ (n : Nat) (r : RC) :
    RCscale (Q'.ofNat (n+1)) r = RCadd (RCscale (Q'.ofNat n) r) r := by
  rw [RCSignedPairBudget.scale_congr (Q'.ofNat_add_eqv n 1), scale_coeff_add,
    RCSignedPairBudget.scale_congr (by decide : Q'.eqv (Q'.ofNat 1) 1), RCscale_one]

private theorem choose_one : ∀ n : Nat, PNPaths.choose n 1 = n
  | 0 => rfl
  | n+1 => by simp only [PNPaths.choose, choose_one n]; omega

private theorem scale_choose_succ (n k : Nat) (r : RC) :
    RCscale (Q'.ofNat (PNPaths.choose (n+1) (k+1))) r =
      RCadd (RCscale (Q'.ofNat (PNPaths.choose n (k+1))) r)
        (RCscale (Q'.ofNat (PNPaths.choose n k)) r) := by
  change RCscale (Q'.ofNat (PNPaths.choose n k + PNPaths.choose n (k+1))) r = _
  rw [RCSignedPairBudget.scale_congr (Q'.ofNat_add_eqv _ _), scale_coeff_add, add_comm]

private theorem neg_mono {a b : RC} (h : RCle a b) : RCle (RCneg b) (RCneg a) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro X Z h epsilon he
  obtain ⟨N,hN⟩ := h epsilon he
  exact ⟨N, fun n hn => Q'.neg_le_neg_add (hN n hn)⟩

private theorem sub_mono {a b c d : RC} (hab : RCle a b) (hdc : RCle d c) :
    RCle (RCsub a c) (RCsub b d) := RCadd_le_add hab (neg_mono hdc)

private theorem sub_add_last (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun X Z => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide) (fun | 0 => X.approx n | _ => Z.approx n)))

private theorem moment_step (x : V) (n l : Nat) :
    M x (n+1) l = RCsub (M x n l) (M x n (l+1)) := by
  rw [mixedMoment_split hw0 hw1 x n l, sub_add_last]

private theorem time_decreasing (x : V) (n l : Nat) : RCle (M x (n+1) l) (M x n l) := by
  have h := RCadd_le_add (RCle_refl (M x (n+1) l))
    (mixedMoment_nonnegative hw0 hw1 x n (l+1))
  rw [add_zero, ← mixedMoment_split] at h
  exact h

private def linearColumn (x : V) (n l : Nat) : RC :=
  RCsub (M x 0 l) (RCscale (Q'.ofNat n) (M x 0 (l+1)))

private def quadraticColumn (x : V) (n l : Nat) : RC :=
  RCadd (linearColumn hw0 hw1 x n l)
    (RCscale (Q'.ofNat (PNPaths.choose n 2)) (M x 0 (l+2)))

private def cubicColumn (x : V) (n l : Nat) : RC :=
  RCsub (quadraticColumn hw0 hw1 x n l)
    (RCscale (Q'.ofNat (PNPaths.choose n 3)) (M x 0 (l+3)))

private theorem linear_scalar (p : Q') (a b : RC) :
    RCsub a (RCadd (RCscale p b) b) = RCsub (RCsub a (RCscale p b)) b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun X Z => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 1) (.neg (.add (.mul (.var 0) (.var 2)) (.var 2))))
      (.add (.add (.var 1) (.neg (.mul (.var 0) (.var 2)))) (.neg (.var 2)))
      (by decide) (fun | 0 => p | 1 => X.approx n | _ => Z.approx n)))

private theorem quadratic_scalar (p q : Q') (a b c : RC) :
    RCadd (RCsub a (RCadd (RCscale p b) b)) (RCadd (RCscale q c) (RCscale p c)) =
      RCsub (RCadd (RCsub a (RCscale p b)) (RCscale q c)) (RCsub b (RCscale p c)) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun X Z W => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 2) (.neg (.add (.mul (.var 0) (.var 3)) (.var 3))))
        (.add (.mul (.var 1) (.var 4)) (.mul (.var 0) (.var 4))))
      (.add (.add (.add (.var 2) (.neg (.mul (.var 0) (.var 3))))
        (.mul (.var 1) (.var 4))) (.neg (.add (.var 3) (.neg (.mul (.var 0) (.var 4))))))
      (by decide) (fun | 0 => p | 1 => q | 2 => X.approx n | 3 => Z.approx n | _ => W.approx n)))

private theorem cubic_scalar (p q r : Q') (a b c d : RC) :
    RCsub (RCadd (RCsub a (RCadd (RCscale p b) b))
      (RCadd (RCscale q c) (RCscale p c))) (RCadd (RCscale r d) (RCscale q d)) =
    RCsub (RCsub (RCadd (RCsub a (RCscale p b)) (RCscale q c)) (RCscale r d))
      (RCadd (RCsub b (RCscale p c)) (RCscale q d)) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro X Z W
  refine Quotient.inductionOn d ?_
  intro U
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 3) (.neg (.add (.mul (.var 0) (.var 4)) (.var 4))))
        (.add (.mul (.var 1) (.var 5)) (.mul (.var 0) (.var 5))))
        (.neg (.add (.mul (.var 2) (.var 6)) (.mul (.var 1) (.var 6)))))
      (.add (.add (.add (.add (.var 3) (.neg (.mul (.var 0) (.var 4))))
        (.mul (.var 1) (.var 5))) (.neg (.mul (.var 2) (.var 6))))
        (.neg (.add (.add (.var 4) (.neg (.mul (.var 0) (.var 5)))) (.mul (.var 1) (.var 6)))))
      (by decide) (fun
        | 0 => p
        | 1 => q
        | 2 => r
        | 3 => X.approx n
        | 4 => Z.approx n
        | 5 => W.approx n
        | _ => U.approx n)))

private theorem linear_step (x : V) (n l : Nat) :
    linearColumn hw0 hw1 x (n+1) l = RCsub (linearColumn hw0 hw1 x n l) (M x 0 (l+1)) := by
  unfold linearColumn
  rw [scale_nat_succ]
  exact linear_scalar _ _ _

private theorem quadratic_step (x : V) (n l : Nat) :
    quadraticColumn hw0 hw1 x (n+1) l =
      RCsub (quadraticColumn hw0 hw1 x n l) (linearColumn hw0 hw1 x n (l+1)) := by
  unfold quadraticColumn linearColumn
  rw [scale_nat_succ, scale_choose_succ n 1, choose_one]
  rw [show l+1+1=l+2 by omega]
  exact quadratic_scalar _ _ _ _ _

private theorem cubic_step (x : V) (n l : Nat) :
    cubicColumn hw0 hw1 x (n+1) l =
      RCsub (cubicColumn hw0 hw1 x n l) (quadraticColumn hw0 hw1 x n (l+1)) := by
  unfold cubicColumn quadraticColumn linearColumn
  rw [scale_nat_succ, scale_choose_succ n 1, choose_one, scale_choose_succ n 2]
  rw [show l+1+1=l+2 by omega, show l+1+2=l+3 by omega]
  exact cubic_scalar _ _ _ _ _ _ _

private theorem alternating_columns (x : V) : ∀ n l : Nat,
    RCle (M x n l) (M x 0 l) ∧
    RCle (linearColumn hw0 hw1 x n l) (M x n l) ∧
    RCle (M x n l) (quadraticColumn hw0 hw1 x n l) ∧
    RCle (cubicColumn hw0 hw1 x n l) (M x n l) := by
  intro n
  induction n with
  | zero =>
      intro l
      simp only [linearColumn, quadraticColumn, cubicColumn, PNPaths.choose,
        show Q'.ofNat 0 = (0 : Q') from rfl, scale_zero, sub_zero, add_zero]
      exact ⟨RCle_refl _, RCle_refl _, RCle_refl _, RCle_refl _⟩
  | succ n ih =>
      intro l
      have h0 := RCle_trans (time_decreasing hw0 hw1 x n l) (ih l).1
      have h1 := sub_mono (ih l).2.1 (ih (l+1)).1
      rw [← linear_step hw0 hw1 x n l, ← moment_step hw0 hw1 x n l] at h1
      have h2 := sub_mono (ih l).2.2.1 (ih (l+1)).2.1
      rw [← quadratic_step hw0 hw1 x n l, ← moment_step hw0 hw1 x n l] at h2
      have h3 := sub_mono (ih l).2.2.2 (ih (l+1)).2.2.1
      rw [← cubic_step hw0 hw1 x n l, ← moment_step hw0 hw1 x n l] at h3
      exact ⟨h0,h1,h2,h3⟩

/-- Explicit signed cubic in four ORIGINAL time-defect moments. -/
def cubicLower (x : V) (N : Nat) : RC :=
  RCsub (RCadd (RCsub (M x 0 0) (RCscale (Q'.ofNat N) (M x 0 1)))
    (RCscale (Q'.ofNat (PNPaths.choose N 2)) (M x 0 2)))
    (RCscale (Q'.ofNat (PNPaths.choose N 3)) (M x 0 3))

/-- Unconditional for EVERY state and integer lag, without a norm floor. -/
theorem cubic_response_lower (x : V) (N : Nat) :
    RCle (cubicLower hw0 hw1 x N) (completedInner hw0 hw1 x (completedTime hw0 hw1 N x)) := by
  have h := (alternating_columns hw0 hw1 x N 0).2.2.2
  change RCle (cubicLower hw0 hw1 x N) (mixedMoment hw0 hw1 x N 0) at h
  simpa only [mixedMoment, defectPower] using h

end YMGap.Continuum.BF4WilsonAllNomeCubicResponseLower

#print axioms YMGap.Continuum.BF4WilsonAllNomeCubicResponseLower.cubicLower
#print axioms YMGap.Continuum.BF4WilsonAllNomeCubicResponseLower.cubic_response_lower
