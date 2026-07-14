/-
# Constructive Hermite polynomials for the exact Gaussian functional

The probabilists' Hermite recurrence is realized on the finite `QPoly`
carrier.  Its Appell derivative law is proved extensionally at every order.
Together with Gaussian product integration by parts, this is the triangular
orthogonality engine needed for all-degree square positivity.
-/

import YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2QuaternionGaussianHermite

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             ac_rfl))

/-- Probabilists' Hermite polynomials:
`H₀=1`, `H₁=x`, `Hₙ₊₂=xHₙ₊₁-(n+1)Hₙ`. -/
def hermite : Nat → Poly
  | 0 => [1]
  | 1 => [0, 1]
  | n + 2 =>
      padd (0 :: hermite (n + 1))
        (pscale (-(Q'.ofNat (n + 1))) (hermite n))

theorem hermite_eval_recurrence (n : Nat) (z : Q') :
    eval (hermite (n + 2)) z ≈
      z * eval (hermite (n + 1)) z +
        (-(Q'.ofNat (n + 1))) * eval (hermite n) z := by
  refine Q'.eqv_trans _
    (eval (0 :: hermite (n + 1)) z +
      eval (pscale (-(Q'.ofNat (n + 1))) (hermite n)) z) _
    (eval_padd _ _ z) ?_
  exact QPoly.q_add_congr
    (QPoly.q_zero_add_eqv _)
    (eval_pscale (-(Q'.ofNat (n + 1))) (hermite n) z)

/-- The Appell derivative statement at index `n`. -/
def HermiteDerivative (n : Nat) : Prop :=
  PolyEqv (formalDerivative (hermite (n + 1)))
    (pscale (Q'.ofNat (n + 1)) (hermite n))

private theorem hermiteDerivative_zero : HermiteDerivative 0 := by
  intro z
  change eval [Q'.ofNat 1 * 1] z ≈
    eval [Q'.ofNat 1 * 1] z
  exact Q'.eqv_refl _

private theorem hermiteDerivative_one : HermiteDerivative 1 := by
  intro z
  unfold formalDerivative
  simp only [hermite, padd, pscale,
    YMGap.Continuum.UsumFactorization.pderiv,
    YMGap.Continuum.UsumFactorization.scaleFrom]
  exact Q'.eqv_refl _

private theorem hermiteDerivative_step (n : Nat)
    (hn : HermiteDerivative n) (hn1 : HermiteDerivative (n + 1)) :
    HermiteDerivative (n + 2) := by
  intro z
  let A : Q' := eval (hermite (n + 2)) z
  let B : Q' := eval (hermite (n + 1)) z
  let C : Q' := eval (hermite n) z
  let a : Q' := Q'.ofNat (n + 2)
  let b : Q' := Q'.ofNat (n + 1)
  have hD2 : eval (formalDerivative (hermite (n + 2))) z ≈ a * B := by
    exact Q'.eqv_trans _
      (eval (pscale a (hermite (n + 1))) z) _
      (hn1 z) (eval_pscale a (hermite (n + 1)) z)
  have hD1 : eval (formalDerivative (hermite (n + 1))) z ≈ b * C := by
    exact Q'.eqv_trans _
      (eval (pscale b (hermite n)) z) _
      (hn z) (eval_pscale b (hermite n) z)
  have hrec : A ≈ z * B + (-b) * C := by
    exact hermite_eval_recurrence n z
  have htail : z * (a * B) + (-a) * (b * C) ≈ a * A := by
    refine Q'.eqv_trans _ (a * (z * B + (-b) * C)) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm hrec)
  have hsucc : Q'.ofNat (n + 3) ≈ a + 1 := by
    simpa [a, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      YMGap.Continuum.UsumFactorization.ofNatSucc (n + 2)
  change
    eval
      (formalDerivative
        (padd (0 :: hermite (n + 2))
          (pscale (-a) (hermite (n + 1))))) z ≈
      eval (pscale (Q'.ofNat (n + 3)) (hermite (n + 2))) z
  refine Q'.eqv_trans _
    (eval (formalDerivative (0 :: hermite (n + 2))) z +
      eval (formalDerivative (pscale (-a) (hermite (n + 1)))) z) _
    (YMGap.Continuum.UsumFactorization.eval_pderiv_padd z _ _) ?_
  refine Q'.eqv_trans _
    ((A + z * eval (formalDerivative (hermite (n + 2))) z) +
      (-a) * eval (formalDerivative (hermite (n + 1))) z) _
    (QPoly.q_add_congr
      (YMGap.Continuum.UsumFactorization.eval_pderiv_consZero z _)
      (YMGap.Continuum.UsumFactorization.eval_pderiv_pscale z (-a) _)) ?_
  refine Q'.eqv_trans _
    ((A + z * (a * B)) + (-a) * (b * C)) _
    (QPoly.q_add_congr
      (Q'.add_eqv_congr_left A _ _
        (Q'.mul_eqv_congr_left z _ _ hD2))
      (Q'.mul_eqv_congr_left (-a) _ _ hD1)) ?_
  refine Q'.eqv_trans _ (A + (z * (a * B) + (-a) * (b * C))) _
    (Q'.add_assoc_eqv A (z * (a * B)) ((-a) * (b * C))) ?_
  refine Q'.eqv_trans _ (A + a * A) _
    (Q'.add_eqv_congr_left A _ _ htail) ?_
  refine Q'.eqv_trans _ ((a + 1) * A) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _ (Q'.ofNat (n + 3) * A) _
    (Q'.mul_eqv_congr_right _ _ A (Q'.eqv_symm hsucc)) ?_
  exact Q'.eqv_symm (eval_pscale (Q'.ofNat (n + 3)) (hermite (n + 2)) z)

private theorem hermiteDerivative_pair : ∀ n : Nat,
    HermiteDerivative n ∧ HermiteDerivative (n + 1)
  | 0 => ⟨hermiteDerivative_zero, hermiteDerivative_one⟩
  | n + 1 => by
      have ih := hermiteDerivative_pair n
      exact ⟨ih.2, hermiteDerivative_step n ih.1 ih.2⟩

/-- **All-order Appell law** `H'_(n+1) = (n+1) H_n`. -/
theorem hermite_derivative (n : Nat) : HermiteDerivative n :=
  (hermiteDerivative_pair n).1

end YMGap.Continuum.SU2QuaternionGaussianHermite

#print axioms YMGap.Continuum.SU2QuaternionGaussianHermite.hermite_eval_recurrence
#print axioms YMGap.Continuum.SU2QuaternionGaussianHermite.hermite_derivative
