/-
# Hermite lowering for the exact Gaussian pairing

The Gaussian product integration-by-parts identity and the Appell law cancel
the lower Hermite term in the three-term recurrence.  This yields

  <H_(n+1), q> = <H_n, q'>.

This is the direct inductive engine for orthogonality and factorial norms.
-/

import YMGap.Continuum.SU2QuaternionGaussianHermite

namespace YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP
open YMGap.Continuum.SU2QuaternionGaussianHermite

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             ac_rfl))

def gaussianPair (p q : Poly) : Q' :=
  gaussianExpectation (pmul p q)

theorem gaussianPair_polyEqv {p p' q q' : Poly}
    (hp : PolyEqv p p') (hq : PolyEqv q q') :
    gaussianPair p q ≈ gaussianPair p' q' :=
  gaussianExpectation_polyEqv (pmul_congr hp hq)

theorem gaussianPair_symm (p q : Poly) :
    gaussianPair p q ≈ gaussianPair q p :=
  gaussianExpectation_polyEqv (pmul_comm p q)

theorem gaussianPair_zero_left (q : Poly) :
    gaussianPair [] q ≈ 0 := by
  unfold gaussianPair gaussianExpectation
  exact Q'.eqv_refl 0

theorem gaussianPair_zero_right (p : Poly) :
    gaussianPair p [] ≈ 0 :=
  Q'.eqv_trans _ (gaussianPair [] p) _
    (gaussianPair_symm p []) (gaussianPair_zero_left p)

theorem gaussianPair_pscale_left (a : Q') (p q : Poly) :
    gaussianPair (pscale a p) q ≈ a * gaussianPair p q := by
  have hp : PolyEqv (pmul (pscale a p) q) (pscale a (pmul p q)) := by
    intro z
    refine Q'.eqv_trans _ (eval (pscale a p) z * eval q z) _
      (eval_pmul _ _ z) ?_
    refine Q'.eqv_trans _ ((a * eval p z) * eval q z) _
      (Q'.mul_eqv_congr_right _ _ _ (eval_pscale a p z)) ?_
    refine Q'.eqv_trans _ (a * (eval p z * eval q z)) _
      (Q'.mul_assoc_eqv a (eval p z) (eval q z)) ?_
    exact Q'.eqv_symm (Q'.eqv_trans _ (a * eval (pmul p q) z) _
      (eval_pscale a (pmul p q) z)
      (Q'.mul_eqv_congr_left a _ _ (eval_pmul p q z)))
  exact Q'.eqv_trans _ (gaussianExpectation (pscale a (pmul p q))) _
    (gaussianExpectation_polyEqv hp)
    (gaussianExpectation_pscale a (pmul p q))

theorem gaussianPair_hermite_derivative (n : Nat) (q : Poly) :
    gaussianPair (formalDerivative (hermite (n + 1))) q ≈
      Q'.ofNat (n + 1) * gaussianPair (hermite n) q :=
  Q'.eqv_trans _
    (gaussianPair (pscale (Q'.ofNat (n + 1)) (hermite n)) q) _
    (gaussianPair_polyEqv (hermite_derivative n) (peqv_refl q))
    (gaussianPair_pscale_left (Q'.ofNat (n + 1)) (hermite n) q)

private theorem hermitePair_recurrence (n : Nat) (q : Poly) :
    gaussianPair (hermite (n + 2)) q ≈
      gaussianExpectation (0 :: pmul (hermite (n + 1)) q) +
        (-(Q'.ofNat (n + 1))) * gaussianPair (hermite n) q := by
  have hp : PolyEqv (pmul (hermite (n + 2)) q)
      (padd (0 :: pmul (hermite (n + 1)) q)
        (pscale (-(Q'.ofNat (n + 1))) (pmul (hermite n) q))) := by
    intro z
    refine Q'.eqv_trans _
      (eval (hermite (n + 2)) z * eval q z) _
      (eval_pmul _ _ z) ?_
    refine Q'.eqv_trans _
      ((z * eval (hermite (n + 1)) z +
          (-(Q'.ofNat (n + 1))) * eval (hermite n) z) * eval q z) _
      (Q'.mul_eqv_congr_right _ _ _ (hermite_eval_recurrence n z)) ?_
    refine Q'.eqv_trans _
      (eval (0 :: pmul (hermite (n + 1)) q) z +
        eval (pscale (-(Q'.ofNat (n + 1)))
          (pmul (hermite n) q)) z) _
      (by
        refine Q'.eqv_trans _
          ((z * eval (hermite (n + 1)) z) * eval q z +
            ((-(Q'.ofNat (n + 1))) * eval (hermite n) z) * eval q z) _
          (QPoly.q_add_mul _ _ _) ?_
        refine QPoly.q_add_congr ?_ ?_
        · refine Q'.eqv_trans _
            (z * (eval (hermite (n + 1)) z * eval q z)) _
            (Q'.mul_assoc_eqv _ _ _) ?_
          refine Q'.eqv_trans _
            (z * eval (pmul (hermite (n + 1)) q) z) _
            (Q'.mul_eqv_congr_left z _ _
              (Q'.eqv_symm (eval_pmul (hermite (n + 1)) q z))) ?_
          exact Q'.eqv_symm (QPoly.q_zero_add_eqv _)
        · refine Q'.eqv_trans _
            ((-(Q'.ofNat (n + 1))) *
              (eval (hermite n) z * eval q z)) _
            (Q'.mul_assoc_eqv _ _ _) ?_
          refine Q'.eqv_trans _
            ((-(Q'.ofNat (n + 1))) * eval (pmul (hermite n) q) z) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.eqv_symm (eval_pmul (hermite n) q z))) ?_
          exact Q'.eqv_symm (eval_pscale _ _ z)) ?_
    exact Q'.eqv_symm (eval_padd _ _ z)
  refine Q'.eqv_trans _
    (gaussianExpectation
      (padd (0 :: pmul (hermite (n + 1)) q)
        (pscale (-(Q'.ofNat (n + 1))) (pmul (hermite n) q)))) _
    (gaussianExpectation_polyEqv hp) ?_
  refine Q'.eqv_trans _
    (gaussianExpectation (0 :: pmul (hermite (n + 1)) q) +
      gaussianExpectation
        (pscale (-(Q'.ofNat (n + 1))) (pmul (hermite n) q))) _
    (gaussianExpectation_padd _ _) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (gaussianExpectation_pscale (-(Q'.ofNat (n + 1)))
      (pmul (hermite n) q))

/-- **Hermite lowering in the exact Gaussian pairing.** -/
theorem gaussianPair_hermite_succ (n : Nat) (q : Poly) :
    gaussianPair (hermite (n + 1)) q ≈
      gaussianPair (hermite n) (formalDerivative q) := by
  cases n with
  | zero =>
      have hp : PolyEqv (pmul (hermite 1) q) (0 :: pmul (hermite 0) q) := by
        intro z
        have hH1 : eval (hermite 1) z ≈ z := by
          change (0 + z * (1 + z * 0)) ≈ z
          ring_qeqv
        have hH0q : eval (pmul (hermite 0) q) z ≈ eval q z := by
          refine Q'.eqv_trans _ (eval (hermite 0) z * eval q z) _
            (eval_pmul _ _ z) ?_
          change ((1 + z * 0) * eval q z) ≈ eval q z
          ring_qeqv
        refine Q'.eqv_trans _
          (eval (hermite 1) z * eval q z) _ (eval_pmul _ _ z) ?_
        refine Q'.eqv_trans _ (z * eval q z) _
          (Q'.mul_eqv_congr_right _ _ _ hH1) ?_
        exact Q'.eqv_symm (Q'.eqv_trans _
          (z * eval (pmul (hermite 0) q) z) _
          (QPoly.q_zero_add_eqv _)
          (Q'.mul_eqv_congr_left z _ _ hH0q))
      refine Q'.eqv_trans _
        (gaussianExpectation (0 :: pmul (hermite 0) q)) _
        (gaussianExpectation_polyEqv hp) ?_
      refine Q'.eqv_trans _
        (gaussianPair (formalDerivative (hermite 0)) q +
          gaussianPair (hermite 0) (formalDerivative q)) _
        (gaussianExpectation_mulX_product (hermite 0) q) ?_
      exact Q'.eqv_trans _
        (0 + gaussianPair (hermite 0) (formalDerivative q)) _
        (Q'.add_eqv_congr_right _ _ _ (gaussianPair_zero_left q))
        (QPoly.q_zero_add_eqv _)
  | succ k =>
      let a := Q'.ofNat (k + 1)
      have hprod := gaussianExpectation_mulX_product (hermite (k + 1)) q
      have hder := gaussianPair_hermite_derivative k q
      refine Q'.eqv_trans _
        (gaussianExpectation (0 :: pmul (hermite (k + 1)) q) +
          (-a) * gaussianPair (hermite k) q) _
        (hermitePair_recurrence k q) ?_
      refine Q'.eqv_trans _
        ((gaussianPair (formalDerivative (hermite (k + 1))) q +
            gaussianPair (hermite (k + 1)) (formalDerivative q)) +
          (-a) * gaussianPair (hermite k) q) _
        (Q'.add_eqv_congr_right _ _ _ hprod) ?_
      refine Q'.eqv_trans _
        ((a * gaussianPair (hermite k) q +
            gaussianPair (hermite (k + 1)) (formalDerivative q)) +
          (-a) * gaussianPair (hermite k) q) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_right _ _ _ hder)) ?_
      let X := gaussianPair (hermite k) q
      let Y := gaussianPair (hermite (k + 1)) (formalDerivative q)
      change (a * X + Y) + (-a) * X ≈ Y
      refine Q'.eqv_trans _ ((a * X + Y) + -(a * X)) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv a X)) ?_
      refine Q'.eqv_trans _ (Y + (a * X + -(a * X))) _ (by ring_qeqv) ?_
      exact Q'.eqv_trans _ (Y + 0) _
        (Q'.add_eqv_congr_left Y _ _ (Q'.add_neg_self_eqv (a * X)))
        (QPoly.q_add_zero_eqv Y)

theorem gaussianPair_hermite_derivative_right (p : Poly) (n : Nat) :
    gaussianPair p (formalDerivative (hermite (n + 1))) ≈
      Q'.ofNat (n + 1) * gaussianPair p (hermite n) := by
  refine Q'.eqv_trans _
    (gaussianPair (formalDerivative (hermite (n + 1))) p) _
    (gaussianPair_symm _ _) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (n + 1) * gaussianPair (hermite n) p) _
    (gaussianPair_hermite_derivative n p) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (gaussianPair_symm (hermite n) p)

private theorem formalDerivative_hermite_zero :
    formalDerivative (hermite 0) = [] := rfl

/-- Distinct Hermite modes have exactly zero Gaussian pairing. -/
theorem hermite_cross_zero : ∀ (n m : Nat), n ≠ m →
    gaussianPair (hermite n) (hermite m) ≈ 0
  | 0, 0, h => absurd rfl h
  | 0, m + 1, _ => by
      refine Q'.eqv_trans _ (gaussianPair (hermite (m + 1)) (hermite 0)) _
        (gaussianPair_symm _ _) ?_
      refine Q'.eqv_trans _
        (gaussianPair (hermite m) (formalDerivative (hermite 0))) _
        (gaussianPair_hermite_succ m (hermite 0)) ?_
      rw [formalDerivative_hermite_zero]
      exact gaussianPair_zero_right _
  | n + 1, 0, _ => by
      refine Q'.eqv_trans _
        (gaussianPair (hermite n) (formalDerivative (hermite 0))) _
        (gaussianPair_hermite_succ n (hermite 0)) ?_
      rw [formalDerivative_hermite_zero]
      exact gaussianPair_zero_right _
  | n + 1, m + 1, hne => by
      have hnm : n ≠ m := by
        intro h
        apply hne
        omega
      refine Q'.eqv_trans _
        (gaussianPair (hermite n)
          (formalDerivative (hermite (m + 1)))) _
        (gaussianPair_hermite_succ n (hermite (m + 1))) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (m + 1) * gaussianPair (hermite n) (hermite m)) _
        (gaussianPair_hermite_derivative_right (hermite n) m) ?_
      refine Q'.eqv_trans _ (Q'.ofNat (m + 1) * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (hermite_cross_zero n m hnm)) ?_
      exact QPoly.q_mul_zero _

/-- Constructive factorial used for the exact Hermite norms. -/
def hermiteFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * hermiteFactorial n

/-- Each Hermite mode has its exact positive factorial norm. -/
theorem hermite_norm_factorial : ∀ n : Nat,
    gaussianPair (hermite n) (hermite n) ≈ Q'.ofNat (hermiteFactorial n)
  | 0 => by decide
  | n + 1 => by
      refine Q'.eqv_trans _
        (gaussianPair (hermite n)
          (formalDerivative (hermite (n + 1)))) _
        (gaussianPair_hermite_succ n (hermite (n + 1))) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (n + 1) * gaussianPair (hermite n) (hermite n)) _
        (gaussianPair_hermite_derivative_right (hermite n) n) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (n + 1) * Q'.ofNat (hermiteFactorial n)) _
        (Q'.mul_eqv_congr_left _ _ _ (hermite_norm_factorial n)) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat ((n + 1) * hermiteFactorial n)) _
        (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
          (n + 1) (hermiteFactorial n)) ?_
      exact Q'.eqv_refl _

end YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality

#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality.gaussianPair_hermite_derivative
#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality.gaussianPair_hermite_succ
#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality.hermite_cross_zero
#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality.hermite_norm_factorial
