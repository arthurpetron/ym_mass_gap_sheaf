/-
# Constructive triangular Hermite expansion

This file gives an explicit finite inverse to Hermite synthesis.  Multiplying
a Hermite mode by `x` is converted with the three-term recurrence, and the
resulting coefficient action is folded through the Horner presentation of an
arbitrary `QPoly`.
-/

import YMGap.Continuum.SU2QuaternionGaussianHermiteSOS

namespace YMGap.Continuum.SU2QuaternionGaussianHermiteTriangular

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionGaussianHermite
open YMGap.Continuum.SU2QuaternionGaussianHermiteSOS

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 1000000
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

theorem hermiteSynthesisFrom_padd : ∀ (n : Nat) (cs ds : List Q') (z : Q'),
    eval (hermiteSynthesisFrom n (padd cs ds)) z ≈
      eval (hermiteSynthesisFrom n cs) z +
        eval (hermiteSynthesisFrom n ds) z
  | _, [], ds, z => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | _, _ :: _, [], z => Q'.eqv_symm (QPoly.q_add_zero_eqv _)
  | n, c :: cs, d :: ds, z => by
      refine Q'.eqv_trans _
        (eval (pscale (c + d) (hermite n)) z +
          eval (hermiteSynthesisFrom (n + 1) (padd cs ds)) z) _
        (eval_padd _ _ z) ?_
      refine Q'.eqv_trans _
        ((c + d) * eval (hermite n) z +
          (eval (hermiteSynthesisFrom (n + 1) cs) z +
            eval (hermiteSynthesisFrom (n + 1) ds) z)) _
        (QPoly.q_add_congr (eval_pscale _ _ z)
          (hermiteSynthesisFrom_padd (n + 1) cs ds z)) ?_
      refine Q'.eqv_trans _
        ((c * eval (hermite n) z +
            eval (hermiteSynthesisFrom (n + 1) cs) z) +
          (d * eval (hermite n) z +
            eval (hermiteSynthesisFrom (n + 1) ds) z)) _
        (by ring_qeqv) ?_
      exact QPoly.q_add_congr
        (Q'.eqv_symm (Q'.eqv_trans _
          (eval (pscale c (hermite n)) z +
            eval (hermiteSynthesisFrom (n + 1) cs) z) _
          (eval_padd _ _ z)
          (Q'.add_eqv_congr_right _ _ _ (eval_pscale c (hermite n) z))))
        (Q'.eqv_symm (Q'.eqv_trans _
          (eval (pscale d (hermite n)) z +
            eval (hermiteSynthesisFrom (n + 1) ds) z) _
          (eval_padd _ _ z)
          (Q'.add_eqv_congr_right _ _ _ (eval_pscale d (hermite n) z))))

theorem hermiteSynthesisFrom_pscale (a : Q') :
    ∀ (n : Nat) (cs : List Q') (z : Q'),
    eval (hermiteSynthesisFrom n (pscale a cs)) z ≈
      a * eval (hermiteSynthesisFrom n cs) z
  | _, [], _ => Q'.eqv_symm (QPoly.q_mul_zero a)
  | n, c :: cs, z => by
      refine Q'.eqv_trans _
        (eval (pscale (a * c) (hermite n)) z +
          eval (hermiteSynthesisFrom (n + 1) (pscale a cs)) z) _
        (eval_padd _ _ z) ?_
      refine Q'.eqv_trans _
        ((a * c) * eval (hermite n) z +
          a * eval (hermiteSynthesisFrom (n + 1) cs) z) _
        (QPoly.q_add_congr (eval_pscale _ _ z)
          (hermiteSynthesisFrom_pscale a (n + 1) cs z)) ?_
      refine Q'.eqv_trans _
        (a * (c * eval (hermite n) z +
          eval (hermiteSynthesisFrom (n + 1) cs) z)) _
        (by ring_qeqv) ?_
      exact Q'.mul_eqv_congr_left a _ _
        (Q'.eqv_symm (Q'.eqv_trans _
          (eval (pscale c (hermite n)) z +
            eval (hermiteSynthesisFrom (n + 1) cs) z) _
          (eval_padd _ _ z)
          (Q'.add_eqv_congr_right _ _ _ (eval_pscale c (hermite n) z))))

def zeroCoeffs : Nat → List Q'
  | 0 => []
  | n + 1 => 0 :: zeroCoeffs n

def basisCoeffs (n : Nat) (c : Q') : List Q' := zeroCoeffs n ++ [c]

private theorem synthesis_basis_from (start k : Nat) (c : Q') :
    PolyEqv (hermiteSynthesisFrom start (basisCoeffs k c))
      (pscale c (hermite (start + k))) := by
  induction k generalizing start with
  | zero =>
      intro z
      refine Q'.eqv_trans _
        (eval (pscale c (hermite start)) z + 0) _
        (eval_padd _ [] z) ?_
      refine Q'.eqv_trans _ (eval (pscale c (hermite start)) z) _
        (QPoly.q_add_zero_eqv _) ?_
      simpa using Q'.eqv_refl (eval (pscale c (hermite start)) z)
  | succ k ih =>
      intro z
      refine Q'.eqv_trans _
        (eval (pscale 0 (hermite start)) z +
          eval (hermiteSynthesisFrom (start + 1) (basisCoeffs k c)) z) _
        (eval_padd _ _ z) ?_
      refine Q'.eqv_trans _
        (0 + eval (pscale c (hermite ((start + 1) + k))) z) _
        (QPoly.q_add_congr
          (Q'.eqv_trans _ (0 * eval (hermite start) z) _
            (eval_pscale 0 _ z) (QPoly.q_zero_mul _))
          (ih (start + 1) z)) ?_
      refine Q'.eqv_trans _
        (eval (pscale c (hermite ((start + 1) + k))) z) _
        (QPoly.q_zero_add_eqv _) ?_
      have hi : (start + 1) + k = start + (k + 1) := by omega
      rw [hi]
      exact Q'.eqv_refl _

theorem synthesis_basis (n : Nat) (c : Q') :
    PolyEqv (hermiteSynthesisFrom 0 (basisCoeffs n c))
      (pscale c (hermite n)) := by
  simpa using synthesis_basis_from 0 n c

/-- Hermite coefficients of `x * (c H_n)`. -/
def xHermiteTerm : Nat → Q' → List Q'
  | 0, c => basisCoeffs 1 c
  | n + 1, c =>
      padd (basisCoeffs (n + 2) c)
        (basisCoeffs n (Q'.ofNat (n + 1) * c))

theorem synthesis_xHermiteTerm (n : Nat) (c : Q') :
    PolyEqv (hermiteSynthesisFrom 0 (xHermiteTerm n c))
      (0 :: pscale c (hermite n)) := by
  cases n with
  | zero =>
      intro z
      refine Q'.eqv_trans _ (eval (pscale c (hermite 1)) z) _
        (synthesis_basis 1 c z) ?_
      refine Q'.eqv_trans _ (c * eval (hermite 1) z) _
        (eval_pscale c _ z) ?_
      have hH1 : eval (hermite 1) z ≈ z := by
        change (0 + z * (1 + z * 0)) ≈ z
        ring_qeqv
      have hH0 : eval (hermite 0) z ≈ 1 := by
        change (1 + z * 0) ≈ 1
        exact Q'.eqv_trans _ (1 + 0) _
          (Q'.add_eqv_congr_left 1 _ _ (QPoly.q_mul_zero z))
          (QPoly.q_add_zero_eqv 1)
      refine Q'.eqv_trans _ (c * z) _
        (Q'.mul_eqv_congr_left c _ _ hH1) ?_
      refine Q'.eqv_trans _ (z * (c * eval (hermite 0) z)) _
        (Q'.eqv_trans _ (z * (c * 1)) _ (by ring_qeqv)
          (Q'.mul_eqv_congr_left z _ _
            (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm hH0)))) ?_
      exact Q'.eqv_symm (Q'.eqv_trans _
        (z * eval (pscale c (hermite 0)) z) _
        (QPoly.q_zero_add_eqv _)
        (Q'.mul_eqv_congr_left z _ _ (eval_pscale c _ z)))
  | succ n =>
      intro z
      refine Q'.eqv_trans _
        (eval (hermiteSynthesisFrom 0 (basisCoeffs (n + 2) c)) z +
          eval (hermiteSynthesisFrom 0
            (basisCoeffs n (Q'.ofNat (n + 1) * c))) z) _
        (hermiteSynthesisFrom_padd 0 _ _ z) ?_
      refine Q'.eqv_trans _
        (eval (pscale c (hermite (n + 2))) z +
          eval (pscale (Q'.ofNat (n + 1) * c) (hermite n)) z) _
        (QPoly.q_add_congr (synthesis_basis (n + 2) c z)
          (synthesis_basis n (Q'.ofNat (n + 1) * c) z)) ?_
      refine Q'.eqv_trans _
        (c * eval (hermite (n + 2)) z +
          (Q'.ofNat (n + 1) * c) * eval (hermite n) z) _
        (QPoly.q_add_congr (eval_pscale c _ z) (eval_pscale _ _ z)) ?_
      refine Q'.eqv_trans _
        (z * (c * eval (hermite (n + 1)) z)) _ ?_ ?_
      · have hr := hermite_eval_recurrence n z
        refine Q'.eqv_trans _
          (c * (z * eval (hermite (n + 1)) z +
            (-(Q'.ofNat (n + 1))) * eval (hermite n) z) +
            (Q'.ofNat (n + 1) * c) * eval (hermite n) z) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left c _ _ hr)) ?_
        let a := Q'.ofNat (n + 1)
        let C := eval (hermite n) z
        let Y := z * eval (hermite (n + 1)) z
        have hneg : c * ((-a) * C) ≈ -((a * c) * C) := by
          refine Q'.eqv_trans _ ((c * (-a)) * C) _
            (Q'.eqv_symm (Q'.mul_assoc_eqv c (-a) C)) ?_
          refine Q'.eqv_trans _ (-(c * a) * C) _
            (Q'.mul_eqv_congr_right _ _ C (Q'.mul_neg_eqv c a)) ?_
          refine Q'.eqv_trans _ (-((c * a) * C)) _
            (Q'.neg_mul_eqv (c * a) C) ?_
          exact Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_right _ _ C (Q'.mul_comm_eqv c a))
        change c * (Y + (-a) * C) + (a * c) * C ≈ z * (c * eval (hermite (n + 1)) z)
        refine Q'.eqv_trans _
          ((c * Y + c * ((-a) * C)) + (a * c) * C) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv c Y ((-a) * C))) ?_
        refine Q'.eqv_trans _
          ((c * Y + -((a * c) * C)) + (a * c) * C) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.add_eqv_congr_left (c * Y) _ _ hneg)) ?_
        refine Q'.eqv_trans _
          (c * Y + (-((a * c) * C) + (a * c) * C)) _
          (Q'.add_assoc_eqv (c * Y) (-((a * c) * C)) ((a * c) * C)) ?_
        refine Q'.eqv_trans _ (c * Y + 0) _
          (Q'.add_eqv_congr_left (c * Y) _ _
            (Q'.neg_add_self_eqv ((a * c) * C))) ?_
        refine Q'.eqv_trans _ (c * Y) _ (QPoly.q_add_zero_eqv _) ?_
        change c * (z * eval (hermite (n + 1)) z) ≈
          z * (c * eval (hermite (n + 1)) z)
        ring_qeqv
      · exact Q'.eqv_symm (Q'.eqv_trans _
          (z * eval (pscale c (hermite (n + 1))) z) _
          (QPoly.q_zero_add_eqv _)
          (Q'.mul_eqv_congr_left z _ _ (eval_pscale c _ z)))

/-- Full Hermite coefficient action for multiplication by `x`. -/
def hermiteXCoeffsFrom : Nat → List Q' → List Q'
  | _, [] => []
  | n, c :: cs => padd (xHermiteTerm n c) (hermiteXCoeffsFrom (n + 1) cs)

theorem synthesis_hermiteXCoeffsFrom : ∀ (n : Nat) (cs : List Q'),
    PolyEqv (hermiteSynthesisFrom 0 (hermiteXCoeffsFrom n cs))
      (0 :: hermiteSynthesisFrom n cs)
  | _, [] => by
      intro z
      change (0 : Q') ≈ 0 + z * 0
      exact Q'.eqv_symm (Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ _ (QPoly.q_mul_zero z))
        (QPoly.q_zero_add_eqv 0))
  | n, c :: cs => by
      intro z
      refine Q'.eqv_trans _
        (eval (hermiteSynthesisFrom 0 (xHermiteTerm n c)) z +
          eval (hermiteSynthesisFrom 0 (hermiteXCoeffsFrom (n + 1) cs)) z) _
        (hermiteSynthesisFrom_padd 0 _ _ z) ?_
      refine Q'.eqv_trans _
        (eval (0 :: pscale c (hermite n)) z +
          eval (0 :: hermiteSynthesisFrom (n + 1) cs) z) _
        (QPoly.q_add_congr (synthesis_xHermiteTerm n c z)
          (synthesis_hermiteXCoeffsFrom (n + 1) cs z)) ?_
      refine Q'.eqv_trans _
        (z * eval (pscale c (hermite n)) z +
          z * eval (hermiteSynthesisFrom (n + 1) cs) z) _
        (QPoly.q_add_congr (QPoly.q_zero_add_eqv _) (QPoly.q_zero_add_eqv _)) ?_
      refine Q'.eqv_trans _
        (z * (eval (pscale c (hermite n)) z +
          eval (hermiteSynthesisFrom (n + 1) cs) z)) _
        (Q'.eqv_symm (Q'.mul_add_eqv z _ _)) ?_
      exact Q'.eqv_symm (Q'.eqv_trans _
        (z * eval (padd (pscale c (hermite n))
          (hermiteSynthesisFrom (n + 1) cs)) z) _
        (QPoly.q_zero_add_eqv _)
        (Q'.mul_eqv_congr_left z _ _ (eval_padd _ _ z)))

/-- Explicit triangular Hermite coefficients for an arbitrary `QPoly`. -/
def hermiteExpand : Poly → List Q'
  | [] => []
  | c :: cs => padd [c] (hermiteXCoeffsFrom 0 (hermiteExpand cs))

/-- **Constructive triangular surjectivity.** -/
theorem hermiteExpand_synthesis : ∀ p : Poly,
    PolyEqv p (hermiteSynthesisFrom 0 (hermiteExpand p))
  | [] => peqv_refl []
  | c :: cs => by
      intro z
      refine Q'.eqv_trans _
        (c + z * eval (hermiteSynthesisFrom 0 (hermiteExpand cs)) z) _
        (Q'.add_eqv_congr_left c _ _
          (Q'.mul_eqv_congr_left z _ _ (hermiteExpand_synthesis cs z))) ?_
      refine Q'.eqv_symm (Q'.eqv_trans _
        (eval (hermiteSynthesisFrom 0 [c]) z +
          eval (hermiteSynthesisFrom 0
            (hermiteXCoeffsFrom 0 (hermiteExpand cs))) z) _
        (hermiteSynthesisFrom_padd 0 _ _ z) ?_)
      refine QPoly.q_add_congr ?_ ?_
      · refine Q'.eqv_trans _ (eval (pscale c (hermite 0)) z + 0) _
          (eval_padd _ [] z) ?_
        refine Q'.eqv_trans _ (c * eval (hermite 0) z + 0) _
          (Q'.add_eqv_congr_right _ _ _ (eval_pscale c _ z)) ?_
        change c * (1 + z * 0) + 0 ≈ c
        ring_qeqv
      · exact Q'.eqv_trans _
          (eval (0 :: hermiteSynthesisFrom 0 (hermiteExpand cs)) z) _
          (synthesis_hermiteXCoeffsFrom 0 (hermiteExpand cs) z)
          (QPoly.q_zero_add_eqv _)

end YMGap.Continuum.SU2QuaternionGaussianHermiteTriangular

#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteTriangular.synthesis_hermiteXCoeffsFrom
#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteTriangular.hermiteExpand_synthesis
