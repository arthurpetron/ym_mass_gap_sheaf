/-
# A coercive estimate from finite approximate dual tests

Use the positive square of C*f-L*test_k. The finite family norm costs
C+rho^k*N and the pairing error costs rho^k*(L*B+N*||f||^2).
The coefficient N disappears through the existing explicit geometric modulus
and rational Archimedean order lemma. No dual limit, division by B or by
||f||^2, or completed carrier is constructed.

This is positive-form algebra. Its physical consumer must supply the actual
finite family estimates; it is not itself a spectral-gap theorem.
-/

import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.RegularCReal

namespace YMGap.Continuum.GNSFiniteDualCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem add_le_add {a b c d : Q'} (h : a ≤ b) (k : c ≤ d) : a+c ≤ b+d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h) (Q'.add_le_add_left _ _ _ k)

private theorem add_nonneg (a b : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a+b := Q'.le_trans' _ _ _ ha (Q'.add_le_self_of_nonneg a b hb)

private theorem cancel_add {p a b : Q'} (h : p+a ≤ p+b) : a ≤ b := by
  have he (x : Q') : -p+(p+x) ≈ x :=
    poly_identity_of_normal_eq (.add (.neg (.var 0)) (.add (.var 0) (.var 1)))
      (.var 1) (by decide) (fun | 0 => p | _ => x)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (he a))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left (-p) _ _ h) (Q'.le_of_eqv (he b)))

private theorem test_inequality (D : GNSData) (f v : D.V) (C L B e : Q')
    (hp : D.B v f + e ≈ B) :
    2*C*L*B ≤ C*C*D.B f f + L*(L*D.B v v) + C*(2*L*e) := by
  have hn := D.toPreInnerForm.nonnegQuad C (-L) f v
  have he : C*C*D.B f f + (2*(C*(-L)))*D.B f v + (-L)*(-L)*D.B v v ≈
      (C*C*D.B f f + L*(L*D.B v v)) + -(2*C*L*D.B v f) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (qmul (Q'.eqv_refl _) (D.B_symm f v)))
        (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.mul (.mul (.const 2) (.mul (.var 0) (.neg (.var 1)))) (.var 3)))
          (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.var 4)))
        (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.mul (.var 1) (.mul (.var 1) (.var 4))))
          (.neg (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3))))
        (by decide) (fun | 0 => C | 1 => L | 2 => D.B f f | 3 => D.B v f | _ => D.B v v))
  have hb := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))
  have hsum := Q'.add_le_add_right _ _ (C*(2*L*e)) hb
  have hleft : 2*C*L*B ≈ 2*C*L*D.B v f + C*(2*L*e) :=
    Q'.eqv_trans _ _ _ (qmul (Q'.eqv_refl _) (Q'.eqv_symm hp))
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 3))))
        (by decide) (fun | 0 => C | 1 => L | 2 => D.B v f | _ => e))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hsum

/-- The finite approximants supply a genuine coercive estimate in the SAME
positive form. Family size N occurs only in a discarded geometric error. -/
theorem coercivity_of_finite_tests (D : GNSData) (f : D.V)
    (tests : Nat → D.V) (error : Nat → Q') (B L C N rho : Q')
    (hB : (0 : Q') ≤ B) (hL : (0 : Q') ≤ L) (hC : (0 : Q') < C)
    (hN : (0 : Q') ≤ N) (hr : (0 : Q') ≤ rho) (hr1 : rho < (1 : Q'))
    (hnorm : ∀ k, L*D.B (tests k) (tests k) ≤ (C+rho^k*N)*B)
    (hpair : ∀ k, D.B (tests k) f + error k ≈ B)
    (herror : ∀ k, 2*L*error k ≤ rho^k*(L*B+N*D.B f f)) :
    L*B ≤ C*D.B f f := by
  let E := D.B f f
  let budget := C*L*B + C*N*E + L*N*B
  have hE : (0 : Q') ≤ E := D.self_nonneg f
  have hc := Q'.le_of_lt hC
  have hbudget : (0 : Q') ≤ budget :=
    add_nonneg _ _
      (add_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hc hL) hB)
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hc hN) hE))
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hL hN) hB)
  have happrox (k : Nat) : C*(L*B) ≤ C*(C*E)+rho^k*budget := by
    have h0 := test_inequality D f (tests k) C L B (error k) (hpair k)
    have h1 := add_le_add
      (Q'.add_le_add_left (C*C*E) _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ L (hnorm k) hL))
      (Q'.mul_le_mul_of_nonneg_left _ _ C (herror k) hc)
    have he : C*C*E + L*((C+rho^k*N)*B) + C*(rho^k*(L*B+N*E)) ≈
        C*(L*B) + (C*(C*E)+rho^k*budget) :=
      poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 4))
          (.mul (.var 1) (.mul (.add (.var 0) (.mul (.var 5) (.var 3))) (.var 2))))
          (.mul (.var 0) (.mul (.var 5)
            (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))))
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.add (.mul (.var 0) (.mul (.var 0) (.var 4)))
            (.mul (.var 5) (.add
              (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
                (.mul (.mul (.var 0) (.var 3)) (.var 4)))
              (.mul (.mul (.var 1) (.var 3)) (.var 2))))))
        (by decide) (fun | 0 => C | 1 => L | 2 => B | 3 => N | 4 => E | _ => rho^k)
    have hleft : C*(L*B)+C*(L*B) ≈ 2*C*L*B :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
        (by decide) (fun | 0 => C | 1 => L | _ => B)
    have hh := Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ h0 (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv he)))
    exact cancel_add hh
  have hclosed : C*(L*B) ≤ C*(C*E) := by
    refine Q'.le_of_le_add_mul_invSucc _ _ 1 ?_
    intro precision
    let k := PositiveContractionResidual.geometricCutoff rho budget (Q'.invSucc precision)
    have he := PositiveContractionResidual.geometric_bound hr hr1 hbudget
      (Q'.invSucc_pos precision) k (Nat.le_refl k)
    exact Q'.le_trans' _ _ _ (happrox k)
      (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ he (Q'.ge_of_eqv (Q'.one_mul_eqv _))))
  exact Q'.le_of_mul_le_mul_left hclosed hC

end YMGap.Continuum.GNSFiniteDualCoercivity

#print axioms YMGap.Continuum.GNSFiniteDualCoercivity.coercivity_of_finite_tests
