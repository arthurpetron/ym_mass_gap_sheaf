/-
# Actual Laurent increment from a quadratic Euler bound

The comparison is the literal polynomial c*x^(E+2)-p. Its Laurent
evaluation is c*x^2-p/x^E, and its formal Euler sign follows from the
given original Euler bound by positive-denominator cancellation. The
checked finite Laurent endpoint order then pays the increment without
an integration axiom. Both the numerator and c may be signed or zero.
-/

import YMGap.Continuum.RationalLaurentIntervalOrder

namespace YMGap.Continuum.RationalLaurentQuadraticIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation (coefficient_eval)
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower coordinate)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.HeatKernelRGStep (qpow_add lt_of_lt_of_le)
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator (nome_power_generator)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RationalLaurentIntervalOrder

local infix:50 " ≈ " => Q'.eqv

private def comparisonNumerator (p : Poly) (E : Nat) (c : Q') : Poly :=
  psub (pscale c (polynomialPower coordinate (E+2))) p

private def euler (p : Poly) (E : Nat) (x : Q') : Q' :=
  x*QPoly.eval (pderiv p) x + -(Q'.ofNat E*QPoly.eval p x)

private theorem power_positive {x : Q'} (hx : (0 : Q') < x) :
    ∀ E : Nat, (0 : Q') < qpow x E
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | E+1 => Q'.mul_pos (power_positive hx E) hx

private theorem power_quadratic (x : Q') (E : Nat) :
    qpow x (E+2) ≈ qpow x E*(x*x) :=
  Q'.eqv_trans _ _ _ (qpow_add x E 2)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)))

private theorem derivative_sub (p q : Poly) :
    CoeffEqv (pderiv (psub p q)) (psub (pderiv p) (pderiv q)) :=
  (pderiv_padd p (pneg q)).trans
    ((CoeffEqv.refl _).padd (pderiv_pscale (-1) q))

private theorem euler_sub (p q : Poly) (E : Nat) (x : Q') :
    euler (psub p q) E x ≈ euler p E x + -(euler q E x) := by
  have hd := Q'.eqv_trans _ _ _ (coefficient_eval (derivative_sub p q) x)
    (eval_psub (pderiv p) (pderiv q) x)
  have hs : euler (psub p q) E x ≈
      x*(QPoly.eval (pderiv p) x + -QPoly.eval (pderiv q) x) +
        -(Q'.ofNat E*(QPoly.eval p x + -QPoly.eval q x)) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left x _ _ hd)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_psub p q x)))
  exact Q'.eqv_trans _ _ _ hs (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.neg (.mul (.var 3) (.add (.var 4) (.neg (.var 5))))))
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 3) (.var 4))))
      (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 3) (.var 5))))))
    (by decide) (fun
      | 0 => x
      | 1 => QPoly.eval (pderiv p) x
      | 2 => QPoly.eval (pderiv q) x
      | 3 => Q'.ofNat E
      | 4 => QPoly.eval p x
      | _ => QPoly.eval q x))

private theorem scaled_power_euler (c x : Q') (E : Nat) :
    euler (pscale c (polynomialPower coordinate (E+2))) E x ≈
      (2*c)*qpow x (E+2) := by
  let P := polynomialPower coordinate (E+2)
  have hd := Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_pscale c P) x)
    (eval_pscale c (pderiv P) x)
  have hmove : x*(c*QPoly.eval (pderiv P) x) ≈
      c*(x*QPoly.eval (pderiv P) x) := poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => x | 1 => c | _ => QPoly.eval (pderiv P) x)
  have hderivative : x*QPoly.eval (pderiv (pscale c P)) x ≈
      c*(Q'.ofNat (E+2)*qpow x (E+2)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hd)
      (Q'.eqv_trans _ _ _ hmove
        (Q'.mul_eqv_congr_left c _ _ (nome_power_generator x (E+2))))
  have hv : QPoly.eval (pscale c P) x ≈ c*qpow x (E+2) :=
    Q'.eqv_trans _ _ _ (eval_pscale c P x)
      (Q'.mul_eqv_congr_left c _ _ (coordinatePower_eval x (E+2)))
  have hn : Q'.ofNat (E+2) ≈ Q'.ofNat E+2 :=
    Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv E 2)
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.ofNat 2 ≈ (2 : Q')))
  have hs : euler (pscale c P) E x ≈
      c*((Q'.ofNat E+2)*qpow x (E+2)) + -(Q'.ofNat E*(c*qpow x (E+2))) :=
    Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ hderivative
        (Q'.mul_eqv_congr_left c _ _ (Q'.mul_eqv_congr_right _ _ _ hn)))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hv))
  exact Q'.eqv_trans _ _ _ hs (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.mul (.add (.var 1) (.const 2)) (.var 2)))
      (.neg (.mul (.var 1) (.mul (.var 0) (.var 2)))))
    (.mul (.mul (.const 2) (.var 0)) (.var 2)) (by decide)
    (fun | 0 => c | 1 => Q'.ofNat E | _ => qpow x (E+2)))

private theorem comparison_euler (p : Poly) (E : Nat) (c x : Q') :
    euler (comparisonNumerator p E c) E x ≈
      (2*c)*qpow x (E+2) + -(euler p E x) :=
  Q'.eqv_trans _ _ _ (euler_sub _ p E x)
    (Q'.add_eqv_congr_right _ _ _ (scaled_power_euler c x E))

private theorem comparison_laurent (p : Poly) (E : Nat) (c x : Q')
    (hx : (0 : Q') < x) :
    laurent (comparisonNumerator p E c) E x ≈ c*(x*x) + -(laurent p E x) := by
  have hv : QPoly.eval (comparisonNumerator p E c) x ≈
      c*(qpow x E*(x*x)) + -QPoly.eval p x :=
    Q'.eqv_trans _ _ _ (eval_psub _ p x)
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (eval_pscale c _ x)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (coordinatePower_eval x (E+2)))
          (Q'.mul_eqv_congr_left c _ _ (power_quadratic x E)))))
  have hr : (c*(qpow x E*(x*x)) + -QPoly.eval p x)*Q'.recip (qpow x E) ≈
      (qpow x E*Q'.recip (qpow x E))*(c*(x*x)) +
        -(QPoly.eval p x*Q'.recip (qpow x E)) := poly_identity_of_normal_eq
    (.mul (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.var 3))) (.var 4))
    (.add (.mul (.mul (.var 1) (.var 4)) (.mul (.var 0) (.var 2)))
      (.neg (.mul (.var 3) (.var 4)))) (by decide)
    (fun
      | 0 => c
      | 1 => qpow x E
      | 2 => x*x
      | 3 => QPoly.eval p x
      | _ => Q'.recip (qpow x E))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hv)
    (Q'.eqv_trans _ _ _ hr (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recip_eqv _ (power_positive hx E)))
        (Q'.one_mul_eqv _))))

/-- A literal normalized Euler upper bound pays the actual signed Laurent
increment. No sign of c or numerator, endpoint order or integration law is
assumed; the denominator is the original positive coordinate power. -/
theorem laurent_quadratic_increment (p : Poly) (E : Nat) (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (c : Q')
    (hEuler : ∀ x : Q', w ≤ x → x ≤ (1 : Q') →
      Q'.recip (qpow x E)*
        (x*QPoly.eval (pderiv p) x + -(Q'.ofNat E*QPoly.eval p x)) ≤
        2*(x*x)*c) :
    laurent p E 1 + -(laurent p E w) ≤ (1-w*w)*c := by
  have hsign : ∀ x : Q', w ≤ x → x ≤ (1 : Q') →
      (0 : Q') ≤ euler (comparisonNumerator p E c) E x := by
    intro x hwx hx1
    have hx : (0 : Q') < x := lt_of_lt_of_le hw0 hwx
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow x E)
      (hEuler x hwx hx1) (Q'.le_of_lt (power_positive hx E))
    have hcancel : qpow x E*(Q'.recip (qpow x E)*euler p E x) ≈ euler p E x :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recip_eqv _ (power_positive hx E)))
          (Q'.one_mul_eqv _))
    have hright : qpow x E*(2*(x*x)*c) ≈ (2*c)*qpow x (E+2) :=
      Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
        (.mul (.mul (.const 2) (.var 2)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => qpow x E | 1 => x*x | _ => c))
        (Q'.mul_eqv_congr_left (2*c) _ _ (Q'.eqv_symm (power_quadratic x E)))
    have hp : euler p E x ≤ (2*c)*qpow x (E+2) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
        (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hright))
    exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hp)
      (Q'.ge_of_eqv (comparison_euler p E c x))
  have horder := laurent_monotone (comparisonNumerator p E c) E w w 1 hw0
    (Q'.le_refl' _) (Q'.le_of_lt hw1) (Q'.le_refl' _) hsign
  have hc1 : c*((1 : Q')*1) ≈ c :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (Q'.one_mul_eqv 1))
      (Q'.mul_one_eqv c)
  have hbound : c*(w*w) + -(laurent p E w) ≤ c + -(laurent p E 1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (comparison_laurent p E c w hw0))
      (Q'.le_trans' _ _ _ horder
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (comparison_laurent p E c 1 (by decide)))
          (Q'.le_of_eqv (Q'.add_eqv_congr_right
            (c*((1 : Q')*1)) c (-(laurent p E 1)) hc1))))
  have hs := Q'.add_le_add_right _ _ (laurent p E 1 + -(c*(w*w))) hbound
  have hl : (c*(w*w) + -(laurent p E w)) +
      (laurent p E 1 + -(c*(w*w))) ≈ laurent p E 1 + -(laurent p E w) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 0))))
      (.add (.var 2) (.neg (.var 1))) (by decide)
      (fun | 0 => c*(w*w) | 1 => laurent p E w | _ => laurent p E 1)
  have hr : (c + -(laurent p E 1)) + (laurent p E 1 + -(c*(w*w))) ≈
      (1-w*w)*c := poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1)))
      (.add (.var 1) (.neg (.mul (.var 0) (.var 2)))))
    (.mul (.add (.const 1) (.neg (.var 2))) (.var 0)) (by decide)
    (fun | 0 => c | 1 => laurent p E 1 | _ => w*w)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

end YMGap.Continuum.RationalLaurentQuadraticIncrement

#print axioms YMGap.Continuum.RationalLaurentQuadraticIncrement.laurent_quadratic_increment
