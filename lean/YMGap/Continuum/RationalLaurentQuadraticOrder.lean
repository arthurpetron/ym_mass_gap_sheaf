/-
# Quadratic endpoint order for the actual Laurent function

The sole sign input is the literal strict-interior Euler derivative with
exponent E+2. Its actual polynomial numerator has nonnegative left endpoint
by finite Taylor/Archimedean closure. The existing quotient-order producer
then orders p(r)/r^(E+2), and positive-power cancellation gives the original
function p(r)/r^E bounded by r^2 times its value at one.

Signed/zero numerators and exponent zero are included. This scalar algebra
does not assert conditional variance, interacting estimates or uniformity.
-/

import YMGap.Continuum.RationalPolynomialStrictEndpoint
import YMGap.Continuum.RationalLaurentIntervalOrder

namespace YMGap.Continuum.RationalLaurentQuadraticOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (coordinate)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.HeatKernelRGStep (qpow_add lt_of_lt_of_le)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RationalLaurentIntervalOrder
open YMGap.Continuum.RationalPolynomialStrictEndpoint

local infix:50 " ≈ " => Q'.eqv

private theorem power_positive {r : Q'} (hr : (0 : Q') < r) :
    ∀ E : Nat, (0 : Q') < qpow r E
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | E+1 => Q'.mul_pos (power_positive hr E) hr

private theorem power_one : ∀ E : Nat, qpow 1 E ≈ 1
  | 0 => Q'.eqv_refl _
  | E+1 => Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (power_one E)

private theorem cancel_positive {a b c : Q'} (hc : (0 : Q') < c)
    (h : a*c ≈ b*c) : a ≈ b := by
  apply Int.le_antisymm
  · apply Q'.le_of_mul_le_mul_left (c := c) _ hc
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c a))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.le_of_eqv (Q'.mul_comm_eqv b c)))
  · apply Q'.le_of_mul_le_mul_left (c := c) _ hc
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c b))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) (Q'.le_of_eqv (Q'.mul_comm_eqv a c)))

private theorem laurent_cleared (p : Poly) (E : Nat) (r : Q')
    (hr : (0 : Q') < r) : laurent p E r * qpow r E ≈ QPoly.eval p r :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.mul_recip_eqv _ (power_positive hr E)))) (Q'.mul_one_eqv _))

private theorem laurent_one (p : Poly) (E : Nat) :
    laurent p E 1 ≈ QPoly.eval p 1 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (power_one E)))
      (laurent_cleared p E 1 (by decide)))

/-- Exact positive-power cancellation; no sign of the numerator is required. -/
theorem laurent_quadratic_pin (p : Poly) (E : Nat) (r : Q')
    (hr : (0 : Q') < r) :
    laurent p E r ≈ (r*r)*laurent p (E+2) r := by
  have htwo : qpow r 2 ≈ r*r :=
    Q'.mul_eqv_congr_right _ _ r (Q'.one_mul_eqv r)
  have hpower : qpow r (E+2) ≈ qpow r E*(r*r) :=
    Q'.eqv_trans _ _ _ (qpow_add r E 2) (Q'.mul_eqv_congr_left _ _ _ htwo)
  have hleft : laurent p E r * qpow r (E+2) ≈ QPoly.eval p r*(r*r) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hpower)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ (r*r) (laurent_cleared p E r hr)))
  have hright : ((r*r)*laurent p (E+2) r)*qpow r (E+2) ≈
      QPoly.eval p r*(r*r) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (r*r) _ _ (laurent_cleared p (E+2) r hr))
        (Q'.mul_comm_eqv _ _))
  exact cancel_positive (power_positive hr (E+2))
    (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright))

private def eulerPolynomial (p : Poly) (E : Nat) : Poly :=
  psub (pmul coordinate (pderiv p)) (pscale (Q'.ofNat (E+2)) p)

private theorem euler_eval (p : Poly) (E : Nat) (x : Q') :
    QPoly.eval (eulerPolynomial p E) x ≈
      x*QPoly.eval (pderiv p) x + -(Q'.ofNat (E+2)*QPoly.eval p x) := by
  have hc : QPoly.eval coordinate x ≈ x := poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => x)
  exact Q'.eqv_trans _ _ _ (eval_psub _ _ x)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (eval_pmul coordinate (pderiv p) x)
        (Q'.mul_eqv_congr_right _ _ _ hc))
      (Q'.neg_eqv_congr _ _ (eval_pscale (Q'.ofNat (E+2)) p x)))

private theorem eval_argument {x y : Q'} (h : x ≈ y) :
    ∀ p : Poly, QPoly.eval p x ≈ QPoly.eval p y
  | [] => Q'.eqv_refl _
  | c::p => Q'.add_eqv_congr_left c _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
        (Q'.mul_eqv_congr_left _ _ _ (eval_argument h p)))

/-- The actual strict Euler sign yields quadratic endpoint order of the
original Laurent evaluation, including its left endpoint. -/
theorem laurent_quadratic_upper (p : Poly) (E : Nat) (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hstrict : ∀ x : Q', w < x → x ≤ (1 : Q') →
      (0 : Q') ≤ x*QPoly.eval (pderiv p) x + -(Q'.ofNat (E+2)*QPoly.eval p x))
    (r : Q') (hr : w ≤ r) (hr1 : r ≤ (1 : Q')) :
    laurent p E r ≤ (r*r)*laurent p E 1 := by
  have hleft : (0 : Q') ≤ QPoly.eval (eulerPolynomial p E) w :=
    nonnegative_at_left_endpoint (eulerPolynomial p E) w 1 (Q'.le_of_lt hw0)
      hw1 (Q'.le_refl' _) (fun x hx hx1 =>
        Q'.le_trans' _ _ _ (hstrict x hx hx1) (Q'.ge_of_eqv (euler_eval p E x)))
  have hclosed : ∀ x : Q', r ≤ x → x ≤ (1 : Q') →
      (0 : Q') ≤ x*QPoly.eval (pderiv p) x + -(Q'.ofNat (E+2)*QPoly.eval p x) := by
    intro x hrx hx1
    if hx : w < x then
      exact hstrict x hx hx1
    else
      have hxw : x ≤ w := by
        change x.num*(w.den : Int) ≤ w.num*(x.den : Int)
        have hnot : ¬w.num*(x.den : Int) < x.num*(w.den : Int) := hx
        omega
      have hsame : x ≈ w := Int.le_antisymm hxw (Q'.le_trans' _ _ _ hr hrx)
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ hleft (Q'.ge_of_eqv (eval_argument hsame (eulerPolynomial p E))))
        (Q'.le_of_eqv (euler_eval p E x))
  have horder := laurent_monotone p (E+2) w r 1 hw0 hr hr1 (Q'.le_refl' _) hclosed
  have hrpos : (0 : Q') < r := lt_of_lt_of_le hw0 hr
  have hrr : (0 : Q') ≤ r*r := Q'.mul_nonneg _ _ (Q'.le_of_lt hrpos) (Q'.le_of_lt hrpos)
  have hone : laurent p (E+2) 1 ≈ laurent p E 1 :=
    Q'.eqv_trans _ _ _ (laurent_one p (E+2)) (Q'.eqv_symm (laurent_one p E))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (laurent_quadratic_pin p E r hrpos))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (r*r) horder hrr)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (r*r) _ _ hone)))

end YMGap.Continuum.RationalLaurentQuadraticOrder

#print axioms YMGap.Continuum.RationalLaurentQuadraticOrder.laurent_quadratic_pin
#print axioms YMGap.Continuum.RationalLaurentQuadraticOrder.laurent_quadratic_upper
