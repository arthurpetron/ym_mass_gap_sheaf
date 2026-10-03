/-
# Endpoint order of a literal finite Laurent function

The numerator is any signed rational polynomial and the denominator is the
ACTUAL coordinate power. The Euler derivative sign is converted to the formal
quotient-rule sign without dividing that derivative or changing the function.
The positive denominator floor is the computed w^E. Exponent zero and zero or
signed numerators are included. This is finite rational order, not a conditional
variance estimate or a scaling/continuum claim.
-/

import YMGap.Continuum.RationalFunctionIntervalOrder
import YMGap.Continuum.SU2QuaternionHeadHeatGenerator
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.RationalLaurentIntervalOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower coordinate)
open YMGap.Continuum.RationalFunctionIntervalOrder
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.HeatKernelGap (qpow_mono)
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator (nome_power_generator)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Literal signed Laurent evaluation, using the project's right-fold power. -/
def laurent (p : Poly) (E : Nat) (x : Q') : Q' :=
  QPoly.eval p x * Q'.recip (qpow x E)

private theorem coordinate_eval (x : Q') : QPoly.eval coordinate x ≈ x :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => x)

/-- Exact evaluation of the actual denominator, including exponent zero. -/
theorem coordinatePower_eval (x : Q') : ∀ E : Nat,
    QPoly.eval (polynomialPower coordinate E) x ≈ qpow x E
  | 0 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ 0 (Q'.mul_zero_eqv x)) (q_add_zero_eqv 1)
  | E+1 => Q'.eqv_trans _ _ _ (eval_pmul coordinate (polynomialPower coordinate E) x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ x _ (coordinate_eval x))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left x _ _ (coordinatePower_eval x E))
          (Q'.mul_comm_eqv x (qpow x E))))

private theorem power_positive {x : Q'} (hx : (0 : Q') < x) :
    ∀ E : Nat, (0 : Q') < qpow x E
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | E+1 => Q'.mul_pos (power_positive hx E) hx

private theorem cancel_positive_equivalence {u v c : Q'}
    (hc : (0 : Q') < c) (h : u*c ≈ v*c) : u ≈ v := by
  apply Int.le_antisymm
  · apply Q'.le_of_mul_le_mul_left (c := c) _ hc
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c u))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.le_of_eqv (Q'.mul_comm_eqv v c)))
  · apply Q'.le_of_mul_le_mul_left (c := c) _ hc
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c v))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) (Q'.le_of_eqv (Q'.mul_comm_eqv u c)))

/-- The literal Laurent function equals the actual polynomial quotient; this
does not silently identify the two power-fold conventions definitionally. -/
theorem laurent_quotient_pin (p : Poly) (E : Nat) (x : Q')
    (hx : (0 : Q') < x) :
    laurent p E x ≈ quotient p (polynomialPower coordinate E) x := by
  have hp : (0 : Q') < qpow x E := power_positive hx E
  have he := coordinatePower_eval x E
  have hden : (0 : Q') < QPoly.eval (polynomialPower coordinate E) x :=
    HeatKernelRGStep.lt_of_lt_of_le hp (Q'.ge_of_eqv he)
  have hl : laurent p E x * qpow x E ≈ QPoly.eval p x := by
    unfold laurent
    exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recip_eqv _ hp)))
        (Q'.mul_one_eqv _))
  have hq : quotient p (polynomialPower coordinate E) x * qpow x E ≈
      QPoly.eval p x :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm he))
      (quotient_denominator_pin p (polynomialPower coordinate E) x hden)
  exact cancel_positive_equivalence hp (Q'.eqv_trans _ _ _ hl (Q'.eqv_symm hq))

/-- Cleared Euler identity for the ACTUAL quotient derivative numerator.
No inverse or positive-x premise is needed here, including x=0 and E=0. -/
theorem euler_derivativeNumerator_pin (p : Poly) (E : Nat) (x : Q') :
    x * QPoly.eval (derivativeNumerator p (polynomialPower coordinate E)) x ≈
      qpow x E * (x * QPoly.eval (pderiv p) x + -(Q'.ofNat E * QPoly.eval p x)) := by
  let q := polynomialPower coordinate E
  have hstart := Q'.mul_eqv_congr_left x _ _ (derivativeNumerator_eval p q x)
  have hr : x * (QPoly.eval q x * QPoly.eval (pderiv p) x +
      -(QPoly.eval p x * QPoly.eval (pderiv q) x)) ≈
      QPoly.eval q x * (x * QPoly.eval (pderiv p) x) +
        -(QPoly.eval p x * (x * QPoly.eval (pderiv q) x)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 4)))))
      (.add (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (.neg (.mul (.var 3) (.mul (.var 0) (.var 4))))) (by decide)
      (fun | 0 => x | 1 => QPoly.eval q x | 2 => QPoly.eval (pderiv p) x
           | 3 => QPoly.eval p x | _ => QPoly.eval (pderiv q) x)
  have hm : QPoly.eval q x * (x * QPoly.eval (pderiv p) x) +
        -(QPoly.eval p x * (x * QPoly.eval (pderiv q) x)) ≈
      qpow x E * (x * QPoly.eval (pderiv p) x) +
        -(QPoly.eval p x * (Q'.ofNat E * qpow x E)) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (coordinatePower_eval x E))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ (nome_power_generator x E)))
  have hf : qpow x E * (x * QPoly.eval (pderiv p) x) +
        -(QPoly.eval p x * (Q'.ofNat E * qpow x E)) ≈
      qpow x E * (x * QPoly.eval (pderiv p) x + -(Q'.ofNat E * QPoly.eval p x)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.var 3) (.mul (.var 4) (.var 0)))))
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 4) (.var 3)))))
      (by decide)
      (fun | 0 => qpow x E | 1 => x | 2 => QPoly.eval (pderiv p) x
           | 3 => QPoly.eval p x | _ => Q'.ofNat E)
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _ hm hf))

/-- Genuine endpoint order of p(x)/x^E on [a,b] contained in [w,1].
The sole sign input is the literal Euler derivative numerator, not endpoint
order. The denominator floor is computed from w and E, not supplied. -/
theorem laurent_monotone (p : Poly) (E : Nat) (w a b : Q')
    (hw : (0 : Q') < w) (hwa : w ≤ a) (hab : a ≤ b) (hb : b ≤ (1 : Q'))
    (hEuler : ∀ x : Q', a ≤ x → x ≤ b →
      (0 : Q') ≤ x * QPoly.eval (pderiv p) x + -(Q'.ofNat E * QPoly.eval p x)) :
    laurent p E a ≤ laurent p E b := by
  have hapos : (0 : Q') < a := HeatKernelRGStep.lt_of_lt_of_le hw hwa
  have hbpos : (0 : Q') < b := HeatKernelRGStep.lt_of_lt_of_le hapos hab
  have hfloor : ∀ x : Q', a ≤ x → x ≤ b →
      qpow w E ≤ QPoly.eval (polynomialPower coordinate E) x := by
    intro x hax _
    exact Q'.le_trans' _ _ _
      (qpow_mono (Q'.le_of_lt hw) (Q'.le_trans' _ _ _ hwa hax) E)
      (Q'.ge_of_eqv (coordinatePower_eval x E))
  have hsign : ∀ x : Q', a ≤ x → x ≤ b →
      (0 : Q') ≤ QPoly.eval (derivativeNumerator p (polynomialPower coordinate E)) x := by
    intro x hax hxb
    have hx : (0 : Q') < x := HeatKernelRGStep.lt_of_lt_of_le hapos hax
    have he := euler_derivativeNumerator_pin p E x
    have hm : (0 : Q') ≤ qpow x E *
        (x * QPoly.eval (pderiv p) x + -(Q'.ofNat E * QPoly.eval p x)) :=
      Q'.mul_nonneg _ _ (Q'.le_of_lt (power_positive hx E)) (hEuler x hax hxb)
    exact Q'.nonneg_of_mul_pos hx (Q'.le_trans' _ _ _ hm (Q'.ge_of_eqv he))
  have horder := quotient_monotone p (polynomialPower coordinate E) a b (qpow w E)
    (Q'.le_of_lt hapos) hab hb (power_positive hw E) hfloor hsign
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (laurent_quotient_pin p E a hapos))
    (Q'.le_trans' _ _ _ horder (Q'.ge_of_eqv (laurent_quotient_pin p E b hbpos)))

#print axioms laurent
#print axioms coordinatePower_eval
#print axioms laurent_quotient_pin
#print axioms euler_derivativeNumerator_pin
#print axioms laurent_monotone

end YMGap.Continuum.RationalLaurentIntervalOrder
