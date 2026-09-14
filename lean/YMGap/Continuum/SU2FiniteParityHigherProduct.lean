/-
# Finite sharp heat products in parity/higher-label coordinates

The factorization retains the exact original squared dimensions and
Casimir sum. Its upper bound has one odd activity per parity bit and
one higher activity per quotient unit, at arbitrary finite support and
without assuming any admissibility or independence of Haar variables.
-/

import YMGap.Continuum.SU2ParityHigherHeatEnvelope

namespace YMGap.Continuum.SU2FiniteParityHigherProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2ParityHigherHeatEnvelope

local infix:50 " ≈ " => Q'.eqv

def parityCount (state : Nat → Nat) : List Nat → Nat
  | [] => 0
  | id::ids => state id % 2 + parityCount state ids

def higherCount (state : Nat → Nat) : List Nat → Nat
  | [] => 0
  | id::ids => state id / 2 + higherCount state ids

def heatProduct (w : Q') (state : Nat → Nat) (ids : List Nat) : Q' :=
  eliminateLinks (fun id => heatWeight w (state id)) ids

theorem heatProduct_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (state : Nat → Nat) :
    ∀ ids : List Nat, (0 : Q') ≤ heatProduct w state ids
  | [] => Q'.zero_le_one
  | id::ids => Q'.mul_nonneg _ _ (heatWeight_nonnegative hw (state id)) (heatProduct_nonnegative hw state ids)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem square_weight_regroup (a b p q : Q') :
    ((a*a)*p)*((b*b)*q) ≈ ((a*b)*(a*b))*(p*q) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.mul (.mul (.var 1) (.var 1)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
    (by decide) (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then p else q)

theorem heatProduct_pin (w : Q') (state : Nat → Nat) : ∀ ids : List Nat,
    heatProduct w state ids ≈
      (dimensionProduct state ids * dimensionProduct state ids) * qpow w (casimirSum state ids)
  | [] => by change (1 : Q') ≈ (1*1)*1; decide
  | id::ids => by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (heatWeight w (state id)) _ _ (heatProduct_pin w state ids)) ?_
    refine Q'.eqv_trans _ _ _ (square_weight_regroup (dimQ (state id)) (dimensionProduct state ids)
      (qpow w (c4 (state id))) (qpow w (casimirSum state ids))) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (HeatKernelRGStep.qpow_add w _ _))

theorem heatProduct_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (state : Nat → Nat) : ∀ ids : List Nat,
    heatProduct w state ids ≤ qpow (oddRate w) (parityCount state ids) *
      qpow (higherRate w) (higherCount state ids)
  | [] => by change (1 : Q') ≤ 1*1; decide
  | id::ids => by
    have ha := heatWeight_bound hw0 hw1 (state id)
    have ht := heatProduct_bound hw0 hw1 state ids
    have h0 := Q'.mul_le_mul_of_nonneg_right _ _ (heatProduct w state ids) ha
      (heatProduct_nonnegative hw0 state ids)
    have h1 := Q'.mul_le_mul_of_nonneg_left _ _
      (qpow (oddRate w) (state id%2) * qpow (higherRate w) (state id/2)) ht
      (Q'.mul_nonneg _ _ (qpow_nonneg _ (oddRate_nonnegative hw0) _) (qpow_nonneg _ (higherRate_nonnegative hw0) _))
    refine Q'.le_trans' _ _ _ h0 (Q'.le_trans' _ _ _ h1 ?_)
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (mul_shuffle _ _ _ _)
      (qmul (Q'.eqv_symm (HeatKernelRGStep.qpow_add (oddRate w) _ _))
        (Q'.eqv_symm (HeatKernelRGStep.qpow_add (higherRate w) _ _))))

theorem pairedProduct_pin (w : Q') (left right : Nat → Nat) (ids : List Nat) :
    heatProduct w left ids * heatProduct w right ids ≈
      ((dimensionProduct left ids * dimensionProduct right ids) *
        (dimensionProduct left ids * dimensionProduct right ids)) *
        qpow w (casimirSum left ids + casimirSum right ids) :=
  Q'.eqv_trans _ _ _ (qmul (heatProduct_pin w left ids) (heatProduct_pin w right ids))
    (Q'.eqv_trans _ _ _ (square_weight_regroup _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (HeatKernelRGStep.qpow_add w _ _))))

theorem pairedProduct_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (left right : Nat → Nat) (ids : List Nat) :
    heatProduct w left ids * heatProduct w right ids ≤
      qpow (oddRate w) (parityCount left ids + parityCount right ids) *
        qpow (higherRate w) (higherCount left ids + higherCount right ids) := by
  have hl := heatProduct_bound hw0 hw1 left ids
  have hr := heatProduct_bound hw0 hw1 right ids
  have h0 := Q'.mul_le_mul_of_nonneg_right _ _ (heatProduct w right ids) hl (heatProduct_nonnegative hw0 right ids)
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (oddRate w) (parityCount left ids) * qpow (higherRate w) (higherCount left ids)) hr
    (Q'.mul_nonneg _ _ (qpow_nonneg _ (oddRate_nonnegative hw0) _) (qpow_nonneg _ (higherRate_nonnegative hw0) _))
  exact Q'.le_trans' _ _ _ h0 (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (mul_shuffle _ _ _ _)
      (qmul (Q'.eqv_symm (HeatKernelRGStep.qpow_add (oddRate w) _ _))
        (Q'.eqv_symm (HeatKernelRGStep.qpow_add (higherRate w) _ _))))))

end YMGap.Continuum.SU2FiniteParityHigherProduct

#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.parityCount
#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.higherCount
#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.heatProduct
#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.heatProduct_nonnegative
#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.heatProduct_pin
#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.heatProduct_bound
#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.pairedProduct_pin
#print axioms YMGap.Continuum.SU2FiniteParityHigherProduct.pairedProduct_bound
