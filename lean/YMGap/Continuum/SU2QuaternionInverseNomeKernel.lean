/-
# Actual inverse-nome kernel as finite common-denominator rows

All labels zero through K are retained. The common exponent is c4 K, and
the numerator rows contain the actual original dimensions and characters.
The Euler numerator is computed with literal QPoly pderiv, not defined by a
desired chain rule. Positive r is the only analytic-domain premise; w may
be signed, and K=0 is included. These coefficient identities preserve every
shared input/output spectator when inserted into the conditional heat map.
No positivity, variance estimate or scaling-family conclusion is asserted.
-/

import YMGap.Continuum.SU2QuaternionConditionalHeatGenerator
import YMGap.Continuum.RationalLaurentIntervalOrder

namespace YMGap.Continuum.SU2QuaternionInverseNomeKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower coordinate)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow dimQ c4)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.HeatKernelRGStep (qpow_add)
open YMGap.Continuum.SU2CharacterVacuumHaar (coeffAt)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeCharacter)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionConditionalHeatGenerator
open YMGap.Continuum.RationalLaurentIntervalOrder (coordinatePower_eval)
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator (nome_power_generator)

local infix:50 " ≈ " => Q'.eqv

def inverseNomeExponent (K : Nat) : Nat := c4 K

/-- Actual polynomial numerator coefficient with a common coordinate power. -/
def inverseNomeCoefficient (w : Q') (K spin : Nat) : Poly :=
  pscale (coeffW w spin)
    (polynomialPower coordinate (inverseNomeExponent K - c4 spin))

/-- Original characters in the original inclusive packet order. -/
def inverseNomeRows (w : Q') (K : Nat) : List (Poly × RatPoly) :=
  (List.range (K+1)).map fun spin =>
    (inverseNomeCoefficient w K spin, relativeCharacter spin)

def inverseNomeNumerator (w : Q') (K : Nat) (r : Q') : RatPoly :=
  polySum ((inverseNomeRows w K).map fun row => polySmul (QPoly.eval row.1 r) row.2)

/-- Literal finite Euler derivative of the common-denominator numerator. -/
def inverseNomeEulerNumerator (w : Q') (K : Nat) (r : Q') : RatPoly :=
  polySum ((inverseNomeRows w K).map fun row =>
    polySmul (r * QPoly.eval (pderiv row.1) r +
      -(Q'.ofNat (inverseNomeExponent K) * QPoly.eval row.1 r)) row.2)

private theorem power_positive {r : Q'} (hr : (0 : Q') < r) :
    ∀ n : Nat, (0 : Q') < qpow r n
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | n+1 => Q'.mul_pos (power_positive hr n) hr

private theorem cancel_positive {a b c : Q'} (hc : (0 : Q') < c)
    (h : a*c ≈ b*c) : a ≈ b := by
  apply Int.le_antisymm
  · apply Q'.le_of_mul_le_mul_left (c := c) _ hc
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c a))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.le_of_eqv (Q'.mul_comm_eqv b c)))
  · apply Q'.le_of_mul_le_mul_left (c := c) _ hc
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c b))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) (Q'.le_of_eqv (Q'.mul_comm_eqv a c)))

private theorem inverse_base_cleared (w r : Q') (hr : (0 : Q') < r) :
    (w * Q'.recip r) * r ≈ w :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recip_eqv r hr)))
      (Q'.mul_one_eqv w))

private theorem inverse_power_cleared (w r : Q') (hr : (0 : Q') < r) :
    ∀ n : Nat, qpow (w * Q'.recip r) n * qpow r n ≈ qpow w n
  | 0 => by
      change (1 * 1 : Q') ≈ 1
      decide
  | n+1 =>
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
          (fun | 0 => qpow (w*Q'.recip r) n | 1 => w*Q'.recip r
               | 2 => qpow r n | _ => r))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (inverse_power_cleared w r hr n))
          (Q'.mul_eqv_congr_left _ _ _ (inverse_base_cleared w r hr)))

private theorem inverse_power_pin (w r : Q') (E d : Nat)
    (hr : (0 : Q') < r) (hd : d ≤ E) :
    (qpow w d * qpow r (E-d)) * Q'.recip (qpow r E) ≈
      qpow (w * Q'.recip r) d := by
  have hE : d + (E-d) = E := by omega
  have hp : qpow r E ≈ qpow r d * qpow r (E-d) := by
    simpa only [hE] using qpow_add r d (E-d)
  have hl : ((qpow w d * qpow r (E-d)) * Q'.recip (qpow r E)) * qpow r E ≈
      qpow w d * qpow r (E-d) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.mul_recip_eqv _ (power_positive hr E)))) (Q'.mul_one_eqv _))
  have hh : qpow (w * Q'.recip r) d * qpow r E ≈ qpow w d * qpow r (E-d) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ (inverse_power_cleared w r hr d)))
  exact cancel_positive (power_positive hr E) (Q'.eqv_trans _ _ _ hl (Q'.eqv_symm hh))

private theorem label_exponent_le {spin K : Nat} (hs : spin ≤ K) : c4 spin ≤ c4 K :=
  Nat.mul_le_mul hs (Nat.add_le_add_right hs 2)

private theorem scaled_power_eval (a r : Q') (n : Nat) :
    QPoly.eval (pscale a (polynomialPower coordinate n)) r ≈ a * qpow r n :=
  Q'.eqv_trans _ _ _ (eval_pscale a _ r)
    (Q'.mul_eqv_congr_left a _ _ (coordinatePower_eval r n))

private theorem scaled_power_euler (a r : Q') (n : Nat) :
    r * QPoly.eval (pderiv (pscale a (polynomialPower coordinate n))) r ≈
      Q'.ofNat n * QPoly.eval (pscale a (polynomialPower coordinate n)) r := by
  have hd := Q'.eqv_trans _ _ _
    (coefficient_eval (pderiv_pscale a (polynomialPower coordinate n)) r)
    (eval_pscale a _ r)
  have hreorder : r * (a * QPoly.eval (pderiv (polynomialPower coordinate n)) r) ≈
      a * (r * QPoly.eval (pderiv (polynomialPower coordinate n)) r) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => r | 1 => a | _ => QPoly.eval (pderiv (polynomialPower coordinate n)) r)
  have hfinish : a * (Q'.ofNat n * qpow r n) ≈ Q'.ofNat n * (a * qpow r n) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => a | 1 => Q'.ofNat n | _ => qpow r n)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left r _ _ hd)
    (Q'.eqv_trans _ _ _ hreorder (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _ (nome_power_generator r n))
      (Q'.eqv_trans _ _ _ hfinish
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (scaled_power_eval a r n))))))

/-- Actual numerator row divided by the common power equals its inverse-nome
packet coefficient. Positive r, but no restriction on the signed nome w. -/
theorem inverseNomeCoefficient_scaled_eval (w r : Q') (K spin : Nat)
    (hr : (0 : Q') < r) (hs : spin ≤ K) :
    Q'.recip (qpow r (inverseNomeExponent K)) *
      QPoly.eval (inverseNomeCoefficient w K spin) r ≈ coeffW (w*Q'.recip r) spin := by
  have hv := scaled_power_eval (coeffW w spin) r (inverseNomeExponent K-c4 spin)
  have hr' : Q'.recip (qpow r (inverseNomeExponent K)) *
      (coeffW w spin * qpow r (inverseNomeExponent K-c4 spin)) ≈
      dimQ spin * ((qpow w (c4 spin) * qpow r (inverseNomeExponent K-c4 spin)) *
        Q'.recip (qpow r (inverseNomeExponent K))) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 1) (.mul (.mul (.var 2) (.var 3)) (.var 0))) (by decide)
      (fun | 0 => Q'.recip (qpow r (inverseNomeExponent K)) | 1 => dimQ spin
           | 2 => qpow w (c4 spin) | _ => qpow r (inverseNomeExponent K-c4 spin))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hv)
    (Q'.eqv_trans _ _ _ hr' (Q'.mul_eqv_congr_left (dimQ spin) _ _
      (inverse_power_pin w r (inverseNomeExponent K) (c4 spin) hr (label_exponent_le hs))))

/-- Literal Euler derivative of a numerator row equals minus its original
label Casimir times the row. Includes the zero label and cutoff zero. -/
theorem inverseNomeCoefficient_euler (w r : Q') (K spin : Nat) (hs : spin ≤ K) :
    r * QPoly.eval (pderiv (inverseNomeCoefficient w K spin)) r +
      -(Q'.ofNat (inverseNomeExponent K) * QPoly.eval (inverseNomeCoefficient w K spin) r) ≈
      -(Q'.ofNat (c4 spin) * QPoly.eval (inverseNomeCoefficient w K spin) r) := by
  let n := inverseNomeExponent K-c4 spin
  have hn : n + c4 spin = inverseNomeExponent K := Nat.sub_add_cancel (label_exponent_le hs)
  have hnat : Q'.ofNat (inverseNomeExponent K) ≈ Q'.ofNat n + Q'.ofNat (c4 spin) := by
    simpa only [hn] using Q'.ofNat_add_eqv n (c4 spin)
  have he := scaled_power_euler (coeffW w spin) r n
  have hreplace :
      r * QPoly.eval (pderiv (inverseNomeCoefficient w K spin)) r +
        -(Q'.ofNat (inverseNomeExponent K) * QPoly.eval (inverseNomeCoefficient w K spin) r) ≈
      Q'.ofNat n * QPoly.eval (inverseNomeCoefficient w K spin) r +
        -((Q'.ofNat n + Q'.ofNat (c4 spin)) * QPoly.eval (inverseNomeCoefficient w K spin) r) :=
    Q'.add_eqv_congr' he
      (Q'.neg_eqv_congr
        (Q'.ofNat (inverseNomeExponent K) * QPoly.eval (inverseNomeCoefficient w K spin) r)
        ((Q'.ofNat n + Q'.ofNat (c4 spin)) * QPoly.eval (inverseNomeCoefficient w K spin) r)
        (Q'.mul_eqv_congr_right (Q'.ofNat (inverseNomeExponent K))
          (Q'.ofNat n + Q'.ofNat (c4 spin))
          (QPoly.eval (inverseNomeCoefficient w K spin) r) hnat))
  have halg : Q'.ofNat n * QPoly.eval (inverseNomeCoefficient w K spin) r +
        -((Q'.ofNat n+Q'.ofNat (c4 spin))*QPoly.eval (inverseNomeCoefficient w K spin) r) ≈
      -(Q'.ofNat (c4 spin)*QPoly.eval (inverseNomeCoefficient w K spin) r) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.add (.var 0) (.var 1)) (.var 2))))
      (.neg (.mul (.var 1) (.var 2))) (by decide)
      (fun | 0 => Q'.ofNat n | 1 => Q'.ofNat (c4 spin)
           | _ => QPoly.eval (inverseNomeCoefficient w K spin) r)
  exact Q'.eqv_trans _ _ _ hreplace halg

private theorem row_chain (w r : Q') (K spin : Nat)
    (hr : (0 : Q') < r) (hs : spin ≤ K) :
    Q'.recip (qpow r (inverseNomeExponent K)) *
      (r*QPoly.eval (pderiv (inverseNomeCoefficient w K spin)) r +
        -(Q'.ofNat (inverseNomeExponent K)*QPoly.eval (inverseNomeCoefficient w K spin) r)) ≈
      (-(w*Q'.recip r))*QPoly.eval (pderiv (nomeCoefficient spin)) (w*Q'.recip r) := by
  let v := w*Q'.recip r
  have hl : Q'.recip (qpow r (inverseNomeExponent K)) *
      (-(Q'.ofNat (c4 spin)*QPoly.eval (inverseNomeCoefficient w K spin) r)) ≈
      -(Q'.ofNat (c4 spin) * (Q'.recip (qpow r (inverseNomeExponent K))*
        QPoly.eval (inverseNomeCoefficient w K spin) r)) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.neg (.mul (.var 1) (.var 2))))
      (.neg (.mul (.var 1) (.mul (.var 0) (.var 2)))) (by decide)
      (fun | 0 => Q'.recip (qpow r (inverseNomeExponent K)) | 1 => Q'.ofNat (c4 spin)
           | _ => QPoly.eval (inverseNomeCoefficient w K spin) r)
  have hv : v * QPoly.eval (pderiv (nomeCoefficient spin)) v ≈ Q'.ofNat (c4 spin)*coeffW v spin :=
    Q'.eqv_trans _ _ _ (scaled_power_euler (dimQ spin) v (c4 spin))
      (Q'.mul_eqv_congr_left _ _ _ (scaled_power_eval (dimQ spin) v (c4 spin)))
  have hh : (-v)*QPoly.eval (pderiv (nomeCoefficient spin)) v ≈
      -(Q'.ofNat (c4 spin)*coeffW v spin) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv _ _) (Q'.neg_eqv_congr _ _ hv)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (inverseNomeCoefficient_euler w r K spin hs))
    (Q'.eqv_trans _ _ _ hl (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
        (inverseNomeCoefficient_scaled_eval w r K spin hr hs))) (Q'.eqv_symm hh)))

private theorem polySum_map (f : Nat → RatPoly) : ∀ ids : List Nat,
    polySum (ids.map f) = finitePolySum f ids
  | [] => rfl
  | _::ids => by simp only [List.map, polySum, finitePolySum, polySum_map f ids]

private theorem scale_sum (a : Q') (f : Nat → RatPoly) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polySmul a (finitePolySum f ids))
      (finitePolySum (fun i => polySmul a (f i)) ids)
  | [] => RatPolyCoeffEqv.smul_zero a
  | _::ids => (RatPolyCoeffEqv.smul_add a _ _).trans
      ((RatPolyCoeffEqv.refl _).add (scale_sum a f ids))

private theorem sum_congr (f g : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → RatPolyCoeffEqv (f i) (g i)) →
      RatPolyCoeffEqv (finitePolySum f ids) (finitePolySum g ids)
  | [], _ => .refl _
  | i::ids, h => (h i List.mem_cons_self).add
      (sum_congr f g ids (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- Exact common-denominator representation of the ORIGINAL full prefix. -/
theorem inverseNomeKernel_original_pin (w r : Q') (K : Nat) (hr : (0 : Q') < r) :
    RatPolyCoeffEqv
      (polySmul (Q'.recip (qpow r (inverseNomeExponent K))) (inverseNomeNumerator w K r))
      (relativeHeat (w*Q'.recip r) K) := by
  have hn : inverseNomeNumerator w K r = finitePolySum
      (fun spin => polySmul (QPoly.eval (inverseNomeCoefficient w K spin) r) (relativeCharacter spin))
      (List.range (K+1)) := by
    simp only [inverseNomeNumerator, inverseNomeRows, List.map_map, Function.comp_def]
    exact polySum_map _ _
  rw [hn]
  refine (scale_sum _ _ _).trans ?_
  unfold relativeHeat
  apply sum_congr
  intro spin hspin
  have hs : spin ≤ K := Nat.le_of_lt_succ (List.mem_range.mp hspin)
  have hc := coeffAt_heatKernelPacket (w := w*Q'.recip r) (List.mem_range.mp hspin)
  exact (RatPolyCoeffEqv.smul_assoc _ _ _).trans
    (RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_trans _ _ _ (inverseNomeCoefficient_scaled_eval w r K spin hr hs)
        (Q'.eqv_of_eq hc.symm)) _)

/-- True inverse-nome CHAIN identity for literal numerator pderiv data.
There is no conclusion-defined derivative and no omission of high labels. -/
theorem inverseNomeEuler_chain_pin (w r : Q') (K : Nat) (hr : (0 : Q') < r) :
    RatPolyCoeffEqv
      (polySmul (Q'.recip (qpow r (inverseNomeExponent K))) (inverseNomeEulerNumerator w K r))
      (polySmul (-(w*Q'.recip r)) (formalConditionalKernelDerivative (w*Q'.recip r) K)) := by
  have hn : inverseNomeEulerNumerator w K r = finitePolySum
      (fun spin => polySmul
        (r*QPoly.eval (pderiv (inverseNomeCoefficient w K spin)) r +
          -(Q'.ofNat (inverseNomeExponent K)*QPoly.eval (inverseNomeCoefficient w K spin) r))
        (relativeCharacter spin)) (List.range (K+1)) := by
    simp only [inverseNomeEulerNumerator, inverseNomeRows, List.map_map, Function.comp_def]
    exact polySum_map _ _
  rw [hn]
  refine (scale_sum _ _ _).trans ?_
  refine (sum_congr _ _ (List.range (K+1)) ?_).trans (scale_sum _ _ _).symm
  intro spin hspin
  have hs : spin ≤ K := Nat.le_of_lt_succ (List.mem_range.mp hspin)
  exact (RatPolyCoeffEqv.smul_assoc _ _ _).trans
    ((RatPolyCoeffEqv.smul_coefficient (row_chain w r K spin hr hs) _).trans
      (RatPolyCoeffEqv.smul_assoc _ _ _).symm)

#print axioms inverseNomeCoefficient_scaled_eval
#print axioms inverseNomeCoefficient_euler
#print axioms inverseNomeKernel_original_pin
#print axioms inverseNomeEuler_chain_pin

end YMGap.Continuum.SU2QuaternionInverseNomeKernel
