/-
# Finite polynomial-valued nome rows

All differentiation is literal coefficient-list formal differentiation.
Product and Euler pins hold at RatPoly coefficient strength, retaining every
shared variable. No analytic derivative or heat-generator premise is assumed.
-/

import YMGap.Constructive.QPolyCoefficientEvaluation
import YMGap.Constructive.QPolyPositivePrimitive
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.RatPolyNomeRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Constructive.QPolyPositivePrimitive (coordinate)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

local infix:50 " ≈ " => Q'.eqv

abbrev Rows := List (Poly × RatPoly)

def evalRows (rows : Rows) (r : Q') : RatPoly :=
  polySum (rows.map fun row => polySmul (QPoly.eval row.1 r) row.2)

def derivativeRows (rows : Rows) : Rows :=
  rows.map fun row => (pderiv row.1, row.2)

def mulRows (A B : Rows) : Rows :=
  A.flatMap fun a => B.map fun b => (pmul a.1 b.1, polyMul a.2 b.2)

def mapRows (f : RatPoly → RatPoly) (A : Rows) : Rows :=
  A.map fun a => (a.1, f a.2)

def eulerRows (E : Nat) (A : Rows) : Rows :=
  A.map fun a => (psub (pmul coordinate (pderiv a.1)) (pscale (Q'.ofNat E) a.1), a.2)

private theorem sum_congr {α : Type} (f g : α → RatPoly) (xs : List α)
    (h : ∀ a, a ∈ xs → RatPolyCoeffEqv (f a) (g a)) :
    RatPolyCoeffEqv (polySum (xs.map f)) (polySum (xs.map g)) := by
  induction xs with
  | nil => exact .refl _
  | cons a xs ih =>
      exact (h a List.mem_cons_self).add
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem sum_add {α : Type} (f g : α → RatPoly) (xs : List α) :
    RatPolyCoeffEqv (polySum (xs.map fun a => polyAdd (f a) (g a)))
      (polyAdd (polySum (xs.map f)) (polySum (xs.map g))) := by
  induction xs with
  | nil => exact .refl _
  | cons a xs ih =>
      exact ((RatPolyCoeffEqv.refl _).add ih).trans
        (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem sum_scale {α : Type} (c : Q') (f : α → RatPoly) (xs : List α) :
    RatPolyCoeffEqv (polySum (xs.map fun a => polySmul c (f a)))
      (polySmul c (polySum (xs.map f))) := by
  induction xs with
  | nil => exact (RatPolyCoeffEqv.smul_zero c).symm
  | cons a xs ih =>
      exact ((RatPolyCoeffEqv.refl _).add ih).trans
        (RatPolyCoeffEqv.smul_add c _ _).symm

private theorem sum_neg {α : Type} (f : α → RatPoly) (xs : List α) :
    RatPolyCoeffEqv (polySum (xs.map fun a => polyNeg (f a)))
      (polyNeg (polySum (xs.map f))) := by
  induction xs with
  | nil => exact .refl _
  | cons a xs ih =>
      exact ((RatPolyCoeffEqv.refl _).add ih).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.neg (.var 0)) (.neg (.var 1)))
          (.neg (.add (.var 0) (.var 1))) (by decide)
          (fun | 0 => f a | _ => polySum (xs.map f)))

private theorem negative_scale (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-c) p) (polyNeg (polySmul c p)) := by
  have ht : RatPolyTermwiseEqv (polySmul (-c) p) (polyNeg (polySmul c p)) := by
    induction p with
    | nil => exact True.intro
    | cons t p ih => exact ⟨rfl, Q'.neg_mul_eqv c t.2, ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

theorem evalRows_append (A B : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (A ++ B) r) (polyAdd (evalRows A r) (evalRows B r)) := by
  unfold evalRows
  rw [List.map_append]
  exact (RatPolyCoeffEqv.polySum_append _ _).symm

private theorem scaled_product (a b : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul a p) (polySmul b q))
      (polySmul (a*b) (polyMul p q)) :=
  (RatPolyCoeffEqv.polyMul_smul_left a p _).trans
    (((RatPolyCoeffEqv.polyMul_smul_right b p q).smul a).trans
      (RatPolyCoeffEqv.smul_assoc a b _))

private theorem eval_row_mul (a : Poly) (p : RatPoly) (B : Rows) (r : Q') :
    RatPolyCoeffEqv
      (evalRows (B.map fun b => (pmul a b.1, polyMul p b.2)) r)
      (polyMul (polySmul (QPoly.eval a r) p) (evalRows B r)) := by
  induction B with
  | nil => exact (RatPolyCoeffEqv.mul_zero_right _).symm
  | cons b B ih =>
      exact (((RatPolyCoeffEqv.smul_coefficient (eval_pmul a b.1 r) _).trans
        (scaled_product _ _ p b.2).symm).add ih).trans
          (RatPolyCoeffEqv.mul_add_right _ _ _).symm

theorem evalRows_mul (A B : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (mulRows A B) r) (polyMul (evalRows A r) (evalRows B r)) := by
  induction A with
  | nil => exact .refl _
  | cons a A ih =>
      change RatPolyCoeffEqv
        (evalRows ((B.map fun b => (pmul a.1 b.1, polyMul a.2 b.2)) ++ mulRows A B) r) _
      have hd : RatPolyCoeffEqv
          (polyAdd (polyMul (polySmul (QPoly.eval a.1 r) a.2) (evalRows B r))
            (polyMul (evalRows A r) (evalRows B r)))
          (polyMul (polyAdd (polySmul (QPoly.eval a.1 r) a.2) (evalRows A r)) (evalRows B r)) := by
        rw [polyMul_add_left_exact]
        exact .refl _
      exact (evalRows_append _ _ r).trans
        (((eval_row_mul a.1 a.2 B r).add ih).trans hd)

private def coefficientMap (f : Poly → Poly) (A : Rows) : Rows :=
  A.map fun a => (f a.1, a.2)

private def pairRows (c : Poly → Poly → Poly) (A B : Rows) : Rows :=
  A.flatMap fun a => B.map fun b => (c a.1 b.1, polyMul a.2 b.2)

private def pairs (A B : Rows) : List ((Poly × RatPoly) × (Poly × RatPoly)) :=
  A.flatMap fun a => B.map fun b => (a,b)

private theorem finite_product_rule (c : Poly → Poly → Poly) (f g : Poly → Poly)
    (A B : Rows) (r : Q')
    (h : ∀ a b, QPoly.eval (c a b) r ≈
      QPoly.eval (f a) r * QPoly.eval b r + QPoly.eval a r * QPoly.eval (g b) r) :
    RatPolyCoeffEqv (evalRows (pairRows c A B) r)
      (polyAdd
        (polyMul (evalRows (coefficientMap f A) r) (evalRows B r))
        (polyMul (evalRows A r) (evalRows (coefficientMap g B) r))) := by
  let F := fun ab : (Poly × RatPoly) × (Poly × RatPoly) =>
    polySmul (QPoly.eval (f ab.1.1) r * QPoly.eval ab.2.1 r) (polyMul ab.1.2 ab.2.2)
  let G := fun ab : (Poly × RatPoly) × (Poly × RatPoly) =>
    polySmul (QPoly.eval ab.1.1 r * QPoly.eval (g ab.2.1) r) (polyMul ab.1.2 ab.2.2)
  have hp : RatPolyCoeffEqv (evalRows (pairRows c A B) r)
      (polySum ((pairs A B).map fun ab => polyAdd (F ab) (G ab))) := by
    have hs := sum_congr
      (fun ab : (Poly × RatPoly) × (Poly × RatPoly) =>
        polySmul (QPoly.eval (c ab.1.1 ab.2.1) r) (polyMul ab.1.2 ab.2.2))
      (fun ab => polyAdd (F ab) (G ab)) (pairs A B) (fun ab _ =>
      (RatPolyCoeffEqv.smul_coefficient (h ab.1.1 ab.2.1) _).trans
        (RatPolyCoeffEqv.add_smul_same _ _ _).symm)
    simpa only [evalRows, pairRows, pairs, List.map_flatMap, List.map_map, Function.comp_def] using hs
  have hF : RatPolyCoeffEqv (polySum ((pairs A B).map F))
      (polyMul (evalRows (coefficientMap f A) r) (evalRows B r)) := by
    have hh := evalRows_mul (coefficientMap f A) B r
    have hs := sum_congr
      (fun ab : (Poly × RatPoly) × (Poly × RatPoly) =>
        polySmul (QPoly.eval (pmul (f ab.1.1) ab.2.1) r) (polyMul ab.1.2 ab.2.2))
      F (pairs A B) (fun ab _ =>
        RatPolyCoeffEqv.smul_coefficient (eval_pmul (f ab.1.1) ab.2.1 r) _)
    have ht : RatPolyCoeffEqv (evalRows (mulRows (coefficientMap f A) B) r)
        (polySum ((pairs A B).map F)) := by
      simpa only [evalRows, mulRows, coefficientMap, pairs, F, List.map_flatMap,
        List.flatMap_map, List.map_map, Function.comp_def] using hs
    exact ht.symm.trans hh
  have hG : RatPolyCoeffEqv (polySum ((pairs A B).map G))
      (polyMul (evalRows A r) (evalRows (coefficientMap g B) r)) := by
    have hh := evalRows_mul A (coefficientMap g B) r
    have hs := sum_congr
      (fun ab : (Poly × RatPoly) × (Poly × RatPoly) =>
        polySmul (QPoly.eval (pmul ab.1.1 (g ab.2.1)) r) (polyMul ab.1.2 ab.2.2))
      G (pairs A B) (fun ab _ =>
        RatPolyCoeffEqv.smul_coefficient (eval_pmul ab.1.1 (g ab.2.1) r) _)
    have ht : RatPolyCoeffEqv (evalRows (mulRows A (coefficientMap g B)) r)
        (polySum ((pairs A B).map G)) := by
      simpa only [evalRows, mulRows, coefficientMap, pairs, G, List.map_flatMap,
        List.flatMap_map, List.map_map, Function.comp_def] using hs
    exact ht.symm.trans hh
  exact hp.trans ((sum_add F G (pairs A B)).trans (hF.add hG))

theorem evalRows_derivative_mul (A B : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (derivativeRows (mulRows A B)) r)
      (polyAdd (polyMul (evalRows (derivativeRows A) r) (evalRows B r))
        (polyMul (evalRows A r) (evalRows (derivativeRows B) r))) := by
  have hh := finite_product_rule (fun a b => pderiv (pmul a b)) pderiv pderiv A B r
    (fun a b => Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_pmul a b) r)
      (Q'.eqv_trans _ _ _ (eval_padd _ _ r)
        (Q'.add_eqv_congr' (eval_pmul (pderiv a) b r) (eval_pmul a (pderiv b) r))))
  simpa only [derivativeRows, mulRows, pairRows, coefficientMap, List.map_flatMap,
    List.map_map, Function.comp_def] using hh

private def eulerCoefficient (E : Nat) (a : Poly) : Poly :=
  psub (pmul coordinate (pderiv a)) (pscale (Q'.ofNat E) a)

private theorem euler_coefficient_eval (E : Nat) (a : Poly) (r : Q') :
    QPoly.eval (eulerCoefficient E a) r ≈
      r * QPoly.eval (pderiv a) r + -(Q'.ofNat E * QPoly.eval a r) := by
  have hc : QPoly.eval coordinate r ≈ r := poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => r)
  exact Q'.eqv_trans _ _ _ (eval_psub _ _ r)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (eval_pmul coordinate (pderiv a) r)
        (Q'.mul_eqv_congr_right _ _ _ hc))
      (Q'.neg_eqv_congr _ _ (eval_pscale (Q'.ofNat E) a r)))

theorem evalRows_euler_pin (E : Nat) (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (eulerRows E A) r)
      (polyAdd (polySmul r (evalRows (derivativeRows A) r))
        (polyNeg (polySmul (Q'.ofNat E) (evalRows A r)))) := by
  have hp : RatPolyCoeffEqv (evalRows (eulerRows E A) r)
      (polySum (A.map fun a => polyAdd
        (polySmul r (polySmul (QPoly.eval (pderiv a.1) r) a.2))
        (polyNeg (polySmul (Q'.ofNat E) (polySmul (QPoly.eval a.1 r) a.2))))) := by
    simp only [evalRows, eulerRows, List.map_map, Function.comp_def]
    apply sum_congr
    intro a _
    exact (RatPolyCoeffEqv.smul_coefficient (euler_coefficient_eval E a.1 r) a.2).trans
      ((RatPolyCoeffEqv.add_smul_same _ _ _).symm.trans
        (((RatPolyCoeffEqv.smul_assoc r _ _).symm).add
          ((negative_scale _ _).trans
            (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.smul_assoc _ _ _).symm))))
  have hscale := sum_scale r (fun a : Poly × RatPoly => polySmul (QPoly.eval (pderiv a.1) r) a.2) A
  have hn := (sum_neg (fun a : Poly × RatPoly =>
      polySmul (Q'.ofNat E) (polySmul (QPoly.eval a.1 r) a.2)) A).trans
    (RatPolyCoeffEqv.neg
      (sum_scale (Q'.ofNat E) (fun a : Poly × RatPoly => polySmul (QPoly.eval a.1 r) a.2) A))
  have hs := hp.trans ((sum_add _ _ A).trans (hscale.add hn))
  simpa only [evalRows, derivativeRows, List.map_map, Function.comp_def] using hs

theorem evalRows_euler_mul (E : Nat) (A B : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (eulerRows E (mulRows A B)) r)
      (polyAdd (polyMul (evalRows (eulerRows E A) r) (evalRows B r))
        (polyMul (evalRows A r) (evalRows (eulerRows 0 B) r))) := by
  have he (a b : Poly) : QPoly.eval (eulerCoefficient E (pmul a b)) r ≈
      QPoly.eval (eulerCoefficient E a) r * QPoly.eval b r +
        QPoly.eval a r * QPoly.eval (eulerCoefficient 0 b) r := by
    have hd := Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_pmul a b) r)
      (Q'.eqv_trans _ _ _ (eval_padd _ _ r)
        (Q'.add_eqv_congr' (eval_pmul (pderiv a) b r) (eval_pmul a (pderiv b) r)))
    have hl := Q'.eqv_trans _ _ _ (euler_coefficient_eval E (pmul a b) r)
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left r _ _ hd)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_pmul a b r))))
    have hr : QPoly.eval (eulerCoefficient E a) r * QPoly.eval b r +
        QPoly.eval a r * QPoly.eval (eulerCoefficient 0 b) r ≈
        (r*QPoly.eval (pderiv a) r + -(Q'.ofNat E*QPoly.eval a r))*QPoly.eval b r +
        QPoly.eval a r*(r*QPoly.eval (pderiv b) r + -(Q'.ofNat 0*QPoly.eval b r)) :=
      Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ (QPoly.eval b r) (euler_coefficient_eval E a r))
        (Q'.mul_eqv_congr_left (QPoly.eval a r) _ _ (euler_coefficient_eval 0 b r))
    exact Q'.eqv_trans _ _ _ hl (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 3) (.var 2))))
          (.neg (.mul (.var 5) (.mul (.var 3) (.var 4)))))
        (.add (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 5) (.var 3)))) (.var 4))
          (.mul (.var 3) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.const 0) (.var 4))))))
        (by decide) (fun
          | 0 => r
          | 1 => QPoly.eval (pderiv a) r
          | 2 => QPoly.eval (pderiv b) r
          | 3 => QPoly.eval a r
          | 4 => QPoly.eval b r
          | _ => Q'.ofNat E)) (Q'.eqv_symm hr))
  have hh := finite_product_rule (fun a b => eulerCoefficient E (pmul a b))
    (eulerCoefficient E) (eulerCoefficient 0) A B r he
  simpa only [eulerRows, eulerCoefficient, mulRows, pairRows, coefficientMap,
    List.map_flatMap, List.map_map, Function.comp_def] using hh

theorem evalRows_angularDerivative (i j : Nat) (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (mapRows (angularDerivative i j) A) r)
      (angularDerivative i j (evalRows A r)) := by
  induction A with
  | nil => exact .refl _
  | cons a A ih =>
      exact (((angularDerivative_smul i j _ _).symm).add ih).trans
        (angularDerivative_add i j _ _).symm

theorem evalRows_partialHaarHead (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (mapRows partialHaarHead A) r)
      (partialHaarHead (evalRows A r)) := by
  induction A with
  | nil => exact .refl _
  | cons a A ih =>
      rw [show evalRows ((a::A)) r = polyAdd (polySmul (QPoly.eval a.1 r) a.2) (evalRows A r) from rfl,
        partialHaarHead_add]
      exact ((partialHaarHead_smul _ _).symm).add ih

theorem evalRows_derivative_mapAngular (i j : Nat) (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (derivativeRows (mapRows (angularDerivative i j) A)) r)
      (angularDerivative i j (evalRows (derivativeRows A) r)) := by
  simpa only [derivativeRows, mapRows, List.map_map, Function.comp_def] using
    evalRows_angularDerivative i j (derivativeRows A) r

theorem evalRows_euler_partialHaarHead (E : Nat) (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (eulerRows E (mapRows partialHaarHead A)) r)
      (partialHaarHead (evalRows (eulerRows E A) r)) := by
  simpa only [eulerRows, mapRows, List.map_map, Function.comp_def] using
    evalRows_partialHaarHead (eulerRows E A) r

end YMGap.Continuum.RatPolyNomeRows

#print axioms YMGap.Continuum.RatPolyNomeRows.Rows
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows
#print axioms YMGap.Continuum.RatPolyNomeRows.derivativeRows
#print axioms YMGap.Continuum.RatPolyNomeRows.mulRows
#print axioms YMGap.Continuum.RatPolyNomeRows.mapRows
#print axioms YMGap.Continuum.RatPolyNomeRows.eulerRows
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_append
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_mul
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_derivative_mul
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_euler_pin
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_euler_mul
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_angularDerivative
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_partialHaarHead
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_derivative_mapAngular
#print axioms YMGap.Continuum.RatPolyNomeRows.evalRows_euler_partialHaarHead
