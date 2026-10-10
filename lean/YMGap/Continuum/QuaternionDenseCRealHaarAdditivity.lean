/-
Actual addition of admissible dense CReal data, with produced inner rates,
sound bounds and continuity radii. The independent Bernstein constructions
are not identified definitionally. Original polynomial moments supply
the additive law after all three approximation errors have been paid.
This is not yet positive, normalized, invariant continuous Haar or J04.
-/

import YMGap.Constructive.CubeRoot
import YMGap.Continuum.QuaternionDenseCRealHaarApproximation

namespace YMGap.Continuum.QuaternionDenseCRealHaarAdditivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets

local infix:50 " ≈ " => Q'.eqv

/-- Sound distances add under the ACTUAL pointwise addition. -/
theorem sum_distance {a b c d : CReal} {eta theta : Q'}
    (h1 : leRat (CReal.abs (CReal.add a (CReal.neg c))) eta)
    (h2 : leRat (CReal.abs (CReal.add b (CReal.neg d))) theta) :
    leRat (CReal.abs (CReal.add (CReal.add a b)
      (CReal.neg (CReal.add c d)))) (eta + theta) := by
  have hs := leRat_add h1 h2
  intro e he
  obtain ⟨K, hK⟩ := hs e he
  refine ⟨K, fun n hn => ?_⟩
  have hpin : (a.approx n + b.approx n) + -(c.approx n + d.approx n) ≈
      (a.approx n + -(c.approx n)) + (b.approx n + -(d.approx n)) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide)
      (fun | 0 => a.approx n | 1 => b.approx n | 2 => c.approx n | _ => d.approx n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (hK n hn))

/-- The sum is an actual function, not an additional analytic input. -/
def sumInput (F G : UnitNorm → CReal) (q : UnitNorm) : CReal :=
  CReal.add (F q) (G q)

/-- Recoverable inner rates are the existing maximum of two half-error rates. -/
def sumInner (F : UnitNorm → CReal) (RF : ∀ q, InnerRegularity (F q))
    (G : UnitNorm → CReal) (RG : ∀ q, InnerRegularity (G q)) :
    ∀ q, InnerRegularity (sumInput F G q) :=
  fun q => InnerRegularity.add (RF q) (RG q)

/-- Computable radius; no monotonicity of either supplied radius is assumed. -/
def sumRadius (rhoF rhoG : Q' → Q') (e : Q') : Q' :=
  Q'.min' (rhoF (HalfPow.half*e)) (rhoG (HalfPow.half*e))

theorem sumRadius_positive (rhoF rhoG : Q' → Q')
    (positiveF : ∀ e, (0 : Q') < e → (0 : Q') < rhoF e)
    (positiveG : ∀ e, (0 : Q') < e → (0 : Q') < rhoG e)
    (e : Q') (he : (0 : Q') < e) : (0 : Q') < sumRadius rhoF rhoG e :=
  CReal.min_pos (positiveF _ (ExpNeg.half_mul_pos _ he))
    (positiveG _ (ExpNeg.half_mul_pos _ he))

/-- The supplied SOUND bounds produce the sum bound; early rows need not obey it. -/
theorem sum_bound (F G : UnitNorm → CReal) (MF MG : Q')
    (boundF : ∀ q, leRat (CReal.abs (F q)) MF)
    (boundG : ∀ q, leRat (CReal.abs (G q)) MG) (q : UnitNorm) :
    leRat (CReal.abs (sumInput F G q)) (MF+MG) := by
  have hs := leRat_add (boundF q) (boundG q)
  intro e he
  obtain ⟨K, hK⟩ := hs e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (hK n hn)

/-- The computed radius produces the exact requested sound continuity error. -/
theorem sum_modulus (F G : UnitNorm → CReal) (rhoF rhoG : Q' → Q')
    (modF : ∀ e, (0 : Q') < e → ∀ q x,
      distSq q.val x.val ≤ rhoF e →
        leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
    (modG : ∀ e, (0 : Q') < e → ∀ q x,
      distSq q.val x.val ≤ rhoG e →
        leRat (CReal.abs (CReal.add (G q) (CReal.neg (G x)))) e)
    (e : Q') (he : (0 : Q') < e) (q x : UnitNorm)
    (hd : distSq q.val x.val ≤ sumRadius rhoF rhoG e) :
    leRat (CReal.abs (CReal.add (sumInput F G q)
      (CReal.neg (sumInput F G x)))) e := by
  have hf : distSq q.val x.val ≤ rhoF (HalfPow.half*e) :=
    Q'.le_trans' _ _ _ hd Q'.min_le_left
  have hg : distSq q.val x.val ≤ rhoG (HalfPow.half*e) :=
    Q'.le_trans' _ _ _ hd Q'.min_le_right
  exact leRat_mono
    (sum_distance (modF _ (ExpNeg.half_mul_pos _ he) q x hf)
      (modG _ (ExpNeg.half_mul_pos _ he) q x hg))
    (Q'.le_of_eqv (ExpNeg.two_halves e))

private theorem distance_symm {a b : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta) :
    leRat (CReal.abs (CReal.add b (CReal.neg a))) eta := by
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hK n hn)

variable (F : UnitNorm → CReal) (RF : ∀ q, InnerRegularity (F q))
variable (MF : Q') (rhoF : Q' → Q')
variable (positiveF : ∀ e, (0 : Q') < e → (0 : Q') < rhoF e)
variable (boundF : ∀ q, leRat (CReal.abs (F q)) MF)
variable (modF : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rhoF e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
variable (G : UnitNorm → CReal) (RG : ∀ q, InnerRegularity (G q))
variable (MG : Q') (rhoG : Q' → Q')
variable (positiveG : ∀ e, (0 : Q') < e → (0 : Q') < rhoG e)
variable (boundG : ∀ q, leRat (CReal.abs (G q)) MG)
variable (modG : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rhoG e →
    leRat (CReal.abs (CReal.add (G q) (CReal.neg (G x)))) e)
variable (H : UnitNorm → CReal) (RH : ∀ q, InnerRegularity (H q))
variable (MH : Q') (rhoH : Q' → Q')
variable (positiveH : ∀ e, (0 : Q') < e → (0 : Q') < rhoH e)
variable (boundH : ∀ q, leRat (CReal.abs (H q)) MH)
variable (modH : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rhoH e →
    leRat (CReal.abs (CReal.add (H q) (CReal.neg (H x)))) e)

include positiveF boundF modF positiveG boundG modG positiveH boundH modH in
/-- Compare H's ACTUAL stage to the sum of F's and G's ACTUAL stages.
Only the dense input addition is identified; no integral identity is supplied. -/
theorem haarAdditivity_stage (hadd : ∀ q, H q = sumInput F G q) (n : Nat) :
    Q'.abs (haarApproximationValue H RH MH rhoH n +
      -(haarApproximationValue F RF MF rhoF n +
        haarApproximationValue G RG MG rhoG n)) ≤
      Q'.invSucc n + (Q'.invSucc n + Q'.invSucc n) := by
  let tau := Q'.invSucc n
  let pf := haarApproximationPolynomial F RF MF rhoF n
  let pg := haarApproximationPolynomial G RG MG rhoG n
  let p := polyAdd pf pg
  have hclose (q : UnitNorm) :
      leRat (CReal.abs (CReal.add (H q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p)))))
        (tau+tau) := by
    have hf := distance_symm
      (realApproximation_error F RF MF rhoF positiveF boundF modF
        tau (Q'.invSucc_pos n) _ (Nat.le_refl _) q)
    have hg := distance_symm
      (realApproximation_error G RG MG rhoG positiveG boundG modG
        tau (Q'.invSucc_pos n) _ (Nat.le_refl _) q)
    have hs := sum_distance hf hg
    intro e he
    obtain ⟨K, hK⟩ := hs e he
    refine ⟨K, fun j hj => ?_⟩
    rw [hadd q]
    have hpin : (F q).approx j + (G q).approx j +
        -(evalRatPoly (environmentOf q.val) p) ≈
        (F q).approx j + (G q).approx j +
          -(evalRatPoly (environmentOf q.val) pf +
            evalRatPoly (environmentOf q.val) pg) :=
      Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (evalRatPoly_add _ pf pg))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin)) (hK j hj)
  have hb := haarApproximation_polynomial_distance H RH MH rhoH
    positiveH boundH modH p
    (supported_add (realApproximation_supported F RF tau _)
      (realApproximation_supported G RG tau _)) (tau+tau) hclose n
  have hpin : haarApproximationValue H RH MH rhoH n + -(quaternionHaar 1 p) ≈
      haarApproximationValue H RH MH rhoH n +
        -(haarApproximationValue F RF MF rhoF n +
          haarApproximationValue G RG MG rhoG n) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (quaternionHaar_append 1 pf pg))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Q'.eqv_symm hpin))) hb

private theorem three_tail_budget (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : (HalfPow.half*(HalfPow.half*e)).den ≤ n) :
    Q'.invSucc n + (Q'.invSucc n + Q'.invSucc n) ≤ e := by
  let t := HalfPow.half*(HalfPow.half*e)
  have ht : (0 : Q') < t := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)
  have hs : Q'.invSucc n ≤ t :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le t ht)
  have hpin : (t+(t+t))+t ≈ (t+t)+(t+t) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 0) (.var 0))) (.var 0))
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (by decide) (fun _ => t)
  have hfour : (t+(t+t))+t ≈ e :=
    Q'.eqv_trans _ _ _ hpin
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*e))
          (ExpNeg.two_halves (HalfPow.half*e))) (ExpNeg.two_halves e))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add hs (Q'.add_le_add hs hs))
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt ht))
      (Q'.le_of_eqv hfour))

/-- Original-Haar additivity for actual admissible data, with ordinary dense
sum identity as input. All three approximation tails vanish at an explicit cutoff. -/
theorem haarAdditivity (hadd : ∀ q, H q = sumInput F G q) :
    Equiv (haarApproximationReal H RH MH rhoH positiveH boundH modH)
      (CReal.add (haarApproximationReal F RF MF rhoF positiveF boundF modF)
        (haarApproximationReal G RG MG rhoG positiveG boundG modG)) := by
  intro e he
  refine ⟨(HalfPow.half*(HalfPow.half*e)).den, fun n hn => ?_⟩
  have hb := Q'.le_trans' _ _ _
    (haarAdditivity_stage F RF MF rhoF positiveF boundF modF
      G RG MG rhoG positiveG boundG modG H RH MH rhoH positiveH boundH modH hadd n)
    (three_tail_budget e he n hn)
  exact ⟨ExpNeg.le_add_of_abs_sub_le hb,
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hb)⟩

/-- Apply ORIGINAL Haar to the ACTUAL sum with the produced admissibility data. -/
def sumHaar : CReal :=
  haarApproximationReal (sumInput F G) (sumInner F RF G RG) (MF+MG)
    (sumRadius rhoF rhoG) (sumRadius_positive rhoF rhoG positiveF positiveG)
    (sum_bound F G MF MG boundF boundG) (sum_modulus F G rhoF rhoG modF modG)

/-- The actual sum candidate retains the recoverable Haar rate den(epsilon/2). -/
def sumHaarInnerRegularity :
    InnerRegularity
      (sumHaar F RF MF rhoF positiveF boundF modF G RG MG rhoG positiveG boundG modG) :=
  haarApproximationInnerRegularity (sumInput F G) (sumInner F RF G RG) (MF+MG)
    (sumRadius rhoF rhoG) (sumRadius_positive rhoF rhoG positiveF positiveG)
    (sum_bound F G MF MG boundF boundG) (sum_modulus F G rhoF rhoG modF modG)

/-- Actual sum-input instance: no sum admissibility or integral answer is assumed. -/
theorem sumHaar_additive :
    Equiv (sumHaar F RF MF rhoF positiveF boundF modF G RG MG rhoG positiveG boundG modG)
      (CReal.add (haarApproximationReal F RF MF rhoF positiveF boundF modF)
        (haarApproximationReal G RG MG rhoG positiveG boundG modG)) := by
  exact haarAdditivity F RF MF rhoF positiveF boundF modF
    G RG MG rhoG positiveG boundG modG
    (sumInput F G) (sumInner F RF G RG) (MF+MG) (sumRadius rhoF rhoG)
    (sumRadius_positive rhoF rhoG positiveF positiveG) (sum_bound F G MF MG boundF boundG)
    (sum_modulus F G rhoF rhoG modF modG) (fun _ => rfl)

#print axioms sum_distance
#print axioms sumInput
#print axioms sumInner
#print axioms sumRadius
#print axioms sumRadius_positive
#print axioms sum_bound
#print axioms sum_modulus
#print axioms haarAdditivity_stage
#print axioms haarAdditivity
#print axioms sumHaar
#print axioms sumHaarInnerRegularity
#print axioms sumHaar_additive

end YMGap.Continuum.QuaternionDenseCRealHaarAdditivity
