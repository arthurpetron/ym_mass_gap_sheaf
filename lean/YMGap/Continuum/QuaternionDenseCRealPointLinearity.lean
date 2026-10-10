/-
The actual choice-free Point extension preserves addition and signed rational
scaling of admissible dense data.  The inner sampling rates of the three
presentations need not agree: their values are compared at one later stage.
No Haar law, continuous integral, or identity of sampled polynomials is an
input to these Point-level identities.
-/

import YMGap.Continuum.QuaternionDenseCRealHaarAdditivity
import YMGap.Continuum.QuaternionDenseCRealHaarHomogeneity
import YMGap.Continuum.QuaternionDenseCRealPointExtension
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.QuaternionDenseCRealPointLinearity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.Continuum.QuaternionDenseCRealHaarAdditivity
open YMGap.Continuum.QuaternionDenseCRealHaarHomogeneity
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup

local infix:50 " ≈ " => Q'.eqv

private theorem sample_add_error (u v : CReal)
    (Ru : InnerRegularity u) (Rv : InnerRegularity v)
    (tau : Q') (ht : (0 : Q') < tau) :
    Q'.abs (sample (CReal.add u v) (InnerRegularity.add Ru Rv) tau +
      -(sample u Ru tau + sample v Rv tau)) ≤ tau + (tau + tau) := by
  let j := max ((InnerRegularity.add Ru Rv).rate tau)
    (max (Ru.rate tau) (Rv.rate tau))
  have ha := sample_error_bound (CReal.add u v) (InnerRegularity.add Ru Rv)
    tau ht j (Nat.le_max_left _ _)
  have hu0 := sample_error_bound u Ru tau ht j
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hv0 := sample_error_bound v Rv tau ht j
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have hu : Q'.abs (u.approx j + -(sample u Ru tau)) ≤ tau :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hu0
  have hv : Q'.abs (v.approx j + -(sample v Rv tau)) ≤ tau :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hv0
  have ha' : Q'.abs (sample (CReal.add u v) (InnerRegularity.add Ru Rv) tau +
      -(u.approx j + v.approx j)) ≤ tau := ha
  have hpin : sample (CReal.add u v) (InnerRegularity.add Ru Rv) tau +
      -(sample u Ru tau + sample v Rv tau) ≈
      (sample (CReal.add u v) (InnerRegularity.add Ru Rv) tau +
        -(u.approx j + v.approx j)) +
        ((u.approx j + -(sample u Ru tau)) +
          (v.approx j + -(sample v Rv tau))) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.var 2))))
      (.add (.add (.var 0) (.neg (.add (.var 3) (.var 4))))
        (.add (.add (.var 3) (.neg (.var 1)))
          (.add (.var 4) (.neg (.var 2)))))
      (by decide)
      (fun | 0 => sample (CReal.add u v) (InnerRegularity.add Ru Rv) tau
           | 1 => sample u Ru tau | 2 => sample v Rv tau
           | 3 => u.approx j | _ => v.approx j)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add ha'
        (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) (Q'.add_le_add hu hv))))

/-- Computed cutoff for the three sample errors in the row-sum identity. -/
def sumRowEqualityRate (epsilon : Q') : Nat :=
  (HalfPow.half * (HalfPow.half * epsilon)).den

private theorem sum_tail_budget (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : sumRowEqualityRate epsilon ≤ n) :
    Q'.invSucc n + (Q'.invSucc n + Q'.invSucc n) ≤ epsilon := by
  let t := HalfPow.half * (HalfPow.half * epsilon)
  have ht : (0 : Q') < t :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)
  have hs : Q'.invSucc n ≤ t :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le t ht)
  have hpin : (t + (t + t)) + t ≈ (t + t) + (t + t) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 0) (.var 0))) (.var 0))
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (by decide) (fun _ => t)
  have hfour : (t + (t + t)) + t ≈ epsilon :=
    Q'.eqv_trans _ _ _ hpin
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon))
          (ExpNeg.two_halves (HalfPow.half * epsilon)))
        (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add hs (Q'.add_le_add hs hs))
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt ht))
      (Q'.le_of_eqv hfour))

section Sum

variable (F G : UnitNorm → CReal)
variable (RF : ∀ q, InnerRegularity (F q))
variable (RG : ∀ q, InnerRegularity (G q))
variable (rhoF rhoG : Q' → Q')
variable (positiveF : ∀ e, (0 : Q') < e → (0 : Q') < rhoF e)
variable (positiveG : ∀ e, (0 : Q') < e → (0 : Q') < rhoG e)
variable (modF : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rhoF e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
variable (modG : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rhoG e →
    leRat (CReal.abs (CReal.add (G q) (CReal.neg (G x)))) e)

/-- The actual sampled image of the dense sum equals the sum of the TWO
actual sampled images, for every supplied point row. -/
theorem rowImage_sum (X : CauchyPoint) :
    Equiv
      (rowImage (sumInput F G) (sumInner F RF G RG)
        (sumRadius rhoF rhoG)
        (sumRadius_positive rhoF rhoG positiveF positiveG)
        (sum_modulus F G rhoF rhoG modF modG) X)
      (CReal.add (rowImage F RF rhoF positiveF modF X)
        (rowImage G RG rhoG positiveG modG X)) := by
  intro epsilon he
  refine ⟨sumRowEqualityRate epsilon, fun n hn => ?_⟩
  have hb := sample_add_error (F (X.seq n)) (G (X.seq n))
    (RF (X.seq n)) (RG (X.seq n)) (Q'.invSucc n) (Q'.invSucc_pos n)
  have hs : Q'.abs
      ((rowImage (sumInput F G) (sumInner F RF G RG)
          (sumRadius rhoF rhoG)
          (sumRadius_positive rhoF rhoG positiveF positiveG)
          (sum_modulus F G rhoF rhoG modF modG) X).approx n +
        -((CReal.add (rowImage F RF rhoF positiveF modF X)
          (rowImage G RG rhoG positiveG modG X)).approx n)) ≤ epsilon := by
    change Q'.abs (sample (CReal.add (F (X.seq n)) (G (X.seq n)))
      (InnerRegularity.add (RF (X.seq n)) (RG (X.seq n))) (Q'.invSucc n) +
      -(sample (F (X.seq n)) (RF (X.seq n)) (Q'.invSucc n) +
        sample (G (X.seq n)) (RG (X.seq n)) (Q'.invSucc n))) ≤ epsilon
    exact Q'.le_trans' _ _ _ hb (sum_tail_budget epsilon he n hn)
  exact ⟨ExpNeg.le_add_of_abs_sub_le hs,
    ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hs)⟩

/-- Addition of the two independently presented dense functions agrees with
addition of their ACTUAL extensions at every completed Point. -/
theorem pointExtension_sum (x : Point) :
    pointExtension (sumInput F G) (sumInner F RF G RG)
      (sumRadius rhoF rhoG)
      (sumRadius_positive rhoF rhoG positiveF positiveG)
      (sum_modulus F G rhoF rhoG modF modG) x =
    RCadd (pointExtension F RF rhoF positiveF modF x)
      (pointExtension G RG rhoG positiveG modG x) := by
  refine Quotient.inductionOn x (fun X => ?_)
  rw [pointExtension_mk, pointExtension_mk, pointExtension_mk, RCadd_mk]
  exact Quotient.sound
    (rowImage_sum F G RF RG rhoF rhoG positiveF positiveG modF modG X)

end Sum

private theorem sample_scale_error (c : Q') (u : CReal)
    (Ru : InnerRegularity u) (tau : Q') (ht : (0 : Q') < tau) :
    Q'.abs (sample (CReal.mul (CReal.ofQ' c) u)
      (InnerRegularity.scaleLeftSigned Ru c) tau +
      -(c * sample u Ru tau)) ≤ tau + Q'.abs c * tau := by
  let S := InnerRegularity.scaleLeftSigned Ru c
  let j := max (S.rate tau) (Ru.rate tau)
  have ha := sample_error_bound (CReal.mul (CReal.ofQ' c) u) S
    tau ht j (Nat.le_max_left _ _)
  have hu0 := sample_error_bound u Ru tau ht j (Nat.le_max_right _ _)
  have hu : Q'.abs (u.approx j + -(sample u Ru tau)) ≤ tau :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hu0
  have ha' : Q'.abs (sample (CReal.mul (CReal.ofQ' c) u) S tau +
      -(c * u.approx j)) ≤ tau := ha
  have hpin : sample (CReal.mul (CReal.ofQ' c) u) S tau +
      -(c * sample u Ru tau) ≈
      (sample (CReal.mul (CReal.ofQ' c) u) S tau +
        -(c * u.approx j)) +
        c * (u.approx j + -(sample u Ru tau)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
      (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.add (.var 3) (.neg (.var 2)))))
      (by decide)
      (fun | 0 => sample (CReal.mul (CReal.ofQ' c) u) S tau
           | 1 => c | 2 => sample u Ru tau | _ => u.approx j)
  have hm : Q'.abs (c * (u.approx j + -(sample u Ru tau))) ≤
      Q'.abs c * tau :=
    Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le c (u.approx j + -(sample u Ru tau)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hu (Q'.abs_nonneg c))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add ha' hm))

/-- Computed signed-scalar row cutoff, including c=0. -/
def scaleRowEqualityRate (c epsilon : Q') : Nat :=
  (InnerRegularity.scaleTolerance (1 + Q'.abs c) epsilon).den

private theorem scale_tail_budget (c epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : scaleRowEqualityRate c epsilon ≤ n) :
    Q'.invSucc n + Q'.abs c * Q'.invSucc n ≤ epsilon := by
  let C := (1 : Q') + Q'.abs c
  let theta := InnerRegularity.scaleTolerance C epsilon
  have hC : (0 : Q') ≤ C :=
    Q'.zero_le_add _ _ Q'.zero_le_one (Q'.abs_nonneg c)
  have ht : (0 : Q') < theta :=
    InnerRegularity.scaleTolerance_pos C epsilon he
  have hs : Q'.invSucc n ≤ theta :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le theta ht)
  have hring : Q'.invSucc n + Q'.abs c * Q'.invSucc n ≈
      C * Q'.invSucc n :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.var 1) (.var 0)))
      (.mul (.add (.const 1) (.var 1)) (.var 0))
      (by decide) (fun | 0 => Q'.invSucc n | _ => Q'.abs c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hring)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ C hs hC)
      (InnerRegularity.mul_scaleTolerance_le C epsilon hC he))

section Scale

variable (c : Q') (F : UnitNorm → CReal)
variable (RF : ∀ q, InnerRegularity (F q))
variable (rho : Q' → Q')
variable (positive : ∀ e, (0 : Q') < e → (0 : Q') < rho e)
variable (modF : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rho e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

/-- Signed rational scaling commutes with the ACTUAL row image. -/
theorem rowImage_scale (X : CauchyPoint) :
    Equiv
      (rowImage (scaleInput c F) (scaleInner c F RF)
        (scaleRadius c rho) (scaleRadius_positive c rho positive)
        (scale_modulus c F rho modF) X)
      (CReal.mul (CReal.ofQ' c) (rowImage F RF rho positive modF X)) := by
  intro epsilon he
  refine ⟨scaleRowEqualityRate c epsilon, fun n hn => ?_⟩
  have hb := sample_scale_error c (F (X.seq n)) (RF (X.seq n))
    (Q'.invSucc n) (Q'.invSucc_pos n)
  have hs : Q'.abs
      ((rowImage (scaleInput c F) (scaleInner c F RF)
          (scaleRadius c rho) (scaleRadius_positive c rho positive)
          (scale_modulus c F rho modF) X).approx n +
        -((CReal.mul (CReal.ofQ' c)
          (rowImage F RF rho positive modF X)).approx n)) ≤ epsilon := by
    change Q'.abs
      (sample (CReal.mul (CReal.ofQ' c) (F (X.seq n)))
        (InnerRegularity.scaleLeftSigned (RF (X.seq n)) c) (Q'.invSucc n) +
        -(c * sample (F (X.seq n)) (RF (X.seq n)) (Q'.invSucc n))) ≤ epsilon
    exact Q'.le_trans' _ _ _ hb (scale_tail_budget c epsilon he n hn)
  exact ⟨ExpNeg.le_add_of_abs_sub_le hs,
    ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hs)⟩

/-- Signed rational scaling of dense data agrees with scaling its ACTUAL
extension at every completed Point, including c=0 and c<0. -/
theorem pointExtension_scale (x : Point) :
    pointExtension (scaleInput c F) (scaleInner c F RF)
      (scaleRadius c rho) (scaleRadius_positive c rho positive)
      (scale_modulus c F rho modF) x =
    RCscale c (pointExtension F RF rho positive modF x) := by
  refine Quotient.inductionOn x (fun X => ?_)
  rw [pointExtension_mk, pointExtension_mk, RCscale_mk]
  exact Quotient.sound (rowImage_scale c F RF rho positive modF X)

end Scale

#print axioms sumRowEqualityRate
#print axioms rowImage_sum
#print axioms pointExtension_sum
#print axioms scaleRowEqualityRate
#print axioms rowImage_scale
#print axioms pointExtension_scale

end YMGap.Continuum.QuaternionDenseCRealPointLinearity
