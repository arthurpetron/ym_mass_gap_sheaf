/-
The original-Haar candidate depends on the supplied dense VALUES, not on
their bounding, regularity or continuity-radius presentation. Two separate
computed polynomial constructions are compared through the existing original
polynomial Haar bound. Sound dense distance eta survives in the limit with
an explicit error cutoff. No integral identity or supremum is assumed.
This is not yet a positive, linear, invariant continuous Haar package or J04.
-/

import YMGap.Continuum.QuaternionDenseCRealHaarApproximation
import YMGap.Continuum.QuaternionDenseCRealPointExtension

namespace YMGap.Continuum.QuaternionDenseCRealHaarComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

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

include positiveF boundF modF positiveG boundG modG in
/-- Separate ACTUAL Haar stages retain both polynomial errors and the dense
input distance. No relation between the two computed rates/radii is needed. -/
theorem haarComparison_stage (eta : Q')
    (hD : ∀ q, leRat (CReal.abs (CReal.add (F q) (CReal.neg (G q)))) eta)
    (m n : Nat) :
    Q'.abs (haarApproximationValue F RF MF rhoF m +
      -(haarApproximationValue G RG MG rhoG n)) ≤
        Q'.invSucc m + (eta + Q'.invSucc n) := by
  let pn := haarApproximationPolynomial G RG MG rhoG n
  let tau := Q'.invSucc n
  have hclose (q : UnitNorm) :
      leRat (CReal.abs (CReal.add (F q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) pn)))))
        (eta + tau) := by
    intro e he
    obtain ⟨K, hK⟩ := hD q e he
    refine ⟨max K (realApproximationOutputRate G RG tau q), fun j hj => ?_⟩
    have hfg : Q'.abs ((F q).approx j + -((G q).approx j)) ≤ eta + e :=
      hK j (Nat.le_trans (Nat.le_max_left _ _) hj)
    have hgp : Q'.abs ((G q).approx j +
        -(evalRatPoly (environmentOf q.val) pn)) ≤ tau :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _))
        (realApproximation_error_at_index G RG MG rhoG positiveG boundG modG
          tau (Q'.invSucc_pos n) _ (Nat.le_refl _) q j
          (Nat.le_trans (Nat.le_max_right _ _) hj))
    have hpin : (F q).approx j + -(evalRatPoly (environmentOf q.val) pn) ≈
        ((F q).approx j + -((G q).approx j)) +
          ((G q).approx j + -(evalRatPoly (environmentOf q.val) pn)) :=
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.var 1)))
        (.add (.add (.var 0) (.neg (.var 2)))
          (.add (.var 2) (.neg (.var 1))))
        (by decide)
        (fun | 0 => (F q).approx j
             | 1 => evalRatPoly (environmentOf q.val) pn
             | _ => (G q).approx j)
    have hswap : (eta + e) + tau ≈ (eta + tau) + e :=
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.var 2))
        (.add (.add (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => eta | 1 => e | _ => tau)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.le_trans' _ _ _ (Q'.add_le_add hfg hgp) (Q'.le_of_eqv hswap)))
  exact haarApproximation_polynomial_distance F RF MF rhoF positiveF boundF modF
    pn (realApproximation_supported G RG tau _) (eta + tau) hclose m

private theorem comparison_budget (eta e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : (HalfPow.half*e).den ≤ n) :
    Q'.invSucc n + (eta + Q'.invSucc n) ≤ eta + e := by
  let h := HalfPow.half*e
  have hs : Q'.invSucc n ≤ h :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le h (Q'.mul_pos (by decide) he))
  have hpin : h + (eta + h) ≈ eta + (h+h) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.var 1) (.var 0)))
      (.add (.var 1) (.add (.var 0) (.var 0)))
      (by decide) (fun | 0 => h | _ => eta)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add hs (Q'.add_le_add_left _ _ _ hs))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hpin
      (Q'.add_eqv_congr_left eta _ _ (ExpNeg.two_halves e))))

/-- The actual original-Haar CReal candidates inherit the dense input distance
eta. The explicit cutoff removes both stage errors, not the supplied eta. -/
theorem haarComparison_distance (eta : Q')
    (hD : ∀ q, leRat (CReal.abs (CReal.add (F q) (CReal.neg (G q)))) eta) :
    leRat (CReal.abs (CReal.add
      (haarApproximationReal F RF MF rhoF positiveF boundF modF)
      (CReal.neg (haarApproximationReal G RG MG rhoG positiveG boundG modG)))) eta := by
  intro e he
  refine ⟨(HalfPow.half*e).den, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (haarComparison_stage F RF MF rhoF positiveF boundF modF
      G RG MG rhoG positiveG boundG modG eta hD n n)
    (comparison_budget eta e he n hn)

/-- Two-sided contractivity in the GENUINE real-quotient order. The output
classes are the actual constructed original-Haar values, not chosen reals. -/
theorem haarComparison_order (eta : Q')
    (hD : ∀ q, leRat (CReal.abs (CReal.add (F q) (CReal.neg (G q)))) eta) :
    RCle (Quotient.mk crealSetoid
      (haarApproximationReal F RF MF rhoF positiveF boundF modF))
      (RCadd (Quotient.mk crealSetoid
        (haarApproximationReal G RG MG rhoG positiveG boundG modG))
        (Quotient.mk crealSetoid (CReal.ofQ' eta))) ∧
    RCle (Quotient.mk crealSetoid
      (haarApproximationReal G RG MG rhoG positiveG boundG modG))
      (RCadd (Quotient.mk crealSetoid
        (haarApproximationReal F RF MF rhoF positiveF boundF modF))
        (Quotient.mk crealSetoid (CReal.ofQ' eta))) := by
  have h := haarComparison_distance F RF MF rhoF positiveF boundF modF
    G RG MG rhoG positiveG boundG modG eta hD
  have forward (u v : CReal)
      (hu : leRat (CReal.abs (CReal.add u (CReal.neg v))) eta) :
      leEv u (CReal.add v (CReal.ofQ' eta)) := by
    intro e he
    obtain ⟨K, hK⟩ := hu e he
    refine ⟨K, fun n hn => ?_⟩
    exact Q'.le_trans' _ _ _ (ExpNeg.le_add_of_abs_sub_le (hK n hn))
      (Q'.ge_of_eqv (Q'.add_assoc_eqv (v.approx n) eta e))
  refine ⟨forward _ _ h, forward _ _ ?_⟩
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hK n hn)

/-- Equal dense input VALUES give the same actual Haar value despite distinct
inner rates, bounds and continuity radii. No proposed integral is an input. -/
theorem haarComparison_equiv
    (hD : ∀ q, leRat (CReal.abs (CReal.add (F q) (CReal.neg (G q)))) 0) :
    Equiv (haarApproximationReal F RF MF rhoF positiveF boundF modF)
      (haarApproximationReal G RG MG rhoG positiveG boundG modG) := by
  apply Equiv_of_abs_sub_le_all_pos
  intro e he
  exact leRat_mono (haarComparison_distance F RF MF rhoF positiveF boundF modF
    G RG MG rhoG positiveG boundG modG 0 hD) (Q'.le_of_lt he)

/-- Literal self-distance vanishes at every approximation, without assuming
an analytic zero-distance certificate. -/
theorem self_input_distance_zero (x : CReal) :
    leRat (CReal.abs (CReal.add x (CReal.neg x))) 0 := by
  apply leRat_of_eventually
  refine ⟨0, fun n _ => ?_⟩
  have hzero : x.approx n + -(x.approx n) ≈ (0 : Q') :=
    Q'.add_neg_self_eqv _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hzero))
    (by decide : Q'.abs (0 : Q') ≤ 0)

private theorem distance_zero_of_equiv {x y : CReal} (h : Equiv x y) :
    leRat (CReal.abs (CReal.add x (CReal.neg y))) 0 := by
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hK n hn
  exact Q'.le_trans' _ _ _ (abs_sub_le_of_bounds h1 h2)
    (Q'.ge_of_eqv (QPoly.q_zero_add_eqv e))

/-- Equality of the ACTUAL completed maps implies equality of their original
Haar candidates. The supplied map equality is an input-value identification,
not an assumed integral equality; dense embedding pins recover its content. -/
theorem haarComparison_completed_maps
    (hpin : ∀ x : Point,
      pointExtension F RF rhoF positiveF modF x =
        pointExtension G RG rhoG positiveG modG x) :
    Equiv (haarApproximationReal F RF MF rhoF positiveF boundF modF)
      (haarApproximationReal G RG MG rhoG positiveG boundG modG) := by
  apply haarComparison_equiv F RF MF rhoF positiveF boundF modF
    G RG MG rhoG positiveG boundG modG
  intro q
  apply distance_zero_of_equiv
  have h := hpin (embed q)
  rw [pointExtension_embed, pointExtension_embed] at h
  exact Quotient.exact (s := crealSetoid) h

/-- Literal identical inputs yield presentation independence. The identity
pin is ordinary pointwise equality (refl for the same input), not a supplied
analytic distance estimate or proposed integral value. -/
theorem haarComparison_identical_inputs (hFG : ∀ q, F q = G q) :
    Equiv (haarApproximationReal F RF MF rhoF positiveF boundF modF)
      (haarApproximationReal G RG MG rhoG positiveG boundG modG) := by
  apply haarComparison_equiv F RF MF rhoF positiveF boundF modF
    G RG MG rhoG positiveG boundG modG
  intro q
  rw [hFG q]
  exact self_input_distance_zero (G q)

#print axioms haarComparison_stage
#print axioms haarComparison_distance
#print axioms haarComparison_order
#print axioms haarComparison_equiv
#print axioms haarComparison_completed_maps
#print axioms self_input_distance_zero
#print axioms haarComparison_identical_inputs

end YMGap.Continuum.QuaternionDenseCRealHaarComparison
