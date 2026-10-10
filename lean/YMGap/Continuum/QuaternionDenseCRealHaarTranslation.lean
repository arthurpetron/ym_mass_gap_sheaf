/-
Actual rational left/right translation of admissible dense CReal data.
The original bound, inner rates and continuity radius are transported by
the exact chord isometry. Original polynomial evaluation and Haar invariance
compare the independently constructed stages with two vanishing errors.
The actual completed-map composition pin covers every Point, without choosing
representatives. Multipliers here are rational UNIT quaternions; arbitrary
completed multipliers, full continuous Haar/J04, MAIN scaling and Clay remain
open.
-/

import YMGap.Continuum.QuaternionDenseCRealHaarHomogeneity
import YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation
import YMGap.RepTheory.RationalQuaternionCauchyGroup
import YMGap.RepTheory.RationalQuaternionUnitNormGroup
import YMGap.Continuum.QuaternionDenseCRealPointExtension

namespace YMGap.Continuum.QuaternionDenseCRealHaarTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.QuaternionPointBernsteinCRealApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.Continuum.QuaternionDenseCRealPointExtension

local infix:50 " ≈ " => Q'.eqv

/-- Left or right translation by the supplied rational unit quaternion. -/
def translatePoint (right : Bool) (g q : UnitNorm) : UnitNorm :=
  if right then UnitNorm.mul q g else UnitNorm.mul g q

/-- Both multiplication orders preserve the actual rational squared chord. -/
theorem translate_distSq (right : Bool) (g q x : UnitNorm) :
    distSq (translatePoint right g q).val (translatePoint right g x).val ≈
      distSq q.val x.val := by
  cases right with
  | false =>
      change chord (UnitNorm.mul g q) (UnitNorm.mul g x) ≈ chord q x
      exact chord_mul_left g q x
  | true =>
      change chord (UnitNorm.mul q g) (UnitNorm.mul x g) ≈ chord q x
      exact chord_mul_right q x g

/-- Actual translated input, evaluated at the translated dense point. -/
def translateInput (right : Bool) (g : UnitNorm)
    (F : UnitNorm → CReal) (q : UnitNorm) : CReal :=
  F (translatePoint right g q)

/-- Translation transports the existing Type-level inner rate pointwise. -/
def translateInner (right : Bool) (g : UnitNorm)
    (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q)) :
    ∀ q, InnerRegularity (translateInput right g F q) :=
  fun q => R (translatePoint right g q)

/-- Translation inherits the sound input bound at its actual translated point. -/
theorem translate_bound (right : Bool) (g : UnitNorm)
    (F : UnitNorm → CReal) (M : Q')
    (bound : ∀ q, leRat (CReal.abs (F q)) M) (q : UnitNorm) :
    leRat (CReal.abs (translateInput right g F q)) M :=
  bound (translatePoint right g q)

/-- Translation preserves the same supplied continuity radius by exact chord
invariance; no monotonicity or new modulus is required. -/
theorem translate_modulus (right : Bool) (g : UnitNorm)
    (F : UnitNorm → CReal) (radius : Q' → Q')
    (modulus : ∀ e, (0 : Q') < e → ∀ q x,
      distSq q.val x.val ≤ radius e →
        leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
    (e : Q') (he : (0 : Q') < e) (q x : UnitNorm)
    (hd : distSq q.val x.val ≤ radius e) :
    leRat (CReal.abs (CReal.add (translateInput right g F q)
      (CReal.neg (translateInput right g F x)))) e := by
  have hd' :
      distSq (translatePoint right g q).val (translatePoint right g x).val ≤ radius e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (translate_distSq right g q x)) hd
  exact modulus e he (translatePoint right g q) (translatePoint right g x) hd'

private theorem environment_pin (q : RationalQuaternion) :
    quaternionCoordinates q = environmentOf q := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | k+4 =>
      have hk : ¬ k+4 < 4 := by omega
      simp [quaternionCoordinates, environmentOf, hk]

private theorem translated_evaluation (right : Bool) (g q : UnitNorm)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    evalRatPoly (environmentOf q.val) (fixedTranslatedPolynomial right g p) ≈
      evalRatPoly (environmentOf (translatePoint right g q).val) p := by
  rw [← environment_pin, ← environment_pin]
  cases right with
  | false => exact fixedTranslatedPolynomial_eval false g q p hp
  | true => exact fixedTranslatedPolynomial_eval true g q p hp

private theorem distance_symm {a b : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta) :
    leRat (CReal.abs (CReal.add b (CReal.neg a))) eta := by
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hK n hn)

variable (right : Bool) (g : UnitNorm)
variable (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
variable (M : Q') (radius : Q' → Q')
variable (radius_positive : ∀ e, (0 : Q') < e → (0 : Q') < radius e)
variable (hM : ∀ q, leRat (CReal.abs (F q)) M)
variable (hmod : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ radius e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

/-- ORIGINAL Haar of the actual translated input, using produced data only. -/
def translateHaar : CReal :=
  haarApproximationReal (translateInput right g F) (translateInner right g F R)
    M radius radius_positive (translate_bound right g F M hM)
    (translate_modulus right g F radius hmod)

/-- The actual translated candidate retains the computed den(epsilon/2) rate. -/
def translateHaarInnerRegularity :
    InnerRegularity (translateHaar right g F R M radius radius_positive hM hmod) :=
  haarApproximationInnerRegularity (translateInput right g F)
    (translateInner right g F R) M radius radius_positive
    (translate_bound right g F M hM) (translate_modulus right g F radius hmod)

include radius_positive hM hmod in
/-- Actual translated and original Haar stages differ by at most two stage
errors. Their independently sampled polynomials are NOT identified. -/
theorem translateHaar_stage (n : Nat) :
    Q'.abs (haarApproximationValue (translateInput right g F)
      (translateInner right g F R) M radius n +
      -(haarApproximationValue F R M radius n)) ≤
      Q'.invSucc n + Q'.invSucc n := by
  let tau := Q'.invSucc n
  let pf := haarApproximationPolynomial F R M radius n
  let p := fixedTranslatedPolynomial right g pf
  have hpf : SupportedQuaternionBlocks 1 pf :=
    realApproximation_supported F R tau _
  have hp : SupportedQuaternionBlocks 1 p :=
    fixedTranslatedPolynomial_supported right g pf
  have hclose (q : UnitNorm) :
      leRat (CReal.abs (CReal.add (translateInput right g F q)
        (CReal.neg (CReal.ofQ' (evalRatPoly (environmentOf q.val) p))))) tau := by
    have hf := distance_symm
      (realApproximation_error F R M radius radius_positive hM hmod
        tau (Q'.invSucc_pos n) _ (Nat.le_refl _) (translatePoint right g q))
    intro e he
    obtain ⟨K, hK⟩ := hf e he
    refine ⟨K, fun j hj => ?_⟩
    have hpin : (translateInput right g F q).approx j +
        -(evalRatPoly (environmentOf q.val) p) ≈
        (F (translatePoint right g q)).approx j +
          -(evalRatPoly (environmentOf (translatePoint right g q).val) pf) :=
      Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (translated_evaluation right g q pf hpf))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin)) (hK j hj)
  have hb := haarApproximation_polynomial_distance
    (translateInput right g F) (translateInner right g F R) M radius
    radius_positive (translate_bound right g F M hM)
    (translate_modulus right g F radius hmod) p hp tau hclose n
  have hpin : haarApproximationValue (translateInput right g F)
      (translateInner right g F R) M radius n + -(quaternionHaar 1 p) ≈
      haarApproximationValue (translateInput right g F)
        (translateInner right g F R) M radius n +
        -(haarApproximationValue F R M radius n) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (fixedTranslatedPolynomial_haar right g pf hpf))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Q'.eqv_symm hpin))) hb

/-- Recoverable equality cutoff paying both vanishing approximation errors. -/
def translateHaarEqualityRate (epsilon : Q') : Nat :=
  (HalfPow.half * epsilon).den

private theorem translate_tail_budget (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : translateHaarEqualityRate epsilon ≤ n) :
    Q'.invSucc n + Q'.invSucc n ≤ epsilon := by
  have hh : (0 : Q') < HalfPow.half * epsilon := Q'.mul_pos (by decide) he
  have hs : Q'.invSucc n ≤ HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le _ hh)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add hs hs)
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

/-- Actual original-Haar invariance for either rational unit multiplication
order, with an explicit cutoff and no integral identity assumed. -/
theorem translateHaar_invariant :
    Equiv (translateHaar right g F R M radius radius_positive hM hmod)
      (haarApproximationReal F R M radius radius_positive hM hmod) := by
  intro epsilon he
  refine ⟨translateHaarEqualityRate epsilon, fun n hn => ?_⟩
  have hb := Q'.le_trans' _ _ _
    (translateHaar_stage right g F R M radius radius_positive hM hmod n)
    (translate_tail_budget epsilon he n hn)
  exact ⟨ExpNeg.le_add_of_abs_sub_le hb,
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hb)⟩

/-- The ACTUAL translated extension is composition with the SAME completed
Hamilton product, for every Point and a rational unit multiplier. Literal
row samples agree; no representative is selected from either quotient. -/
theorem translateExtension_value (x : Point) :
    pointExtension (translateInput right g F) (translateInner right g F R)
      radius radius_positive (translate_modulus right g F radius hmod) x =
    pointExtension F R radius radius_positive hmod
      (if right then completedMul x (embed g) else completedMul (embed g) x) := by
  refine Quotient.inductionOn x (fun X => ?_)
  cases right <;> apply Quotient.sound <;>
    apply SumOfSquares.Equiv_of_approx_eqv <;> intro n <;> exact Q'.eqv_refl _

#print axioms translatePoint
#print axioms translate_distSq
#print axioms translateInput
#print axioms translateInner
#print axioms translate_bound
#print axioms translate_modulus
#print axioms translateHaar
#print axioms translateHaarInnerRegularity
#print axioms translateHaar_stage
#print axioms translateHaarEqualityRate
#print axioms translateHaar_invariant
#print axioms translateExtension_value

end YMGap.Continuum.QuaternionDenseCRealHaarTranslation
