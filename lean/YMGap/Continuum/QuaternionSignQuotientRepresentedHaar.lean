/-
Represented original-Haar functions invariant under the two actual embedded
central signs descend to the SAME completed sign-coset group.  This is an
algebraic represented-map domain, not compact SO(3), all continuous Haar,
an interacting action, or a Yang--Mills gap.
-/

import YMGap.RepTheory.RationalQuaternionCompletedSignQuotient
import YMGap.Continuum.QuaternionRepresentedHaarMultiplication

namespace YMGap.Continuum.QuaternionSignQuotientRepresentedHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.QuaternionRepresentedHaar
open YMGap.Continuum.QuaternionRepresentedHaarMultiplication
open YMGap.Continuum.QuaternionRepresentedPolynomialHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation
open YMGap.Continuum.QuaternionPointPolynomialDenseEvaluation
open YMGap.Continuum.RingNormaliser
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionCoordinateCompletion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternionCompletedSignQuotient

/-- Invariance under the ACTUAL two embedded central signs on every completed
point.  This is a property of a represented map, not new admissibility data. -/
def Even (f : Represented) : Prop :=
  ∀ (z : QuaternionSign) (x : Point),
    evaluate f (completedMul x (includeSign z)) = evaluate f x

/-- The concrete represented even-function algebra. -/
def EvenRepresented : Type := {f : Represented // Even f}

def evaluation (f : EvenRepresented) (x : Point) : RC := evaluate f.val x

/-- Evaluation is independent of the chosen completed sign-coset
representative.  The existential coset witness is eliminated only into an
equality proposition. -/
theorem evaluation_coset (f : EvenRepresented) {x y : Point}
    (h : signQuotientGroup.Equivalent x y) : evaluation f x = evaluation f y := by
  apply h.elim
  intro w
  rcases w with ⟨z, hz⟩
  change x = completedMul y (includeSign z) at hz
  rw [hz]
  exact f.property z y

/-- The original-Haar value restricted to the actual even subalgebra. -/
def integration (f : EvenRepresented) : RC := integral f.val

def constant (c : Q') : EvenRepresented :=
  ⟨QuaternionRepresentedHaar.constant c, by
    intro z x
    rw [evaluate_constant, evaluate_constant]⟩

theorem evaluation_constant (c : Q') (x : Point) :
    evaluation (constant c) x =
      Quotient.mk crealSetoid (CReal.ofQ' c) :=
  evaluate_constant c x

theorem integration_constant (c : Q') :
    integration (constant c) =
      Quotient.mk crealSetoid (CReal.ofQ' c) :=
  integral_constant c

def add (f g : EvenRepresented) : EvenRepresented :=
  ⟨QuaternionRepresentedHaar.add f.val g.val, by
    intro z x
    rw [evaluate_add, evaluate_add, f.property z x, g.property z x]⟩

theorem evaluation_add (f g : EvenRepresented) (x : Point) :
    evaluation (add f g) x = RCadd (evaluation f x) (evaluation g x) :=
  evaluate_add f.val g.val x

theorem integration_add (f g : EvenRepresented) :
    integration (add f g) = RCadd (integration f) (integration g) :=
  integral_add f.val g.val

def scale (c : Q') (f : EvenRepresented) : EvenRepresented :=
  ⟨QuaternionRepresentedHaar.scale c f.val, by
    intro z x
    rw [evaluate_scale, evaluate_scale, f.property z x]⟩

theorem evaluation_scale (c : Q') (f : EvenRepresented) (x : Point) :
    evaluation (scale c f) x = RCscale c (evaluation f x) :=
  evaluate_scale c f.val x

theorem integration_scale (c : Q') (f : EvenRepresented) :
    integration (scale c f) = RCscale c (integration f) :=
  integral_scale c f.val

def mul (f g : EvenRepresented) : EvenRepresented :=
  ⟨QuaternionRepresentedHaarMultiplication.mul f.val g.val, by
    intro z x
    rw [evaluate_mul, evaluate_mul, f.property z x, g.property z x]⟩

theorem evaluation_mul (f g : EvenRepresented) (x : Point) :
    evaluation (mul f g) x = RCmul (evaluation f x) (evaluation g x) :=
  evaluate_mul f.val g.val x

theorem integration_lower (f : EvenRepresented) (c : Q')
    (h : ∀ x : Point,
      RCle (Quotient.mk crealSetoid (CReal.ofQ' c)) (evaluation f x)) :
    RCle (Quotient.mk crealSetoid (CReal.ofQ' c)) (integration f) :=
  integral_lower f.val c h

theorem integration_nonnegative (f : EvenRepresented)
    (h : ∀ x : Point, RCnonneg (evaluation f x)) :
    RCnonneg (integration f) :=
  integral_nonnegative f.val h

private theorem translate_right_sign (x g : Point) (z : QuaternionSign) :
    completedMul (completedMul x (includeSign z)) g =
      completedMul (completedMul x g) (includeSign z) := by
  rw [completedMul_assoc, includeSign_central z g, ← completedMul_assoc]

private theorem translate_left_sign (x g : Point) (z : QuaternionSign) :
    completedMul g (completedMul x (includeSign z)) =
      completedMul (completedMul g x) (includeSign z) := by
  rw [← completedMul_assoc]

/-- Both completed translations preserve evenness. -/
def translate (right : Bool) (g : Point) (f : EvenRepresented) : EvenRepresented :=
  ⟨QuaternionRepresentedHaar.translate right g f.val, by
    intro z x
    rw [evaluate_translate, evaluate_translate]
    cases right with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [translate_left_sign]
        exact f.property z (completedMul g x)
    | true =>
        simp only [↓reduceIte]
        rw [translate_right_sign]
        exact f.property z (completedMul x g)⟩

theorem evaluation_translate (right : Bool) (g : Point)
    (f : EvenRepresented) (x : Point) :
    evaluation (translate right g f) x =
      evaluation f (if right then completedMul x g else completedMul g x) :=
  QuaternionRepresentedHaar.evaluate_translate right g f.val x

/-- The multiplier, too, is a sign coset: no locator on completed points is
needed to descend either Hamilton order. -/
theorem translate_coset (right : Bool) (f : EvenRepresented) {g h : Point}
    (hgh : signQuotientGroup.Equivalent g h) :
    (translate right g f).val = (translate right h f).val := by
  apply QuaternionRepresentedHaar.ext
  intro x
  change evaluation (translate right g f) x =
    evaluation (translate right h f) x
  rw [evaluation_translate, evaluation_translate]
  apply hgh.elim
  intro w
  rcases w with ⟨z, hz⟩
  change g = completedMul h (includeSign z) at hz
  rw [hz]
  cases right with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [completedMul_assoc, includeSign_central z x, ← completedMul_assoc]
      exact f.property z (completedMul h x)
  | true =>
      simp only [↓reduceIte]
      rw [← completedMul_assoc]
      exact f.property z (completedMul x h)

theorem translate_coset_eq (right : Bool) (f : EvenRepresented) {g h : Point}
    (hgh : signQuotientGroup.Equivalent g h) :
    translate right g f = translate right h f :=
  Subtype.ext (translate_coset right f hgh)

theorem integration_translate (right : Bool) (g : Point) (f : EvenRepresented) :
    integration (translate right g f) = integration f :=
  QuaternionRepresentedHaar.integral_translate right g f.val

local infix:50 " ≈ " => Q'.eqv

/-- The actual spin-one character on unit quaternions: 4 r² - 1.
Its two terms are signed, and it is not the first available even mode. -/
def chiTwoPolynomial : RatPoly := [([2], 4), ([], -1)]

private theorem chiTwo_value (rho : Nat → Q') :
    evalRatPoly rho chiTwoPolynomial ≈ 4*(rho 0*rho 0)+(-1) := by
  change (4 : Q') * (((1*rho 0)*rho 0)*1) + ((-1:Q')*1+0) ≈ _
  exact poly_identity_of_normal_eq
    (.add (.mul (.const 4)
      (.mul (.mul (.mul (.const 1) (.var 0)) (.var 0)) (.const 1)))
      (.add (.mul (.const (-1)) (.const 1)) (.const 0)))
    (.add (.mul (.const 4) (.mul (.var 0) (.var 0))) (.const (-1)))
    (by decide) (fun _ => rho 0)

private theorem scalar_negative_r (a : RationalQuaternion) :
    (RationalQuaternion.mul a unitNegativeOne.val).r ≈ -a.r := by
  change ((a.r * -(1:Q') + -(a.i * -(0:Q'))) +
      (-(a.j * -(0:Q')) + -(a.k * -(0:Q')))) ≈ -a.r
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.neg (.const 1)))
      (.neg (.mul (.var 1) (.neg (.const 0)))))
      (.add (.neg (.mul (.var 2) (.neg (.const 0))))
        (.neg (.mul (.var 3) (.neg (.const 0))))))
    (.neg (.var 0)) (by decide)
    (fun | 0 => a.r | 1 => a.i | 2 => a.j | _ => a.k)

private theorem chiTwo_raw_antipodal (q : UnitNorm) :
    evalRatPoly (quaternionCoordinates (UnitNorm.mul q unitNegativeOne).val)
      chiTwoPolynomial ≈
      evalRatPoly (quaternionCoordinates q.val) chiTwoPolynomial := by
  let t := (RationalQuaternion.mul q.val unitNegativeOne.val).r
  have ht : t ≈ -q.val.r := scalar_negative_r q.val
  have hp : 4*(t*t)+(-1) ≈ 4*(q.val.r*q.val.r)+(-1) := by
    have hsq : t*t ≈ (-q.val.r)*(-q.val.r) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ht)
        (Q'.mul_eqv_congr_left _ _ _ ht)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hsq))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 4)
          (.mul (.neg (.var 0)) (.neg (.var 0)))) (.const (-1)))
        (.add (.mul (.const 4) (.mul (.var 0) (.var 0))) (.const (-1)))
        (by decide) (fun _ => q.val.r))
  exact Q'.eqv_trans _ _ _ (chiTwo_value _)
    (Q'.eqv_trans _ _ _ hp (Q'.eqv_symm (chiTwo_value _)))

/-- The finite antipodal identity is transported on the SAME explicit-modulus
point rows; no density axiom or representative of a completed point is used. -/
theorem chiTwo_antipodal (x : Point) :
    evaluate (polynomial chiTwoPolynomial)
      (completedMul x (includeSign .negative)) =
      evaluate (polynomial chiTwoPolynomial) x := by
  rw [evaluate_polynomial, evaluate_polynomial]
  refine Quotient.inductionOn x (fun X => ?_)
  change pointEval (completedMul (Quotient.mk chordSeminorm.completionSetoid X)
      (embed unitNegativeOne)) chiTwoPolynomial =
    pointEval (Quotient.mk chordSeminorm.completionSetoid X) chiTwoPolynomial
  change pointEval (multiplication.completionMap
      (Quotient.mk chordSeminorm.completionSetoid X)
      (Quotient.mk chordSeminorm.completionSetoid
        (chordSeminorm.constant unitNegativeOne))) chiTwoPolynomial =
    pointEval (Quotient.mk chordSeminorm.completionSetoid X) chiTwoPolynomial
  rw [YMGap.Continuum.CRealSeminormCompletion.SquaredSeminorm.BinaryQuadraticLipschitz.completionMap_mk,
    pointEval_rowPolynomialEval, pointEval_rowPolynomialEval]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  rw [rowPolynomialEval_approx, rowPolynomialEval_approx]
  exact chiTwo_raw_antipodal (X.seq n)

/-- The concrete spin-one character descends to completed sign cosets. -/
def chiTwo : EvenRepresented :=
  ⟨polynomial chiTwoPolynomial, by
    intro z x
    cases z with
    | positive =>
        change evaluate (polynomial chiTwoPolynomial)
          (completedMul x completedOne) = _
        rw [completedMul_one]
    | negative => exact chiTwo_antipodal x⟩

theorem chiTwo_supported : SupportedQuaternionBlocks 1 chiTwoPolynomial := by
  intro t ht
  simp only [chiTwoPolynomial, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> decide

theorem chiTwo_square_supported :
    SupportedQuaternionBlocks 1
      (polyMul chiTwoPolynomial chiTwoPolynomial) :=
  supported_polyMul chiTwo_supported chiTwo_supported

theorem chiTwo_mean_zero : integration chiTwo = rational 0 := by
  change integral (polynomial chiTwoPolynomial) = rational 0
  rw [integral_polynomial _ chiTwo_supported]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

/-- Same represented function, same ORIGINAL one-block Haar, general product. -/
theorem chiTwo_same_square_one :
    integration (mul chiTwo chiTwo) = rational 1 := by
  change integral (QuaternionRepresentedHaarMultiplication.mul
    (polynomial chiTwoPolynomial) (polynomial chiTwoPolynomial)) = rational 1
  rw [mul_polynomial, integral_polynomial _ chiTwo_square_supported]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

private theorem chiTwo_at_one :
    evaluation chiTwo (embed unitOne) = rational 3 := by
  change evaluate (polynomial chiTwoPolynomial) (embed unitOne) = rational 3
  rw [evaluate_polynomial, pointEval_embed]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

private theorem chiTwo_at_i :
    evaluation chiTwo
      (embed YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.equatorialUnit) =
      rational (-1) := by
  change evaluate (polynomial chiTwoPolynomial)
    (embed YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.equatorialUnit) =
    rational (-1)
  rw [evaluate_polynomial, pointEval_embed]
  exact Quotient.sound (TrigAdd.equiv_ofQ'_of_eqv (by decide))

theorem chiTwo_nonconstant :
    evaluation chiTwo (embed unitOne) ≠
      evaluation chiTwo
        (embed YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.equatorialUnit) := by
  intro h
  rw [chiTwo_at_one, chiTwo_at_i] at h
  have he : Equiv (CReal.ofQ' 3) (CReal.ofQ' (-1)) := Quotient.exact h
  obtain ⟨N, hN⟩ := he 1 (by decide)
  have hb : (3:Q') ≤ (-1:Q')+1 := (hN N (Nat.le_refl N)).1
  exact (by decide : ¬ ((3:Q') ≤ (-1:Q')+1)) hb

#print axioms Even
#print axioms EvenRepresented
#print axioms evaluation_coset
#print axioms integration
#print axioms integration_constant
#print axioms evaluation_constant
#print axioms constant
#print axioms add
#print axioms evaluation_add
#print axioms integration_add
#print axioms scale
#print axioms integration_scale
#print axioms evaluation_scale
#print axioms mul
#print axioms evaluation_mul
#print axioms integration_lower
#print axioms integration_nonnegative
#print axioms translate
#print axioms evaluation_translate
#print axioms translate_coset
#print axioms translate_coset_eq
#print axioms integration_translate
#print axioms chiTwoPolynomial
#print axioms chiTwo_antipodal
#print axioms chiTwo
#print axioms chiTwo_supported
#print axioms chiTwo_square_supported
#print axioms chiTwo_mean_zero
#print axioms chiTwo_same_square_one
#print axioms chiTwo_nonconstant

end YMGap.Continuum.QuaternionSignQuotientRepresentedHaar
