/-
# All-degree Gaussian recursion for the actual quaternion translations

The four coordinates of a*u (or u*a) are head-linear and harmonic, and
their head-gradient Gram matrix is |a|^2 times the identity. These are
small exact coefficient certificates about the ORIGINAL Hamilton products.

Coefficient-retaining Gaussian IBP then gives an all-word-length Wick
recursion. Only equal coordinate labels contract. The tail radius and
all tail polynomial coefficients remain explicit. The closed moment
formula, sphere conversion and full Haar translation are NOT asserted here.
-/

import YMGap.Continuum.SU2QuaternionHeadGaussianIBP
import YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionTranslationGaussianStein

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP

/-- Actual Hamilton product coordinate: false selects a*u, true selects u*a.
The head quaternion is u (block zero); a is the retained block one. -/
def translatedCoordinate (right : Bool) (i : Fin 4) : RatPoly :=
  let q := if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion
  match i.val with
  | 0 => q.scalar
  | 1 => q.iPart
  | 2 => q.jPart
  | _ => q.kPart

/-- The actual translated coordinates have degree one in the head variables. -/
theorem translatedCoordinate_euler (right : Bool) (i : Fin 4) :
    RatPolyCoeffEqv (headEuler (translatedCoordinate right i)) (translatedCoordinate right i) := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> cases right <;>
    dsimp only [translatedCoordinate] <;>
    apply RatPolyCoeffEqv.of_canon_termwise <;> decide

theorem translatedCoordinate_harmonic (right : Bool) (i : Fin 4) :
    RatPolyCoeffEqv (headLaplacian (translatedCoordinate right i)) polyZero := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> cases right <;>
    dsimp only [translatedCoordinate] <;>
    apply RatPolyCoeffEqv.of_canon_termwise <;> decide

/-- The head-gradient frame is orthogonal with the ORIGINAL tail radius.
No unit-radius assumption is made before integration. -/
theorem translatedCoordinate_gradient (right : Bool) (i j : Fin 4) :
    RatPolyCoeffEqv (headGradientDot (translatedCoordinate right i) (translatedCoordinate right j))
      (if i = j then quaternionRadiusPolynomial 1 else polyZero) := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have k : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;>
    rcases k with rfl | rfl | rfl | rfl <;> cases right <;>
      simp only [Fin.mk.injEq] <;> dsimp only [translatedCoordinate] <;>
      apply RatPolyCoeffEqv.of_canon_termwise <;> decide

/-- Actual quaternion translation coordinates satisfy the Stein identity
for EVERY polynomial, not just polynomials beneath a certificate cutoff. -/
theorem translatedCoordinate_stein (right : Bool) (i : Fin 4) (p : RatPoly) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul (translatedCoordinate right i) p))
      (partialGaussianHead (headGradientDot (translatedCoordinate right i) p)) :=
  partialGaussianHead_linear_stein _ _ (translatedCoordinate_euler right i) (translatedCoordinate_harmonic right i)

/-- Ordered product of any finite list of actual translated coordinates. -/
def translatedWord (right : Bool) : List (Fin 4) → RatPoly
  | [] => polyOne
  | i :: rest => polyMul (translatedCoordinate right i) (translatedWord right rest)

/-- Explicit Wick contractions of one leading coordinate against the word.
Equal labels contribute the actual radius; unequal labels contribute zero.
The recursion retains all surviving coordinate factors and their order. -/
def contractedWord (right : Bool) (i : Fin 4) : List (Fin 4) → RatPoly
  | [] => polyZero
  | j :: rest => polyAdd
      (polyMul (if i = j then quaternionRadiusPolynomial 1 else polyZero) (translatedWord right rest))
      (polyMul (translatedCoordinate right j) (contractedWord right i rest))

/-- Leibniz and the actual gradient frame generate the finite contraction
sum at arbitrary word length, before any integration. -/
theorem translatedWord_gradient (right : Bool) (i : Fin 4) : ∀ word : List (Fin 4),
    RatPolyCoeffEqv (headGradientDot (translatedCoordinate right i) (translatedWord right word))
      (contractedWord right i word)
  | [] => headGradientDot_headIndependent_right _ _ (hasQuaternionBlockDegree_one 0)
  | j :: rest => (headGradientDot_mul_right _ _ _).trans
      (((translatedCoordinate_gradient right i j).mul_right (translatedWord right rest)).add
        ((translatedWord_gradient right i rest).mul_left (translatedCoordinate right j)))

/-- All-degree moment recursion for the ORIGINAL left/right translated word,
with every tail coefficient retained. No moment equality is a hypothesis. -/
theorem translatedWord_gaussian_recursion (right : Bool) (i : Fin 4) (word : List (Fin 4)) :
    RatPolyCoeffEqv (partialGaussianHead (translatedWord right (i :: word)))
      (partialGaussianHead (contractedWord right i word)) :=
  (translatedCoordinate_stein right i (translatedWord right word)).trans
    (partialGaussianHead_congr (translatedWord_gradient right i word))

theorem translatedWord_append (right : Bool) : ∀ xs ys : List (Fin 4),
    RatPolyCoeffEqv (translatedWord right (xs ++ ys))
      (polyMul (translatedWord right xs) (translatedWord right ys))
  | [], _ => (RatPolyCoeffEqv.one_mul _).symm
  | i :: xs, ys => ((translatedWord_append right xs ys).mul_left (translatedCoordinate right i)).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm

theorem translatedWord_replicate (right : Bool) (i : Fin 4) : ∀ n : Nat,
    RatPolyCoeffEqv (translatedWord right (List.replicate n i))
      (ratPolyPow (translatedCoordinate right i) n)
  | 0 => RatPolyCoeffEqv.refl _
  | n + 1 => ((translatedWord_replicate right i n).mul_left (translatedCoordinate right i)).trans
      (RatPolyCoeffEqv.mul_comm _ _)

/-- The explicit coordinate word corresponding to the EXISTING four-exponent
translation-moment API. No new moment family is substituted for that API. -/
def translatedExponentWord (e0 e1 e2 e3 : Nat) : List (Fin 4) :=
  List.replicate e0 0 ++ (List.replicate e1 1 ++ (List.replicate e2 2 ++ List.replicate e3 3))

/-- The original translatedHeadMonomial is exactly the coordinate word to
which the all-degree Gaussian recursion applies, coefficientwise. -/
theorem translatedHeadMonomial_eq_word (right : Bool) (e0 e1 e2 e3 : Nat) :
    RatPolyCoeffEqv (translatedHeadMonomial
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) e0 e1 e2 e3)
      (translatedWord right (translatedExponentWord e0 e1 e2 e3)) := by
  apply RatPolyCoeffEqv.symm
  refine (translatedWord_append right (List.replicate e0 0) _).trans ?_
  apply RatPolyCoeffEqv.mul (translatedWord_replicate right 0 e0)
  refine (translatedWord_append right (List.replicate e1 1) _).trans ?_
  apply RatPolyCoeffEqv.mul (translatedWord_replicate right 1 e1)
  exact (translatedWord_append right (List.replicate e2 2) (List.replicate e3 3)).trans
    ((translatedWord_replicate right 2 e2).mul (translatedWord_replicate right 3 e3))

end YMGap.Continuum.SU2QuaternionTranslationGaussianStein

#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedCoordinate
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedCoordinate_euler
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedCoordinate_harmonic
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedCoordinate_gradient
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedCoordinate_stein
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedWord
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.contractedWord
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedWord_gradient
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedWord_gaussian_recursion
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedWord_append
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedWord_replicate
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedExponentWord
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianStein.translatedHeadMonomial_eq_word
