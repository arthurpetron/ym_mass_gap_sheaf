/-
# Commutation of rational-polynomial partial derivatives

The raw formal derivatives commute coefficientwise at arbitrary coordinate
indices.  Consequently every derivative commutes with the four-coordinate
head Laplacian, and the degree-sensitive active representative of a derivative
preserves harmonicity.  Tail coefficients remain arbitrary throughout.
-/

import YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

namespace YMGap.Continuum.SU2QuaternionDerivativeCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

local infix:50 " ≈ " => Q'.eqv

private theorem map_coeff {A : Type} (f g : A → RatTerm)
    (h : ∀ a, (f a).1 = (g a).1 ∧ (f a).2 ≈ (g a).2) :
    ∀ xs : List A, RatPolyCoeffEqv (xs.map f) (xs.map g)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => by
      intro weight
      change (f a).2 * weight (f a).1 + ratWeightedSum weight (xs.map f) ≈
        (g a).2 * weight (g a).1 + ratWeightedSum weight (xs.map g)
      rw [(h a).1]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (h a).2)
        (map_coeff f g h xs weight)

private theorem lowerExponentAt_comm : ∀ (first second : Nat) (monomial : List Nat),
    lowerExponentAt first (lowerExponentAt second monomial) =
      lowerExponentAt second (lowerExponentAt first monomial)
  | first, second, [] => by cases first <;> cases second <;> rfl
  | 0, 0, _ :: _ => rfl
  | 0, _ + 1, _ :: _ => rfl
  | _ + 1, 0, _ :: _ => rfl
  | first + 1, second + 1, _ :: rest => by
      simp only [lowerExponentAt, lowerExponentAt_comm first second rest]

private theorem exponentAt_lower_other
    (first second : Nat) (hne : first ≠ second) : ∀ monomial : List Nat,
    exponentAt (lowerExponentAt second monomial) first =
      exponentAt monomial first
  | [] => by cases second <;> rfl
  | _ :: rest => by
      cases first with
      | zero =>
          cases second with
          | zero => exact False.elim (hne rfl)
          | succ _ => rfl
      | succ first =>
          cases second with
          | zero => rfl
          | succ second =>
              simp only [lowerExponentAt, exponentAt]
              exact exponentAt_lower_other first second
                (fun h => hne (congrArg Nat.succ h)) rest

private theorem coefficient_swap (first second coefficient : Q') :
    first * (second * coefficient) ≈ second * (first * coefficient) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ coefficient (Q'.mul_comm_eqv first second))
      (Q'.mul_assoc_eqv _ _ _))

/-- Arbitrary rational-polynomial partial derivatives commute at
coefficient-probe strength, including their retained zero-coefficient terms. -/
theorem ratDerivative_comm (first second : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (ratDerivative first (ratDerivative second polynomial))
      (ratDerivative second (ratDerivative first polynomial)) := by
  simp only [ratDerivative, List.map_map]
  apply map_coeff
  intro term
  constructor
  · exact lowerExponentAt_comm first second term.1
  · by_cases h : first = second
    · subst second
      exact Q'.eqv_refl _
    · change Q'.ofNat (exponentAt (lowerExponentAt second term.1) first) *
          (Q'.ofNat (exponentAt term.1 second) * term.2) ≈
        Q'.ofNat (exponentAt (lowerExponentAt first term.1) second) *
          (Q'.ofNat (exponentAt term.1 first) * term.2)
      rw [exponentAt_lower_other first second h,
          exponentAt_lower_other second first (fun hs => h hs.symm)]
      exact coefficient_swap _ _ _

/-- Every coordinate derivative commutes coefficientwise with the selected
four-coordinate head Laplacian. -/
theorem headLaplacian_derivative
    (coordinate : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (headLaplacian (ratDerivative coordinate polynomial))
      (ratDerivative coordinate (headLaplacian polynomial)) := by
  have hsecond (head : Nat) :
      RatPolyCoeffEqv
        (ratDerivative head
          (ratDerivative head (ratDerivative coordinate polynomial)))
        (ratDerivative coordinate
          (ratDerivative head (ratDerivative head polynomial))) :=
    ((ratDerivative_comm head coordinate polynomial).derivative head).trans
      (ratDerivative_comm head coordinate (ratDerivative head polynomial))
  unfold headLaplacian
  rw [ratDerivative_add_exact, ratDerivative_add_exact,
    ratDerivative_add_exact]
  exact RatPolyCoeffEqv.add (hsecond 0)
    (RatPolyCoeffEqv.add (hsecond 1)
      (RatPolyCoeffEqv.add (hsecond 2) (hsecond 3)))

/-- The active degree-preserving representative of any derivative of a
head-harmonic polynomial is again head harmonic. -/
theorem activeDerivative_harmonic
    (coordinate : Nat) {polynomial : RatPoly}
    (hharmonic : RatPolyCoeffEqv (headLaplacian polynomial) polyZero) :
    RatPolyCoeffEqv
      (headLaplacian (activeDerivative coordinate polynomial)) polyZero := by
  have hzero : RatPolyCoeffEqv
      (ratDerivative coordinate (headLaplacian polynomial)) polyZero := by
    simpa only [ratDerivative, polyZero, List.map_nil] using
      hharmonic.derivative coordinate
  exact (activeDerivative_coeff coordinate polynomial).headLaplacian.trans
    ((headLaplacian_derivative coordinate polynomial).trans hzero)

/-- Multiplication on the right by a literal head-degree-zero polynomial
preserves coefficient-sensitive head harmonicity. -/
theorem harmonic_mul_independent
    {harmonic independent : RatPoly}
    (hharmonic : RatPolyCoeffEqv (headLaplacian harmonic) polyZero)
    (hindependent : HasQuaternionBlockDegree 0 0 independent) :
    RatPolyCoeffEqv
      (headLaplacian (polyMul harmonic independent)) polyZero := by
  have hleft : RatPolyCoeffEqv
      (polyMul (headLaplacian harmonic) independent) polyZero :=
    (hharmonic.mul_right independent).trans
      (RatPolyCoeffEqv.mul_zero_left independent)
  have hgradient : RatPolyCoeffEqv
      (polySmul 2 (headGradientDot harmonic independent)) polyZero :=
    ((headGradientDot_headIndependent_right
      harmonic independent hindependent).smul 2).trans
        (RatPolyCoeffEqv.smul_zero 2)
  have hindependentLaplacian :
      RatPolyCoeffEqv (headLaplacian independent) polyZero := by
    have hcoordinate (coordinate : Nat) (hcoordinate : coordinate < 4) :
        RatPolyCoeffEqv
          (ratDerivative coordinate (ratDerivative coordinate independent))
          polyZero := by
      have hfirst := ratDerivative_eq_zero_of_headDegree_zero
        coordinate hcoordinate independent hindependent
      simpa only [ratDerivative, polyZero, List.map_nil] using
        hfirst.derivative coordinate
    unfold headLaplacian
    exact (RatPolyCoeffEqv.add (hcoordinate 0 (by omega))
      (RatPolyCoeffEqv.add (hcoordinate 1 (by omega))
        (RatPolyCoeffEqv.add (hcoordinate 2 (by omega))
          (hcoordinate 3 (by omega))))).trans
            (RatPolyCoeffEqv.zero_add polyZero)
  have hright : RatPolyCoeffEqv
      (polyMul harmonic (headLaplacian independent)) polyZero :=
    (RatPolyCoeffEqv.mul_left harmonic hindependentLaplacian).trans
      (RatPolyCoeffEqv.mul_zero_right harmonic)
  exact (headLaplacian_mul harmonic independent).trans
    ((RatPolyCoeffEqv.add hleft
      (RatPolyCoeffEqv.add hgradient hright)).trans
        (RatPolyCoeffEqv.zero_add polyZero))

end YMGap.Continuum.SU2QuaternionDerivativeCommutation

#print axioms YMGap.Continuum.SU2QuaternionDerivativeCommutation.ratDerivative_comm
#print axioms YMGap.Continuum.SU2QuaternionDerivativeCommutation.headLaplacian_derivative
#print axioms YMGap.Continuum.SU2QuaternionDerivativeCommutation.activeDerivative_harmonic
#print axioms YMGap.Continuum.SU2QuaternionDerivativeCommutation.harmonic_mul_independent
