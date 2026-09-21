/-
# Dropped-head substitution into the retained quaternion

Substitute the retained quaternion into the selected head and then delete the
four head coordinates.  After this deletion the four head variables and the
four retained variables have the same coefficient-level image.  The endpoint
for a head-degree-zero polynomial is likewise coefficient-exact; no unpadded
pre-drop substitution identity is asserted.
-/

import YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
import YMGap.Continuum.SU2QuaternionHaarBlockProjection

namespace YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

/-- Replace the selected head by retained block one, then remove the padded
head coordinates. -/
def substituteRetained (p : RatPoly) : RatPoly :=
  dropHeadPolynomial
    (translatedHeadPolynomial (PolyQuaternion.coordinateVariable 1) p)

/-- Dropping the head respects constructive coefficient equivalence. -/
theorem dropHeadPolynomial_congr {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (dropHeadPolynomial p) (dropHeadPolynomial q) := by
  intro weight
  have hp : ∀ r : RatPoly,
      ratWeightedSum weight (dropHeadPolynomial r) =
        ratWeightedSum (fun monomial => weight (monomial.drop 4)) r := by
    intro r
    induction r with
    | nil => rfl
    | cons term rest ih =>
        change term.2 * weight (term.1.drop 4) +
            ratWeightedSum weight (dropHeadPolynomial rest) = _
        rw [ih]
        rfl
  rw [hp p, hp q]
  exact h _

private theorem dropHeadPolynomial_add (p q : RatPoly) :
    dropHeadPolynomial (polyAdd p q) =
      polyAdd (dropHeadPolynomial p) (dropHeadPolynomial q) := by
  simp [dropHeadPolynomial, polyAdd, List.map_append]

private theorem dropHeadPolynomial_smul (c : Q') (p : RatPoly) :
    dropHeadPolynomial (polySmul c p) =
      polySmul c (dropHeadPolynomial p) := by
  simp only [dropHeadPolynomial, polySmul, List.map_map]
  rfl

theorem substituteRetained_congr {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (substituteRetained p) (substituteRetained q) :=
  dropHeadPolynomial_congr
    (translatedHeadPolynomial_coeffEqv
      (PolyQuaternion.coordinateVariable 1) h)

theorem substituteRetained_add (p q : RatPoly) :
    RatPolyCoeffEqv (substituteRetained (polyAdd p q))
      (polyAdd (substituteRetained p) (substituteRetained q)) := by
  unfold substituteRetained
  rw [translatedHeadPolynomial_add, dropHeadPolynomial_add]
  exact RatPolyCoeffEqv.refl _

theorem substituteRetained_mul (p q : RatPoly) :
    RatPolyCoeffEqv (substituteRetained (polyMul p q))
      (polyMul (substituteRetained p) (substituteRetained q)) := by
  unfold substituteRetained
  exact (dropHeadPolynomial_congr
      (translatedHeadPolynomial_mul
        (PolyQuaternion.coordinateVariable 1) p q)).trans
    (by
      rw [dropHeadPolynomial_polyMul]
      exact RatPolyCoeffEqv.refl _)

theorem substituteRetained_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (substituteRetained (polySmul c p))
      (polySmul c (substituteRetained p)) := by
  unfold substituteRetained
  exact (dropHeadPolynomial_congr
      (translatedHeadPolynomial_smul
        (PolyQuaternion.coordinateVariable 1) c p)).trans
    (by
      rw [dropHeadPolynomial_smul]
      exact RatPolyCoeffEqv.refl _)

private theorem translatedHeadMonomial_zero
    (q : PolyQuaternion) :
    RatPolyCoeffEqv (translatedHeadMonomial q 0 0 0 0) polyOne := by
  unfold translatedHeadMonomial
  simp only [ratPolyPow]
  exact (RatPolyCoeffEqv.one_mul _).trans
    ((RatPolyCoeffEqv.one_mul _).trans
      (RatPolyCoeffEqv.one_mul _))

private theorem substituteRetained_term_degree_zero
    (term : RatTerm)
    (hdegree : quaternionBlockDegree term.1 0 = 0) :
    RatPolyCoeffEqv
      (dropHeadPolynomial
        (translatedHeadTerm (PolyQuaternion.coordinateVariable 1) term))
      (dropHeadPolynomial [term]) := by
  unfold quaternionBlockDegree at hdegree
  simp only [Nat.mul_zero, Nat.zero_add] at hdegree
  have h0 : exponentAt term.1 0 = 0 := by omega
  have h1 : exponentAt term.1 1 = 0 := by omega
  have h2 : exponentAt term.1 2 = 0 := by omega
  have h3 : exponentAt term.1 3 = 0 := by omega
  unfold translatedHeadTerm
  rw [h0, h1, h2, h3]
  refine (dropHeadPolynomial_congr
      ((translatedHeadMonomial_zero
          (PolyQuaternion.coordinateVariable 1)).mul_right
        (headTailLiftTerm term))).trans ?_
  refine (dropHeadPolynomial_congr
      (RatPolyCoeffEqv.one_mul (headTailLiftTerm term))).trans ?_
  exact RatPolyCoeffEqv.refl _

/-- A polynomial of head degree zero is unchanged after retained substitution
and deletion of the padded head. -/
theorem substituteRetained_degree_zero {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 0 p) :
    RatPolyCoeffEqv (substituteRetained p) (dropHeadPolynomial p) := by
  induction p with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons term rest ih =>
      have hterm := hp term List.mem_cons_self
      have hrest : HasQuaternionBlockDegree 0 0 rest := by
        intro other hother
        exact hp other (List.mem_cons_of_mem term hother)
      unfold substituteRetained
      change RatPolyCoeffEqv
        (dropHeadPolynomial
          (polyAdd
            (translatedHeadTerm (PolyQuaternion.coordinateVariable 1) term)
            (translatedHeadPolynomial
              (PolyQuaternion.coordinateVariable 1) rest)))
        (dropHeadPolynomial (term :: rest))
      rw [dropHeadPolynomial_add]
      change RatPolyCoeffEqv
        (polyAdd
          (dropHeadPolynomial
            (translatedHeadTerm (PolyQuaternion.coordinateVariable 1) term))
          (dropHeadPolynomial
            (translatedHeadPolynomial
              (PolyQuaternion.coordinateVariable 1) rest)))
        (polyAdd (dropHeadPolynomial [term]) (dropHeadPolynomial rest))
      exact (substituteRetained_term_degree_zero term hterm).add (ih hrest)

/-- After dropping the selected head, a selected-head coordinate becomes the
matching retained coordinate. -/
theorem substituteRetained_head_coordinate (i : Fin 4) :
    RatPolyCoeffEqv (substituteRetained (polyVar i.val)) (polyVar i.val) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  revert i
  decide +kernel

/-- After dropping the selected head, an already-retained coordinate becomes
the same matching coordinate in the dropped polynomial. -/
theorem substituteRetained_tail_coordinate (i : Fin 4) :
    RatPolyCoeffEqv (substituteRetained (polyVar (4+i.val))) (polyVar i.val) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  revert i
  decide +kernel

end YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution

#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.dropHeadPolynomial_congr
#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.substituteRetained_congr
#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.substituteRetained_add
#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.substituteRetained_mul
#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.substituteRetained_smul
#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.substituteRetained_degree_zero
#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.substituteRetained_head_coordinate
#print axioms YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution.substituteRetained_tail_coordinate
