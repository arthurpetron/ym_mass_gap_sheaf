/-
# Finite interaction features for original weighted conditional moments

Only the shared interaction K is expanded. The one-sided weights L,R and
tests f,g remain inside their exact one-link Haar moments. Consequently the
number of moment pairs is K.length, independent of the degrees of f and g.
All unselected coordinates remain polynomial coefficients, not sampled data.

This is an exact finite-cutoff reduction, not a uniform finite-rank claim,
Gram-matrix estimate, inverse-normalizer bound or spectral-gap theorem.
The consumer is the original two-link normalizer and signed covariance.
-/

import YMGap.Continuum.SU2QuaternionBlockMonomialFeatures

namespace YMGap.Continuum.SU2QuaternionSeparableConditionalMoments

set_option autoImplicit false

open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionBlockMonomialFeatures

/-- The coefficient and exterior coordinates are retained on this side. -/
def leftMoment (a b : Nat) (L f : RatPoly) (t : RatTerm) : RatPoly :=
  project a (polyMul (polyMul L f) (outsideFeature b t))

def rightMoment (b : Nat) (R g : RatPoly) (t : RatTerm) : RatPoly :=
  project b (polyMul (polyMul R g) (insideFeature b t))

/-- The indexing list is the shared interaction, never a test expansion. -/
def featureMoment (a b : Nat) (L R f g : RatPoly) : RatPoly → RatPoly
  | [] => polyZero
  | t :: K => polyAdd
      (polyMul (leftMoment a b L f t) (rightMoment b R g t))
      (featureMoment a b L R f g K)

theorem separated_pair (a b : Nat) (F G : RatPoly)
    (hF : QuaternionBlockIndependent b F)
    (hG : QuaternionBlockIndependent a G) :
    RatPolyCoeffEqv (familyProject [a, b] (polyMul F G))
      (polyMul (project a F) (project b G)) :=
  (project_congr b (project_mul_right_of_independent a F G hG)).trans
    (project_mul_of_independent b (project a F) G
      (project_preserves_independent a hF))

theorem weighted_term (a b : Nat) (hne : a ≠ b)
    (L R f g : RatPoly) (t : RatTerm)
    (hL : QuaternionBlockIndependent b L)
    (hR : QuaternionBlockIndependent a R)
    (hf : QuaternionBlockIndependent b f)
    (hg : QuaternionBlockIndependent a g) :
    RatPolyCoeffEqv
      (familyProject [a, b] (polyMul (polyMul (polyMul L R) [t]) (polyMul f g)))
      (polyMul (leftMoment a b L f t) (rightMoment b R g t)) := by
  have hreorder : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul L R)
        (polyMul (outsideFeature b t) (insideFeature b t))) (polyMul f g))
      (polyMul (polyMul (polyMul L f) (outsideFeature b t))
        (polyMul (polyMul R g) (insideFeature b t))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 4) (.var 5)))
        (.mul (.var 2) (.var 3)))
      (.mul (.mul (.mul (.var 0) (.var 2)) (.var 4))
        (.mul (.mul (.var 1) (.var 3)) (.var 5))) (by decide)
      (fun | 0 => L | 1 => R | 2 => f | 3 => g
           | 4 => outsideFeature b t | _ => insideFeature b t)
  exact (familyProject_congr [a, b]
    ((((term_factorization b t).mul_left (polyMul L R)).mul_right
      (polyMul f g)).trans hreorder)).trans
    (separated_pair a b _ _
      (quaternionBlockIndependent_polyMul
        (quaternionBlockIndependent_polyMul hL hf) (outside_independent b t))
      (quaternionBlockIndependent_polyMul
        (quaternionBlockIndependent_polyMul hR hg) (inside_independent a b hne t)))

/-- Exact weighted reduction for arbitrary-degree, opposite-block-independent
tests. No positivity assumption or exterior integration is used. -/
theorem weighted_moment (a b : Nat) (hne : a ≠ b)
    (L R f g : RatPoly)
    (hL : QuaternionBlockIndependent b L)
    (hR : QuaternionBlockIndependent a R)
    (hf : QuaternionBlockIndependent b f)
    (hg : QuaternionBlockIndependent a g) (K : RatPoly) :
    RatPolyCoeffEqv
      (familyProject [a, b] (polyMul (polyMul (polyMul L R) K) (polyMul f g)))
      (featureMoment a b L R f g K) := by
  induction K with
  | nil =>
      exact (familyProject_congr [a, b]
        (((RatPolyCoeffEqv.mul_zero_right (polyMul L R)).mul_right
          (polyMul f g)).trans (RatPolyCoeffEqv.mul_zero_left _))).trans
        (RatPolyCoeffEqv.refl polyZero)
  | cons t K ih =>
      have hsplit : RatPolyCoeffEqv
          (polyMul (polyMul (polyMul L R) (t :: K)) (polyMul f g))
          (polyAdd (polyMul (polyMul (polyMul L R) [t]) (polyMul f g))
            (polyMul (polyMul (polyMul L R) K) (polyMul f g))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
          (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
            (.mul (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
          (fun | 0 => polyMul L R | 1 => [t] | 2 => K | _ => polyMul f g)
      refine (familyProject_congr [a, b] hsplit).trans ?_
      rw [familyProject_add]
      exact (weighted_term a b hne L R f g t hL hR hf hg).add ih

theorem leftMoment_independent_left (a b : Nat) (L f : RatPoly) (t : RatTerm) :
    QuaternionBlockIndependent a (leftMoment a b L f t) :=
  project_independent a _

theorem leftMoment_independent_right (a b : Nat) (L f : RatPoly) (t : RatTerm)
    (hL : QuaternionBlockIndependent b L) (hf : QuaternionBlockIndependent b f) :
    QuaternionBlockIndependent b (leftMoment a b L f t) :=
  project_preserves_independent a (quaternionBlockIndependent_polyMul
    (quaternionBlockIndependent_polyMul hL hf) (outside_independent b t))

theorem rightMoment_independent_left (a b : Nat) (hne : a ≠ b)
    (R g : RatPoly) (t : RatTerm)
    (hR : QuaternionBlockIndependent a R) (hg : QuaternionBlockIndependent a g) :
    QuaternionBlockIndependent a (rightMoment b R g t) :=
  project_preserves_independent b (quaternionBlockIndependent_polyMul
    (quaternionBlockIndependent_polyMul hR hg) (inside_independent a b hne t))

theorem rightMoment_independent_right (b : Nat) (R g : RatPoly) (t : RatTerm) :
    QuaternionBlockIndependent b (rightMoment b R g t) :=
  project_independent b _

theorem featureMoment_independent (a b : Nat) (hne : a ≠ b)
    (L R f g K : RatPoly)
    (hL : QuaternionBlockIndependent b L) (hR : QuaternionBlockIndependent a R)
    (hf : QuaternionBlockIndependent b f) (hg : QuaternionBlockIndependent a g) :
    QuaternionBlockIndependent a (featureMoment a b L R f g K) ∧
      QuaternionBlockIndependent b (featureMoment a b L R f g K) := by
  induction K with
  | nil => exact ⟨quaternionBlockIndependent_polyZero a,
      quaternionBlockIndependent_polyZero b⟩
  | cons t K ih =>
      exact ⟨quaternionBlockIndependent_polyAdd
        (quaternionBlockIndependent_polyMul (leftMoment_independent_left a b L f t)
          (rightMoment_independent_left a b hne R g t hR hg)) ih.1,
        quaternionBlockIndependent_polyAdd
          (quaternionBlockIndependent_polyMul (leftMoment_independent_right a b L f t hL hf)
            (rightMoment_independent_right b R g t)) ih.2⟩

#print axioms separated_pair
#print axioms weighted_term
#print axioms weighted_moment
#print axioms leftMoment_independent_left
#print axioms leftMoment_independent_right
#print axioms rightMoment_independent_left
#print axioms rightMoment_independent_right
#print axioms featureMoment_independent

end YMGap.Continuum.SU2QuaternionSeparableConditionalMoments
