/-
# Tangential integration by parts for the original quaternion Haar moments

The rotation derivative x_i partial_j - x_j partial_i has zero partial
Haar integral, coefficientwise in EVERY other link. Gaussian cancellation
passes through the common radial factor on each homogeneous polynomial;
termwise additivity then removes the homogeneity restriction.

The weighted identity retains the derivative of the complete supplied
action polynomial. It does not replace Haar by Gaussian measure, discard
interacting factors, estimate the derivative, or assert a spectral gap.
-/

import YMGap.Continuum.SU2QuaternionAngularDerivative
import YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

namespace YMGap.Continuum.SU2QuaternionHaarAngularIBP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative

local infix:50 " ≈ " => Q'.eqv

private def activeAngular (i j : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (polyMul (polyVar i) (activeDerivative j p))
    (polySmul (-1) (polyMul (polyVar j) (activeDerivative i p)))

private theorem activeAngular_coeff (i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (activeAngular i j p) (angularDerivative i j p) :=
  ((activeDerivative_coeff j p).mul_left (polyVar i)).add
    (((activeDerivative_coeff i p).mul_left (polyVar j)).smul (-1))

private theorem activeAngular_degree {i j d : Nat} (hi : i < 4) (hj : j < 4)
    {p : RatPoly} (hp : HasQuaternionBlockDegree 0 d p) (hd : 0 < d) :
    HasQuaternionBlockDegree 0 d (activeAngular i j p) := by
  have hv (k : Nat) (hk : k < 4) : HasQuaternionBlockDegree 0 1 (polyVar k) := by
    simpa only [Nat.mul_zero, Nat.zero_add, ite_true] using
      hasQuaternionBlockDegree_coordinate 0 k 0 hk
  exact HasQuaternionBlockDegree.relabel (by omega)
    (((hv i hi).mul (activeDerivative_degree hj hp)).add
      (((hv j hj).mul (activeDerivative_degree hi hp)).smul (-1)))

private theorem partialHaarHead_activeAngular_zero {i j d : Nat}
    (hi : i < 4) (hj : j < 4) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 d p) :
    RatPolyCoeffEqv (partialHaarHead (activeAngular i j p)) polyZero := by
  by_cases hd : d = 0
  · subst d
    rw [activeAngular, activeDerivative_zero hi p hp, activeDerivative_zero hj p hp]
    exact RatPolyCoeffEqv.refl _
  · have hdeg := activeAngular_degree hi hj hp (by omega)
    by_cases heven : d % 2 = 0
    · have hrad := partialHaarHead_mul_radial (d / 2) (activeAngular i j p)
        (HasQuaternionBlockDegree.relabel (by omega) hdeg)
      have hg := (partialGaussianHead_congr (activeAngular_coeff i j p)).trans
        (partialGaussianHead_angularDerivative_zero i j hi hj p)
      apply coeffEqv_of_positive_smul (radialDenominator_positive (d / 2))
      exact (hrad.trans hg).trans (RatPolyCoeffEqv.smul_zero _).symm
    · apply partialHaarHead_eq_zero_of_odd
      intro term ht
      have h := hdeg term ht
      change headQuaternionDegree term.1 % 2 = 1
      change exponentAt term.1 0 + exponentAt term.1 1 +
        exponentAt term.1 2 + exponentAt term.1 3 = d at h
      unfold headQuaternionDegree
      omega

private theorem partialHaarHead_angular_homogeneous {i j d : Nat}
    (hi : i < 4) (hj : j < 4) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 d p) :
    RatPolyCoeffEqv (partialHaarHead (angularDerivative i j p)) polyZero :=
  (partialHaarHead_congr (activeAngular_coeff i j p).symm).trans
    (partialHaarHead_activeAngular_zero hi hj p hp)

private theorem partialHaarHead_add (p q : RatPoly) :
    partialHaarHead (polyAdd p q) = polyAdd (partialHaarHead p) (partialHaarHead q) :=
  List.map_append

/-- All degrees and all retained tail coefficients: the tangential rotation
has zero integral under the ORIGINAL S^3 moment functional. -/
theorem partialHaarHead_angularDerivative_zero {i j : Nat}
    (hi : i < 4) (hj : j < 4) : ∀ p : RatPoly,
    RatPolyCoeffEqv (partialHaarHead (angularDerivative i j p)) polyZero
  | [] => RatPolyCoeffEqv.refl _
  | term :: rest => by
    have ht : HasQuaternionBlockDegree 0 (quaternionBlockDegree term.1 0) [term] := by
      intro t hm
      simp only [List.mem_singleton] at hm
      subst t
      rfl
    have hs := partialHaarHead_congr (angularDerivative_add i j [term] rest)
    rw [partialHaarHead_add] at hs
    exact hs.trans ((partialHaarHead_angular_homogeneous hi hj [term] ht).add
      (partialHaarHead_angularDerivative_zero hi hj rest))

private theorem haar_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: p => by simp only [quaternionHaar, ratWeightedSum, haar_weighted blocks p]

/-- Product Haar divergence cancellation, without any degree or support
restriction on the polynomial and without a positivity premise. -/
theorem quaternionHaar_angularDerivative_zero (tailBlocks : Nat) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (p : RatPoly) :
    quaternionHaar (tailBlocks + 1) (angularDerivative i j p) ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead tailBlocks _)) ?_
  rw [haar_weighted]
  exact partialHaarHead_angularDerivative_zero hi hj p (quaternionHaarMono tailBlocks)

/-- Exact weighted integration by parts. BOTH the weight derivative and
the test derivative remain; no independence or heat-weight bound is assumed. -/
theorem quaternionHaar_weighted_angular (tailBlocks : Nat) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (weight test : RatPoly) :
    quaternionHaar (tailBlocks + 1)
      (polyAdd (polyMul (angularDerivative i j weight) test)
        (polyMul weight (angularDerivative i j test))) ≈ 0 := by
  rw [haar_weighted]
  refine Q'.eqv_trans _ _ _
    ((angularDerivative_mul i j weight test).symm (quaternionHaarMono (tailBlocks + 1))) ?_
  rw [← haar_weighted]
  exact quaternionHaar_angularDerivative_zero tailBlocks hi hj (polyMul weight test)

/-- Head-independent factors have zero tangential derivative, with every
other coordinate retained. -/
theorem angularDerivative_independent_zero {i j : Nat} (hi : i < 4) (hj : j < 4)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 0 p) :
    RatPolyCoeffEqv (angularDerivative i j p) polyZero := by
  have h (k : Nat) (hk : k < 4) (l : Nat) :=
    ((ratDerivative_eq_zero_of_headDegree_zero k hk p hp).mul_left (polyVar l)).trans
      (RatPolyCoeffEqv.mul_zero_right _)
  exact ((h j hj i).add ((h i hi j).smul (-1))).trans
    (((RatPolyCoeffEqv.refl polyZero).add (RatPolyCoeffEqv.smul_zero (-1))).trans
      (RatPolyCoeffEqv.add_zero _))

/-- Only the link-dependent weight is differentiated. The complete
independent background remains INSIDE the integral, with no factorization
of the other links or comparison against a deleted-action measure. -/
theorem quaternionHaar_retained_background (tailBlocks : Nat) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (background weight test : RatPoly)
    (hbackground : HasQuaternionBlockDegree 0 0 background) :
    quaternionHaar (tailBlocks + 1)
      (polyMul background
        (polyAdd (polyMul (angularDerivative i j weight) test)
          (polyMul weight (angularDerivative i j test)))) ≈ 0 := by
  have he : RatPolyCoeffEqv
      (polyAdd (polyMul (angularDerivative i j background) (polyMul weight test))
        (polyMul background (angularDerivative i j (polyMul weight test))))
      (polyMul background
        (polyAdd (polyMul (angularDerivative i j weight) test)
          (polyMul weight (angularDerivative i j test)))) :=
    ((((angularDerivative_independent_zero hi hj background hbackground).mul_right _).trans
      (RatPolyCoeffEqv.mul_zero_left _)).add
        ((angularDerivative_mul i j weight test).mul_left background)).trans
      (RatPolyCoeffEqv.zero_add _)
  rw [haar_weighted]
  exact Q'.eqv_trans _ _ _ (he.symm (quaternionHaarMono (tailBlocks + 1)))
    (by rw [← haar_weighted]; exact quaternionHaar_weighted_angular tailBlocks hi hj background (polyMul weight test))

end YMGap.Continuum.SU2QuaternionHaarAngularIBP

#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBP.partialHaarHead_angularDerivative_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBP.quaternionHaar_angularDerivative_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBP.quaternionHaar_weighted_angular
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBP.angularDerivative_independent_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBP.quaternionHaar_retained_background
