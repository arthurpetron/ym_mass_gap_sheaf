/-
# Polynomial-valued Gaussian integration by parts in the head quaternion

Integrate only the four head coordinates, retaining EVERY tail coefficient.
The exact scalar moment recurrence gives E[u_i P] = E[partial_i P]
coefficientwise for arbitrary polynomial P and i < 4, without degree bounds.
This supplies the recurrence input for all-degree quaternion translation;
it does not assert translation invariance or reflected slab positivity.
-/

import YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
import YMGap.Continuum.SU2QuaternionRatPolyDifferential

namespace YMGap.Continuum.SU2QuaternionHeadGaussianIBP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer

local infix:50 " ≈ " => Q'.eqv

/-- Exact partial Gaussian integral on the ORIGINAL rational polynomial
carrier; the four head exponents are removed and all tail exponents retained. -/
def partialGaussianHead (p : RatPoly) : RatPoly :=
  p.map fun term => (term.1.drop 4, term.2 * headGaussianMoment term.1)

/-- An arbitrary tail coefficient probe, preceded by the exact head moment. -/
def gaussianHeadProbe (weight : List Nat → Q') (m : List Nat) : Q' :=
  headGaussianMoment m * weight (m.drop 4)

theorem partialGaussianHead_probe (weight : List Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum weight (partialGaussianHead p) ≈ ratWeightedSum (gaussianHeadProbe weight) p
  | [] => Q'.eqv_refl _
  | _ :: rest => Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (partialGaussianHead_probe weight rest)

/-- Coefficient equality, not merely pointwise evaluation, passes through
the partial integral. No tail variable is specialized. -/
theorem partialGaussianHead_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (partialGaussianHead p) (partialGaussianHead q) := fun weight =>
  Q'.eqv_trans _ _ _ (partialGaussianHead_probe weight p)
    (Q'.eqv_trans _ _ _ (h (gaussianHeadProbe weight)) (Q'.eqv_symm (partialGaussianHead_probe weight q)))

private theorem gaussian_ibp0 (a b c d : Nat) :
    gaussianMoment4 (a + 1) b c d ≈ Q'.ofNat a * gaussianMoment4 (a - 1) b c d := by
  cases a with
  | zero =>
    have h : gaussianMoment4 1 b c d = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ a => exact gaussianMoment4_shift0 a b c d

private theorem gaussian_ibp1 (a b c d : Nat) :
    gaussianMoment4 a (b + 1) c d ≈ Q'.ofNat b * gaussianMoment4 a (b - 1) c d := by
  cases b with
  | zero =>
    have h : gaussianMoment4 a 1 c d = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ b => exact gaussianMoment4_shift1 a b c d

private theorem gaussian_ibp2 (a b c d : Nat) :
    gaussianMoment4 a b (c + 1) d ≈ Q'.ofNat c * gaussianMoment4 a b (c - 1) d := by
  cases c with
  | zero =>
    have h : gaussianMoment4 a b 1 d = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ c => exact gaussianMoment4_shift2 a b c d

private theorem gaussian_ibp3 (a b c d : Nat) :
    gaussianMoment4 a b c (d + 1) ≈ Q'.ofNat d * gaussianMoment4 a b c (d - 1) := by
  cases d with
  | zero =>
    have h : gaussianMoment4 a b c 1 = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ d => exact gaussianMoment4_shift3 a b c d

private theorem mul_tail {x a y : Q'} (h : x ≈ a * y) (tail : Q') :
    x * tail ≈ a * (y * tail) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_assoc_eqv _ _ _)

/-- Monomial integration by parts, with an arbitrary untouched tail probe.
Short exponent lists are included; there is no support or padding premise. -/
theorem gaussianHeadProbe_ibp (weight : List Nat → Q') (i : Nat) (hi : i < 4) (m : List Nat) :
    gaussianHeadProbe weight (monoMul (varMono i) m) ≈
      derivativeProbe i (gaussianHeadProbe weight) m := by
  have h0 := mul_tail (gaussian_ibp0 (exponentAt m 0) (exponentAt m 1) (exponentAt m 2) (exponentAt m 3)) (weight (m.drop 4))
  have h1 := mul_tail (gaussian_ibp1 (exponentAt m 0) (exponentAt m 1) (exponentAt m 2) (exponentAt m 3)) (weight (m.drop 4))
  have h2 := mul_tail (gaussian_ibp2 (exponentAt m 0) (exponentAt m 1) (exponentAt m 2) (exponentAt m 3)) (weight (m.drop 4))
  have h3 := mul_tail (gaussian_ibp3 (exponentAt m 0) (exponentAt m 1) (exponentAt m 2) (exponentAt m 3)) (weight (m.drop 4))
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases_i with rfl | rfl | rfl | rfl
  all_goals try (rcases m with _ | ⟨a, m⟩)
  all_goals try (rcases m with _ | ⟨b, m⟩)
  all_goals try (rcases m with _ | ⟨c, m⟩)
  all_goals try (rcases m with _ | ⟨d, tail⟩)
  all_goals
    simp [gaussianHeadProbe, headGaussianMoment, derivativeProbe, varMono,
      monoMul, lowerExponentAt, exponentAt, Nat.add_comm,
      List.getElem?_cons_zero] at h0 h1 h2 h3 ⊢
    first | exact h0 | exact h1 | exact h2 | exact h3

private theorem weighted_var (weight : List Nat → Q') (i : Nat) : ∀ p : RatPoly,
    ratWeightedSum weight (polyMul (polyVar i) p) ≈
      ratWeightedSum (fun m => weight (monoMul (varMono i) m)) p
  | [] => Q'.eqv_refl _
  | term :: rest => by
    have ih := weighted_var weight i rest
    rcases term with ⟨m, c⟩
    simp only [polyMul, polyVar, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons]
    simp only [polyMul, polyVar, List.flatMap_cons, List.flatMap_nil, List.append_nil] at ih
    exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv c)) ih

private theorem weighted_congr (w v : List Nat → Q') (h : ∀ m, w m ≈ v m) :
    ∀ p : RatPoly, ratWeightedSum w p ≈ ratWeightedSum v p
  | [] => Q'.eqv_refl _
  | term :: rest => Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (h term.1)) (weighted_congr w v h rest)

/-- All-degree, coefficient-retaining Gaussian integration by parts on the
original multivariate polynomial carrier. This is not a finite-degree check. -/
theorem partialGaussianHead_ibp (i : Nat) (hi : i < 4) (p : RatPoly) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul (polyVar i) p))
      (partialGaussianHead (ratDerivative i p)) := by
  intro weight
  refine Q'.eqv_trans _ _ _ (partialGaussianHead_probe weight _) ?_
  refine Q'.eqv_trans _ _ _ (weighted_var (gaussianHeadProbe weight) i p) ?_
  refine Q'.eqv_trans _ _ _ (weighted_congr _ _ (gaussianHeadProbe_ibp weight i hi) p) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (ratWeightedSum_derivative i (gaussianHeadProbe weight) p))
    (Q'.eqv_symm (partialGaussianHead_probe weight _))

theorem partialGaussianHead_add (p q : RatPoly) :
    partialGaussianHead (polyAdd p q) = polyAdd (partialGaussianHead p) (partialGaussianHead q) :=
  List.map_append

private theorem partial_four (a b c d : RatPoly) :
    partialGaussianHead (polyFour a b c d) =
      polyFour (partialGaussianHead a) (partialGaussianHead b) (partialGaussianHead c) (partialGaussianHead d) := by
  simp only [polyFour, partialGaussianHead_add]

private theorem partial_four_congr {a b : Nat → RatPoly}
    (h0 : RatPolyCoeffEqv (partialGaussianHead (a 0)) (partialGaussianHead (b 0)))
    (h1 : RatPolyCoeffEqv (partialGaussianHead (a 1)) (partialGaussianHead (b 1)))
    (h2 : RatPolyCoeffEqv (partialGaussianHead (a 2)) (partialGaussianHead (b 2)))
    (h3 : RatPolyCoeffEqv (partialGaussianHead (a 3)) (partialGaussianHead (b 3))) :
    RatPolyCoeffEqv (partialGaussianHead (polyFour (a 0) (a 1) (a 2) (a 3)))
      (partialGaussianHead (polyFour (b 0) (b 1) (b 2) (b 3))) := by
  rw [partial_four, partial_four]
  exact h0.add (h1.add (h2.add h3))

private theorem four_mul_right (a b c d p : RatPoly) :
    polyMul (polyFour a b c d) p =
      polyFour (polyMul a p) (polyMul b p) (polyMul c p) (polyMul d p) := by
  simp only [polyFour, polyMul_add_left_exact]

/-- Gaussian Euler/gradient identity with EVERY tail coefficient retained:
E[(Euler L) P] = E[(Delta L) P + grad L . grad P]. -/
theorem partialGaussianHead_euler_product (l p : RatPoly) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul (headEuler l) p))
      (partialGaussianHead (polyAdd (polyMul (headLaplacian l) p) (headGradientDot l p))) := by
  let a := fun i => polyMul (ratDerivative i (ratDerivative i l)) p
  let b := fun i => polyMul (ratDerivative i l) (ratDerivative i p)
  let input := fun i => polyMul (polyMul (polyVar i) (ratDerivative i l)) p
  have row (i : Nat) (hi : i < 4) :
      RatPolyCoeffEqv (partialGaussianHead (input i)) (partialGaussianHead (polyAdd (a i) (b i))) :=
    (partialGaussianHead_congr (RatPolyCoeffEqv.mul_assoc (polyVar i) (ratDerivative i l) p)).trans
      ((partialGaussianHead_ibp i hi (polyMul (ratDerivative i l) p)).trans
        (partialGaussianHead_congr (ratDerivative_mul i (ratDerivative i l) p)))
  have hrows := partial_four_congr (a := input) (b := fun i => polyAdd (a i) (b i))
    (row 0 (by decide)) (row 1 (by decide)) (row 2 (by decide)) (row 3 (by decide))
  have hgroup := partialGaussianHead_congr (polyFour_add (a 0) (a 1) (a 2) (a 3) (b 0) (b 1) (b 2) (b 3))
  have hcollect : RatPolyCoeffEqv (polyFour (a 0) (a 1) (a 2) (a 3)) (polyMul (headLaplacian l) p) := by
    change RatPolyCoeffEqv _ (polyMul (polyFour _ _ _ _) p)
    rw [four_mul_right]
    exact RatPolyCoeffEqv.refl _
  have h := hrows.trans (hgroup.trans (partialGaussianHead_congr (hcollect.add (RatPolyCoeffEqv.refl _))))
  change RatPolyCoeffEqv (partialGaussianHead (polyMul (polyFour _ _ _ _) p)) _
  rw [four_mul_right]
  exact h

/-- A head-linear harmonic polynomial is a Gaussian directional derivative.
The two conditions are explicit coefficient identities, not moment premises. -/
theorem partialGaussianHead_linear_stein (l p : RatPoly)
    (heuler : RatPolyCoeffEqv (headEuler l) l)
    (hlaplacian : RatPolyCoeffEqv (headLaplacian l) polyZero) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul l p))
      (partialGaussianHead (headGradientDot l p)) := by
  refine (partialGaussianHead_congr (heuler.symm.mul_right p)).trans ?_
  refine (partialGaussianHead_euler_product l p).trans ?_
  apply partialGaussianHead_congr
  exact ((((hlaplacian.mul_right p).trans (RatPolyCoeffEqv.mul_zero_left p)).add
    (RatPolyCoeffEqv.refl (headGradientDot l p))).trans (RatPolyCoeffEqv.zero_add _))

end YMGap.Continuum.SU2QuaternionHeadGaussianIBP

#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.partialGaussianHead
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.gaussianHeadProbe
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.partialGaussianHead_probe
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.partialGaussianHead_congr
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.gaussianHeadProbe_ibp
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.partialGaussianHead_ibp
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.partialGaussianHead_add
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.partialGaussianHead_euler_product
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianIBP.partialGaussianHead_linear_stein
