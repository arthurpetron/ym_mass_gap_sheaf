/-
# Coefficient-level substitution into the original multivariate carrier

The existing division-free root-count theorem reflects a univariate
identity known on x>=-1 to coefficient equality. Horner substitution then
preserves that equality, addition, scaling, multiplication, composition
and the actual Chebyshev character recurrence. The result is RatPolyCoeffEqv,
not merely equality at rational environments, and is usable under arbitrary
Haar insertions. No multivariate extensionality principle is assumed.
-/

import YMGap.Continuum.QPolyHaarPositiveSubstitution
import YMGap.Continuum.SU2ClassPolynomialChebUniqueness

namespace YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialExtensionalReflection
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QPolyHaarPositiveSubstitution

local infix:50 " ≈ " => Q'.eqv

/-- A finite polynomial identity on the rational half-line is an identity
of coefficient lists. Only a computed finite positive integer grid is used. -/
theorem polyEqv_of_ge_neg_one {p q : Poly}
    (h : ∀ x : Q', (-(1 : Q')) ≤ x → eval p x ≈ eval q x) : PolyEqv p q := by
  have hz : ∀ x, eval (psub p q) x ≈ 0 :=
    roots_zero (positiveGrid (psub p q).length) (positiveGrid_distinct _) _
      (by rw [positiveGrid_length]; exact Nat.le_refl _) (by
        intro y hy
        obtain ⟨k, _, _, rfl⟩ := positiveGrid_member hy
        have hk : (-(1 : Q')) ≤ Q'.ofNat k := by
          change (-1 : Int) * 1 ≤ (k : Int) * 1
          omega
        exact Q'.eqv_trans _ _ _ (eval_psub p q _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (h _ hk))
            (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.neg_add_self_eqv _))))
  intro x
  exact q_eqv_of_sub_zero (Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_psub p q x)) (hz x))

theorem subst_arg {x y : RatPoly} (h : RatPolyCoeffEqv x y) : ∀ p : Poly,
    RatPolyCoeffEqv (subst x p) (subst y p)
  | [] => RatPolyCoeffEqv.refl _
  | c :: p => (RatPolyCoeffEqv.refl (polySmul c polyOne)).add (h.mul (subst_arg h p))

theorem subst_singleton (x : RatPoly) (c : Q') :
    RatPolyCoeffEqv (subst x [c]) (polySmul c polyOne) :=
  ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.mul_zero_right x)).trans (RatPolyCoeffEqv.add_zero _)

private theorem zero_horner (x : RatPoly) : RatPolyCoeffEqv polyZero
    (polyAdd (polySmul 0 polyOne) (polyMul x polyZero)) :=
  (((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.mul_zero_right x)).trans
    (RatPolyCoeffEqv.zero_add polyZero)).symm

/-- Reflective coefficient equality survives actual multivariate substitution,
including unequal lengths and unnormalized trailing zero coefficients. -/
theorem subst_coeffEqv (x : RatPoly) : ∀ p q : Poly, CoeffEqv p q →
    RatPolyCoeffEqv (subst x p) (subst x q)
  | [], [], _ => RatPolyCoeffEqv.refl _
  | [], d :: ds, h => (zero_horner x).trans
      ((RatPolyCoeffEqv.smul_coefficient (headCoeff_congr h) polyOne).add
        ((subst_coeffEqv x [] ds (coeffEqv_tail h)).mul_left x))
  | c :: cs, [], h =>
      ((RatPolyCoeffEqv.smul_coefficient (headCoeff_congr h) polyOne).add
        ((subst_coeffEqv x cs [] (coeffEqv_tail h)).mul_left x)).trans (zero_horner x).symm
  | c :: cs, d :: ds, h =>
      (RatPolyCoeffEqv.smul_coefficient (headCoeff_congr h) polyOne).add
        ((subst_coeffEqv x cs ds (coeffEqv_tail h)).mul_left x)

theorem subst_polyEqv (x : RatPoly) {p q : Poly} (h : PolyEqv p q) :
    RatPolyCoeffEqv (subst x p) (subst x q) :=
  subst_coeffEqv x p q (allZero_psub_of_polyEqv h)

theorem subst_pscale (x : RatPoly) (k : Q') : ∀ p : Poly,
    RatPolyCoeffEqv (subst x (pscale k p)) (polySmul k (subst x p))
  | [] => (RatPolyCoeffEqv.smul_zero k).symm
  | c :: p =>
      ((RatPolyCoeffEqv.smul_assoc k c polyOne).symm.add
        (((subst_pscale x k p).mul_left x).trans (RatPolyCoeffEqv.polyMul_smul_right k x _))).trans
        (RatPolyCoeffEqv.smul_add k _ _).symm

theorem subst_padd (x : RatPoly) : ∀ p q : Poly,
    RatPolyCoeffEqv (subst x (padd p q)) (polyAdd (subst x p) (subst x q))
  | [], _ => (RatPolyCoeffEqv.zero_add _).symm
  | _ :: _, [] => (RatPolyCoeffEqv.add_zero _).symm
  | a :: p, b :: q =>
      ((RatPolyCoeffEqv.add_smul_same a b polyOne).symm.add
        (((subst_padd x p q).mul_left x).trans (RatPolyCoeffEqv.mul_add_right x _ _))).trans
        (RatPolyCoeffEqv.four_add_swap _ _ _ _)

theorem subst_zero_cons (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (subst x (0 :: p)) (polyMul x (subst x p)) :=
  ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)

theorem subst_pmul (x : RatPoly) : ∀ p q : Poly,
    RatPolyCoeffEqv (subst x (pmul p q)) (polyMul (subst x p) (subst x q))
  | [], _ => (RatPolyCoeffEqv.mul_zero_left _).symm
  | a :: p, q => by
      have h := (subst_padd x (pscale a q) (0 :: pmul p q)).trans
        ((subst_pscale x a q).add
          ((subst_zero_cons x (pmul p q)).trans ((subst_pmul x p q).mul_left x)))
      apply h.trans
      change RatPolyCoeffEqv _ (polyMul (polyAdd (polySmul a polyOne) (polyMul x (subst x p))) (subst x q))
      rw [polyMul_add_left_exact]
      exact (((RatPolyCoeffEqv.polyMul_smul_left a polyOne _).trans
        ((RatPolyCoeffEqv.one_mul _).smul a)).symm).add (RatPolyCoeffEqv.mul_assoc _ _ _).symm

/-- Finite Horner composition; inner polynomial first. -/
def compose (inner : Poly) : Poly → Poly
  | [] => []
  | c :: p => padd [c] (pmul inner (compose inner p))

theorem eval_compose (inner : Poly) (x : Q') : ∀ outer : Poly,
    eval (compose inner outer) x ≈ eval outer (eval inner x)
  | [] => Q'.eqv_refl 0
  | c :: p => Q'.eqv_trans _ _ _ (eval_padd _ _ x)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) (q_add_zero_eqv c))
        (Q'.eqv_trans _ _ _ (eval_pmul _ _ x) (Q'.mul_eqv_congr_left _ _ _ (eval_compose inner x p))))

theorem subst_compose (x : RatPoly) (inner : Poly) : ∀ outer : Poly,
    RatPolyCoeffEqv (subst x (compose inner outer)) (subst (subst x inner) outer)
  | [] => RatPolyCoeffEqv.refl _
  | c :: p => (subst_padd x [c] _).trans
      ((subst_singleton x c).add ((subst_pmul x inner _).trans
        ((subst_compose x inner p).mul_left (subst x inner))))

theorem subst_one_add (x : RatPoly) :
    RatPolyCoeffEqv (subst x [1, 1]) (polyAdd polyOne x) :=
  (RatPolyCoeffEqv.one_smul polyOne).add
    ((((subst_singleton x 1).trans (RatPolyCoeffEqv.one_smul polyOne)).mul_left x).trans
      (RatPolyCoeffEqv.mul_one x))

theorem subst_chi1 (x : RatPoly) : RatPolyCoeffEqv (subst x chi1) (polySmul 2 x) :=
  (subst_zero_cons x [2]).trans
    (((subst_singleton x 2).mul_left x).trans
      ((RatPolyCoeffEqv.polyMul_smul_right 2 x polyOne).trans ((RatPolyCoeffEqv.mul_one x).smul 2)))

/-- Exact original multivariate character recurrence, all labels. -/
theorem subst_chebPoly (x : RatPoly) : ∀ n : Nat,
    RatPolyCoeffEqv (subst x (chebPoly n)) (characterPolynomial x n)
  | 0 => (subst_singleton x 1).trans (RatPolyCoeffEqv.one_smul polyOne)
  | 1 => subst_chi1 x
  | n + 2 => (subst_padd x _ _).trans
      (((subst_pmul x chi1 _).trans ((subst_chi1 x).mul (subst_chebPoly x (n + 1)))).add
        ((subst_pscale x (-1) _).trans ((subst_chebPoly x n).smul (-1))))

end YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.polyEqv_of_ge_neg_one
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_arg
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_singleton
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_coeffEqv
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_polyEqv
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_pscale
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_padd
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_zero_cons
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_pmul
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.compose
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.eval_compose
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_compose
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_one_add
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_chi1
#print axioms YMGap.Continuum.QPolyRatPolySubstitutionAlgebra.subst_chebPoly
