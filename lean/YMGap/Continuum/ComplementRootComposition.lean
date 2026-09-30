/-
Coefficient-positive finite composition of the complement-root polynomials.
The nested rows are algebraic coefficient lists, not a limiting operator.
-/

import YMGap.Continuum.ComplementRootPolynomial
import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

namespace YMGap.Continuum.ComplementRootComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Constructive.CRealArtanhEulerPositiveCompanion
open YMGap.Constructive.CRealArtanhEulerPositiveCompanionBound
open YMGap.Continuum.ComplementRootPolynomial
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

/-- Horner composition preserves nonnegative padded coefficients. -/
theorem compose_coeffNonnegative (inner outer : Poly)
    (hi : CoeffNonnegative inner) (ho : CoeffNonnegative outer) :
    CoeffNonnegative (compose inner outer) := by
  revert ho
  induction outer with
  | nil =>
      intro _
      exact coeffNonnegative_empty
  | cons c outer ih =>
      intro ho
      change CoeffNonnegative
        (padd (pconst c) (pmul inner (compose inner outer)))
      exact coeffNonnegative_padd
        (coeffNonnegative_pconst (ho 0))
        (coeffNonnegative_pmul hi
          (ih (fun index => ho (index + 1))))

private theorem singleton_coeffLe {a b : Q'} (hab : a ≤ b) :
    CoeffLe (pconst a) (pconst b) := by
  intro index
  cases index with
  | zero => exact hab
  | succ index => exact Q'.le_refl' 0

private theorem singleton_le_empty {a : Q'} (ha : a ≤ (0 : Q')) :
    CoeffLe (pconst a) [] := by
  intro index
  cases index with
  | zero => exact ha
  | succ index => exact Q'.le_refl' 0

private theorem coeffLe_congr_right {p q r : Poly}
    (hpq : CoeffLe p q) (hqr : CoeffEqv q r) : CoeffLe p r :=
  fun index => Q'.le_trans' _ _ _ (hpq index) (Q'.le_of_eqv (hqr index))

/-- Simultaneously increasing the inner and outer coefficient lists can only
increase the composed coefficients, provided both lists have nonnegative
coefficients. This includes unequal outer lengths and padded zeros. -/
theorem compose_coeffLe {a b p q : Poly}
    (hab : CoeffLe a b) (hpq : CoeffLe p q)
    (ha : CoeffNonnegative a) (hb : CoeffNonnegative b)
    (hp : CoeffNonnegative p) (hq : CoeffNonnegative q) :
    CoeffLe (compose a p) (compose b q) := by
  revert hpq hp hq
  induction p generalizing q with
  | nil =>
      intro _ _ hq
      intro index
      exact compose_coeffNonnegative b q hb hq index
  | cons c p ih =>
      intro hpq hp hq
      cases q with
      | nil =>
          have htail : CoeffLe p ([] : Poly) :=
            fun index => hpq (index + 1)
          have hptail : CoeffNonnegative p :=
            fun index => hp (index + 1)
          have hmul : CoeffLe (pmul a (compose a p))
              (pmul b (compose b ([] : Poly))) :=
            coeffLe_pmul hab
              (ih htail hptail coeffNonnegative_empty)
              (compose_coeffNonnegative a p ha hptail) hb
          change CoeffLe
            (padd (pconst c) (pmul a (compose a p))) []
          have hraw := coeffLe_padd (singleton_le_empty (hpq 0)) hmul
          change CoeffLe
            (padd (pconst c) (pmul a (compose a p))) (pmul b []) at hraw
          have hz : CoeffEqv (pmul b []) [] := by
            simpa only [pmul] using (coeffEqv_pmul_comm b [])
          exact coeffLe_congr_right hraw hz
      | cons d q =>
          have htail : CoeffLe p q :=
            fun index => hpq (index + 1)
          have hptail : CoeffNonnegative p :=
            fun index => hp (index + 1)
          have hqtail : CoeffNonnegative q :=
            fun index => hq (index + 1)
          have hmul : CoeffLe (pmul a (compose a p))
              (pmul b (compose b q)) :=
            coeffLe_pmul hab (ih htail hptail hqtail)
              (compose_coeffNonnegative a p ha hptail) hb
          change CoeffLe
            (padd (pconst c) (pmul a (compose a p)))
            (padd (pconst d) (pmul b (compose b q)))
          exact coeffLe_padd (singleton_coeffLe (hpq 0)) hmul

/-- A fixed number of nested finite root rows, starting at the defect
variable; the second index is the common polynomial recursion depth. -/
def nested : Nat → Nat → Poly
  | 0, _ => pvar
  | k + 1, n => compose (nested k n) (polynomial n)

theorem nested_coeffNonnegative (k n : Nat) :
    CoeffNonnegative (nested k n) := by
  induction k with
  | zero => exact pvar_coeffNonnegative
  | succ k ih =>
      exact compose_coeffNonnegative _ _ ih (polynomial_coeffNonnegative n)

theorem nested_coeffLe (k : Nat) {m n : Nat} (hmn : m ≤ n) :
    CoeffLe (nested k m) (nested k n) := by
  induction k with
  | zero => exact coeffLe_refl pvar
  | succ k ih =>
      exact compose_coeffLe ih (polynomial_coeffLe hmn)
        (nested_coeffNonnegative k m) (nested_coeffNonnegative k n)
        (polynomial_coeffNonnegative m) (polynomial_coeffNonnegative n)

/-- Every ordered pair of nested rows has a coefficient-positive difference. -/
theorem nested_difference_nonnegative (k : Nat) {m n : Nat} (hmn : m ≤ n) :
    CoeffNonnegative (psub (nested k n) (nested k m)) := by
  intro index
  have hcoeff := nested_coeffLe k hmn index
  have hneg :
      ((-1 : Q') * coeff (nested k m) index).eqv
        (-(coeff (nested k m) index)) := by
    exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
  have hsub :
      (coeff (psub (nested k n) (nested k m)) index).eqv
        (coeff (nested k n) index - coeff (nested k m) index) := by
    exact Q'.eqv_trans _ _ _ (coeff_psub _ _ _)
      (Q'.add_eqv_congr_left _ _ _ hneg)
  exact Q'.le_trans' _
      (coeff (nested k n) index - coeff (nested k m) index) _
      (Q'.sub_nonneg_of_le hcoeff)
      (Q'.ge_of_eqv hsub)

#print axioms compose_coeffNonnegative
#print axioms compose_coeffLe
#print axioms nested
#print axioms nested_coeffNonnegative
#print axioms nested_coeffLe
#print axioms nested_difference_nonnegative

end YMGap.Continuum.ComplementRootComposition
