/-
Finite explicit u/h monomial rows, where u=1-h.  Nonnegative refers to
the WEIGHTS of this row, not to the coefficients after expansion in h.
All data compute; the polynomial carrier and its equivalence are unchanged.
These rows are intended for ORIGINAL mixed-moment positivity, not for a
scalar-only replacement of the operator lift.
-/

import YMGap.Constructive.QPolyFinitePowerDifference
import YMGap.Constructive.QPolyCoefficientEvaluation

namespace YMGap.Constructive.QPolyUHRow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyFinitePowerDifference
open YMGap.Constructive.QPolyCoefficientEvaluation

structure Term where
  weight : Q'
  uDegree : Nat
  hDegree : Nat

abbrev Row := List Term

def monomial (a b : Nat) : Poly :=
  pmul (polynomialPower complement a) (polynomialPower coordinate b)

def polynomial : Row → Poly
  | [] => []
  | t :: r => padd (pscale t.weight (monomial t.uDegree t.hDegree)) (polynomial r)

def nonnegative : Row → Prop
  | [] => True
  | t :: r => (0 : Q') ≤ t.weight ∧ nonnegative r

def singleton (a b : Nat) : Row := [⟨1,a,b⟩]

def scale (c : Q') : Row → Row
  | [] => []
  | t :: r => ⟨c*t.weight,t.uDegree,t.hDegree⟩ :: scale c r

def shift (a b : Nat) : Row → Row
  | [] => []
  | t :: r => ⟨t.weight,a+t.uDegree,b+t.hDegree⟩ :: shift a b r

def multiply : Row → Row → Row
  | [], _ => []
  | t :: r, s => scale t.weight (shift t.uDegree t.hDegree s) ++ multiply r s

def power (r : Row) : Nat → Row
  | 0 => singleton 0 0
  | n+1 => multiply r (power r n)

private theorem add_zero_right (p : Poly) : CoeffEqv (padd p []) p := by
  intro i
  exact Q'.eqv_trans _ _ _ (coeff_padd i p []) (q_add_zero_eqv _)

theorem polynomial_singleton (a b : Nat) :
    CoeffEqv (polynomial (singleton a b)) (monomial a b) :=
  (add_zero_right _).trans (coeffEqv_pscale_one _)

theorem monomial_multiply (a b c d : Nat) :
    CoeffEqv (pmul (monomial a b) (monomial c d)) (monomial (a+c) (b+d)) := by
  let A := polynomialPower complement a
  let B := polynomialPower coordinate b
  let C := polynomialPower complement c
  let D := polynomialPower coordinate d
  have hinner : CoeffEqv (pmul B (pmul C D)) (pmul C (pmul B D)) :=
    (coeffEqv_pmul_assoc B C D).symm.trans
      (((coeffEqv_pmul_comm B C).pmul (CoeffEqv.refl D)).trans
        (coeffEqv_pmul_assoc C B D))
  exact (coeffEqv_pmul_assoc A B (pmul C D)).trans
    (((CoeffEqv.refl A).pmul hinner).trans
      ((coeffEqv_pmul_assoc A C (pmul B D)).symm.trans
        ((polynomialPower_add complement a c).pmul (polynomialPower_add coordinate b d))))

theorem polynomial_append (r s : Row) :
    CoeffEqv (polynomial (r ++ s)) (padd (polynomial r) (polynomial s)) := by
  induction r with
  | nil => exact CoeffEqv.refl _
  | cons t r ih =>
      exact (CoeffEqv.padd (CoeffEqv.refl _) ih).trans
        (coeffEqv_padd_assoc _ _ _).symm

theorem polynomial_scale (c : Q') (r : Row) :
    CoeffEqv (polynomial (scale c r)) (pscale c (polynomial r)) := by
  induction r with
  | nil => exact CoeffEqv.refl []
  | cons t r ih =>
      exact (CoeffEqv.padd (coeffEqv_pscale_comp c t.weight _).symm ih).trans
        (coeffEqv_pscale_padd c _ _).symm

theorem polynomial_shift (a b : Nat) (r : Row) :
    CoeffEqv (polynomial (shift a b r)) (pmul (monomial a b) (polynomial r)) := by
  induction r with
  | nil => exact (coeffEqv_pmul_comm _ []).symm
  | cons t r ih =>
      have ht : CoeffEqv (pscale t.weight (monomial (a+t.uDegree) (b+t.hDegree)))
          (pmul (monomial a b) (pscale t.weight (monomial t.uDegree t.hDegree))) :=
        ((monomial_multiply a b t.uDegree t.hDegree).symm.pscale t.weight).trans
          (coeffEqv_pmul_pscale t.weight _ _).symm
      exact (CoeffEqv.padd ht ih).trans (coeffEqv_pmul_padd_right _ _ _).symm

theorem polynomial_multiply (r s : Row) :
    CoeffEqv (polynomial (multiply r s)) (pmul (polynomial r) (polynomial s)) := by
  induction r with
  | nil => exact CoeffEqv.refl []
  | cons t r ih =>
      have ht : CoeffEqv (polynomial (scale t.weight (shift t.uDegree t.hDegree s)))
          (pmul (pscale t.weight (monomial t.uDegree t.hDegree)) (polynomial s)) :=
        (polynomial_scale _ _).trans
          (((polynomial_shift _ _ _).pscale _).trans
            (coeffEqv_pscale_pmul _ _ _).symm)
      exact (polynomial_append _ _).trans
        ((CoeffEqv.padd ht ih).trans (coeffEqv_padd_pmul_left _ _ _).symm)

theorem polynomial_power (r : Row) (n : Nat) :
    CoeffEqv (polynomial (power r n)) (polynomialPower (polynomial r) n) := by
  induction n with
  | zero =>
      exact (polynomial_singleton 0 0).trans (coeffEqv_pmul_one_left [1])
  | succ n ih =>
      exact (polynomial_multiply r (power r n)).trans
        ((CoeffEqv.refl _).pmul ih)

theorem nonnegative_singleton (a b : Nat) : nonnegative (singleton a b) :=
  ⟨(by decide : (0 : Q') ≤ 1), True.intro⟩

theorem nonnegative_append (r s : Row) (hr : nonnegative r) (hs : nonnegative s) :
    nonnegative (r ++ s) := by
  induction r with
  | nil => exact hs
  | cons t r ih => exact ⟨hr.1, ih hr.2⟩

theorem nonnegative_scale (c : Q') (hc : (0 : Q') ≤ c) (r : Row)
    (hr : nonnegative r) : nonnegative (scale c r) := by
  induction r with
  | nil => exact True.intro
  | cons t r ih => exact ⟨Q'.mul_nonneg _ _ hc hr.1, ih hr.2⟩

theorem nonnegative_shift (a b : Nat) (r : Row) (hr : nonnegative r) :
    nonnegative (shift a b r) := by
  induction r with
  | nil => exact True.intro
  | cons t r ih => exact ⟨hr.1, ih hr.2⟩

theorem nonnegative_multiply (r s : Row) (hr : nonnegative r) (hs : nonnegative s) :
    nonnegative (multiply r s) := by
  induction r with
  | nil => exact True.intro
  | cons t r ih =>
      exact nonnegative_append _ _
        (nonnegative_scale _ hr.1 _ (nonnegative_shift _ _ _ hs)) (ih hr.2)

theorem nonnegative_power (r : Row) (hr : nonnegative r) (n : Nat) :
    nonnegative (power r n) := by
  induction n with
  | zero => exact nonnegative_singleton 0 0
  | succ n ih => exact nonnegative_multiply r (power r n) hr ih

#print axioms Term
#print axioms polynomial
#print axioms multiply
#print axioms power
#print axioms monomial_multiply
#print axioms polynomial_singleton
#print axioms polynomial_append
#print axioms polynomial_scale
#print axioms polynomial_shift
#print axioms polynomial_multiply
#print axioms polynomial_power
#print axioms nonnegative_singleton
#print axioms nonnegative_append
#print axioms nonnegative_scale
#print axioms nonnegative_shift
#print axioms nonnegative_multiply
#print axioms nonnegative_power

end YMGap.Constructive.QPolyUHRow
