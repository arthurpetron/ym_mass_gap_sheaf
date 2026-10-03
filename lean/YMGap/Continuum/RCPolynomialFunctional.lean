/-
A finite coefficient-list functional with values in the EXISTING constructive
real quotient.  It respects actual padded rational coefficient equivalence.
The sequence g is arbitrary: this module introduces no vector carrier or time
action.  Its consumer substitutes the original dyadic root/defect moments.
-/

import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.FCLimitContinuity
import YMGap.Constructive.QPolyFormalDerivative

namespace YMGap.Continuum.RCPolynomialFunctional

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative

/-- Scalar quotient algebra: no state or operator is introduced. -/
theorem rc_add_zero (x : RC) : RCadd x RCzero = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_add_zero_eqv (X.approx n)))

theorem rc_zero_add (x : RC) : RCadd RCzero x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_zero_add_eqv (X.approx n)))

theorem rc_scale_zero (x : RC) : RCscale 0 x = RCzero := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_zero_mul (X.approx n)))

theorem rc_scale_congr {a b : Q'} (h : a.eqv b) (x : RC) :
    RCscale a x = RCscale b x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_eqv_congr_right a b (X.approx n) h))

theorem rc_scale_coeff_add (a b : Q') (x : RC) :
    RCscale (a + b) x = RCadd (RCscale a x) (RCscale b x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_add_mul a b (X.approx n)))

theorem rc_add_interchange (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d) = RCadd (RCadd a c) (RCadd b d) := by
  refine Quotient.inductionOn a ?_
  intro A
  refine Quotient.inductionOn b ?_
  intro B
  refine Quotient.inductionOn c ?_
  intro C
  refine Quotient.inductionOn d ?_
  intro D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => q_interchange (A.approx n) (B.approx n) (C.approx n) (D.approx n)))

private theorem scale_neg_one (x : RC) : RCscale (-1) x = RCneg x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (X.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (X.approx n)))))

/-- The actual finite coefficient functional, starting at moment index i. -/
def formFrom (g : Nat → RC) : Poly → Nat → RC
  | [], _ => RCzero
  | a :: p, i => RCadd (RCscale a (g i)) (formFrom g p (i + 1))

private theorem formFrom_zero_coeff (g : Nat → RC) :
    forall (p : Poly), CoeffEqv p [] → forall i : Nat, formFrom g p i = RCzero
  | [], _, _ => rfl
  | a :: p, hc, i => by
      have ha : a.eqv 0 := hc 0
      have htail : CoeffEqv p [] := fun j => hc (j + 1)
      change RCadd (RCscale a (g i)) (formFrom g p (i + 1)) = RCzero
      rw [rc_scale_congr ha, rc_scale_zero,
        formFrom_zero_coeff g p htail (i + 1), rc_zero_add]

/-- Arbitrary zero padding and rational coefficient representatives do not
change the finite functional. -/
theorem formFrom_coeffEqv (g : Nat → RC) :
    forall {p q : Poly}, CoeffEqv p q → forall i : Nat,
      formFrom g p i = formFrom g q i
  | [], [], _, _ => rfl
  | [], b :: q, hc, i =>
      (formFrom_zero_coeff g (b :: q) hc.symm i).symm
  | a :: p, [], hc, i =>
      formFrom_zero_coeff g (a :: p) hc i
  | a :: p, b :: q, hc, i => by
      have hab : a.eqv b := hc 0
      have htail : CoeffEqv p q := fun j => hc (j + 1)
      exact (congrArg (fun z => RCadd z (formFrom g p (i + 1)))
        (rc_scale_congr hab (g i))).trans
        (congrArg (RCadd (RCscale b (g i))) (formFrom_coeffEqv g htail (i + 1)))

/-- Polynomial addition maps to quotient addition. -/
theorem formFrom_padd (g : Nat → RC) (p q : Poly) (i : Nat) :
    formFrom g (padd p q) i = RCadd (formFrom g p i) (formFrom g q i) := by
  induction p generalizing q i with
  | nil =>
      exact (rc_zero_add _).symm
  | cons a p ih =>
      cases q with
      | nil =>
          exact (rc_add_zero _).symm
      | cons b q =>
          change RCadd (RCscale (a + b) (g i)) (formFrom g (padd p q) (i + 1)) =
            RCadd (RCadd (RCscale a (g i)) (formFrom g p (i + 1)))
              (RCadd (RCscale b (g i)) (formFrom g q (i + 1)))
          rw [rc_scale_coeff_add, ih]
          exact rc_add_interchange _ _ _ _

/-- Rational polynomial scaling maps to the SAME quotient scalar action. -/
theorem formFrom_pscale (g : Nat → RC) (c : Q') (p : Poly) (i : Nat) :
    formFrom g (pscale c p) i = RCscale c (formFrom g p i) := by
  induction p generalizing i with
  | nil =>
      exact (RCscale_RCzero c).symm
  | cons a p ih =>
      change RCadd (RCscale (c * a) (g i)) (formFrom g (pscale c p) (i + 1)) =
        RCscale c (RCadd (RCscale a (g i)) (formFrom g p (i + 1)))
      rw [ih, ← RCscale_RCscale, ← RCscale_RCadd]

theorem formFrom_pneg (g : Nat → RC) (p : Poly) (i : Nat) :
    formFrom g (pneg p) i = RCneg (formFrom g p i) :=
  (formFrom_pscale g (-1) p i).trans (scale_neg_one _)

theorem formFrom_psub (g : Nat → RC) (p q : Poly) (i : Nat) :
    formFrom g (psub p q) i = RCsub (formFrom g p i) (formFrom g q i) := by
  unfold psub RCsub
  rw [formFrom_padd, formFrom_pneg]

/-- A prepended zero shifts the actual moment index, without changing g. -/
theorem formFrom_zeroCons (g : Nat → RC) (p : Poly) (i : Nat) :
    formFrom g (0 :: p) i = formFrom g p (i + 1) := by
  change RCadd (RCscale 0 (g i)) (formFrom g p (i + 1)) = _
  rw [rc_scale_zero, rc_zero_add]

theorem formFrom_singleton (g : Nat → RC) (a : Q') (i : Nat) :
    formFrom g [a] i = RCscale a (g i) :=
  rc_add_zero _

end YMGap.Continuum.RCPolynomialFunctional

#print axioms YMGap.Continuum.RCPolynomialFunctional.rc_add_zero
#print axioms YMGap.Continuum.RCPolynomialFunctional.rc_zero_add
#print axioms YMGap.Continuum.RCPolynomialFunctional.rc_scale_zero
#print axioms YMGap.Continuum.RCPolynomialFunctional.rc_scale_congr
#print axioms YMGap.Continuum.RCPolynomialFunctional.rc_scale_coeff_add
#print axioms YMGap.Continuum.RCPolynomialFunctional.rc_add_interchange
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom_coeffEqv
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom_padd
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom_pscale
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom_pneg
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom_psub
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom_zeroCons
#print axioms YMGap.Continuum.RCPolynomialFunctional.formFrom_singleton
