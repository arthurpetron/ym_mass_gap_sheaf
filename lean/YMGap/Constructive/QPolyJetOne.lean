/-
# Constant and linear jets for constructive rational polynomials

This module exposes the first two coefficients of the coefficient-list
polynomial carrier and proves their behavior under the ring operations used by
the artanh-Euler compiler.  It is a deliberately small formal-jet layer: no
derivative, quotient, classical choice, or normalization of `Q'`
representatives is used.
-/

import YMGap.Constructive.QPolyWeightedL1

namespace YMGap.Constructive.QPolyJetOne

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyWeightedL1

/-- Constant coefficient, with implicit zero padding. -/
def constantCoeff : Poly -> Q'
  | [] => 0
  | c :: _ => c

/-- Linear coefficient, with implicit zero padding. -/
def linearCoeff : Poly -> Q'
  | [] => 0
  | _ :: cs => constantCoeff cs

theorem constantCoeff_padd (p q : Poly) :
    (constantCoeff (padd p q)).eqv
      (constantCoeff p + constantCoeff q) := by
  cases p with
  | nil =>
      exact Q'.eqv_symm (q_zero_add_eqv (constantCoeff q))
  | cons a ps =>
      cases q with
      | nil => exact Q'.eqv_symm (q_add_zero_eqv a)
      | cons b qs => exact Q'.eqv_refl (a + b)

theorem linearCoeff_padd (p q : Poly) :
    (linearCoeff (padd p q)).eqv
      (linearCoeff p + linearCoeff q) := by
  cases p with
  | nil =>
      exact Q'.eqv_symm (q_zero_add_eqv (linearCoeff q))
  | cons a ps =>
      cases q with
      | nil => exact Q'.eqv_symm (q_add_zero_eqv (constantCoeff ps))
      | cons b qs => exact constantCoeff_padd ps qs

theorem constantCoeff_pscale (k : Q') (p : Poly) :
    (constantCoeff (pscale k p)).eqv (k * constantCoeff p) := by
  cases p with
  | nil => exact Q'.eqv_symm (q_mul_zero k)
  | cons c cs => exact Q'.eqv_refl (k * c)

theorem linearCoeff_pscale (k : Q') (p : Poly) :
    (linearCoeff (pscale k p)).eqv (k * linearCoeff p) := by
  cases p with
  | nil => exact Q'.eqv_symm (q_mul_zero k)
  | cons c cs => exact constantCoeff_pscale k cs

theorem constantCoeff_pneg (p : Poly) :
    (constantCoeff (pneg p)).eqv ((-1 : Q') * constantCoeff p) :=
  constantCoeff_pscale (-1) p

theorem linearCoeff_pneg (p : Poly) :
    (linearCoeff (pneg p)).eqv ((-1 : Q') * linearCoeff p) :=
  linearCoeff_pscale (-1) p

theorem constantCoeff_pmul : forall p q : Poly,
    (constantCoeff (pmul p q)).eqv
      (constantCoeff p * constantCoeff q)
  | [], q => Q'.eqv_symm (q_zero_mul (constantCoeff q))
  | a :: ps, q => by
      refine Q'.eqv_trans _
        (constantCoeff (pscale a q) +
          constantCoeff (0 :: pmul ps q)) _
        (constantCoeff_padd (pscale a q) (0 :: pmul ps q)) ?_
      exact Q'.eqv_trans _ (a * constantCoeff q + 0) _
        (q_add_congr
          (constantCoeff_pscale a q)
          (Q'.eqv_refl 0))
        (q_add_zero_eqv (a * constantCoeff q))

theorem linearCoeff_pmul : forall p q : Poly,
    (linearCoeff (pmul p q)).eqv
      (constantCoeff p * linearCoeff q +
        linearCoeff p * constantCoeff q)
  | [], q => by
      refine Q'.eqv_symm ?_
      exact Q'.eqv_trans _ (0 + 0) _
        (q_add_congr
          (q_zero_mul (linearCoeff q))
          (q_zero_mul (constantCoeff q)))
        (q_add_zero_eqv 0)
  | a :: ps, q => by
      refine Q'.eqv_trans _
        (linearCoeff (pscale a q) +
          linearCoeff (0 :: pmul ps q)) _
        (linearCoeff_padd (pscale a q) (0 :: pmul ps q)) ?_
      refine Q'.eqv_trans _
        (a * linearCoeff q + constantCoeff (pmul ps q)) _
        (q_add_congr
          (linearCoeff_pscale a q)
          (Q'.eqv_refl _)) ?_
      exact q_add_congr (Q'.eqv_refl _)
        (constantCoeff_pmul ps q)

theorem constantCoeff_psub (p q : Poly) :
    (constantCoeff (psub p q)).eqv
      (constantCoeff p + ((-1 : Q') * constantCoeff q)) :=
  Q'.eqv_trans _ _ _ (constantCoeff_padd p (pneg q))
    (q_add_congr (Q'.eqv_refl _) (constantCoeff_pneg q))

theorem linearCoeff_psub (p q : Poly) :
    (linearCoeff (psub p q)).eqv
      (linearCoeff p + ((-1 : Q') * linearCoeff q)) :=
  Q'.eqv_trans _ _ _ (linearCoeff_padd p (pneg q))
    (q_add_congr (Q'.eqv_refl _) (linearCoeff_pneg q))

/-- Vanishing constant and linear jets give the executable two-coefficient
zero prefix consumed by the weighted-tail factorization. -/
theorem zeroPrefix_two_of_coefficients_zero
    (p : Poly)
    (hconstant : (constantCoeff p).eqv 0)
    (hlinear : (linearCoeff p).eqv 0) :
    zeroPrefix 2 p := by
  cases p with
  | nil => rfl
  | cons c cs =>
      have hc : c.eqv 0 := hconstant
      unfold zeroPrefix zeroPrefixB
      rw [show decide (c.eqv 0) = true from decide_eq_true hc]
      simp only [Bool.true_and]
      cases cs with
      | nil => rfl
      | cons d ds =>
          have hd : d.eqv 0 := hlinear
          change decide (d.eqv 0) && true = true
          rw [show decide (d.eqv 0) = true from decide_eq_true hd]
          rfl

end YMGap.Constructive.QPolyJetOne

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.QPolyJetOne.constantCoeff_pmul
#print axioms YMGap.Constructive.QPolyJetOne.linearCoeff_pmul
#print axioms YMGap.Constructive.QPolyJetOne.zeroPrefix_two_of_coefficients_zero
