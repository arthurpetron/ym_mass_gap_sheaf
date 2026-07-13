/-
# Canonical finite Chebyshev-U extraction for bare rational polynomials

This module gives the constructive basis-change algorithm needed after
`SU2ClassPolynomialExtensionalReflection`.  A finite coefficient list is
evaluated in the shifted Chebyshev-U basis by `chebEvalFrom`; `xLift` is the
exact tridiagonal action of multiplication by the ordinary class coordinate
`x`.  The Horner recursion `chebExtract` therefore turns every bare
`QPoly.Poly` into finite Chebyshev-U coefficients.

The load-bearing result `chebExtract_expands` proves that synthesizing those
coefficients is extensionally equal to the original arbitrary polynomial.
No degree bound, node quadrature, measured constant, or choice enters.

Honest scope: coefficient uniqueness and descent of the vacuum functional are
successor results.  The extensional-reflection theorem imported here supplies
the required uniqueness hinge, but this file only closes extraction/existence.

# Axiom gate

All declarations are MLTT/HoTT-clean up to `propext` / `Quot.sound`.  There is
no `Classical.*`, `Real`, `native_decide`, `sorry`, `admit`, or custom axiom.
-/

import YMGap.Continuum.SU2ClassPolynomialExtensionalReflection
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.SU2ClassPolynomialChebExtraction

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.HalfPow
open YMGap.Continuum.SU2ClassPolynomialAlgebra

/-! ## Finite shifted Chebyshev series -/

def chebEvalFrom (k : Nat) : List Q' -> Q' -> Q'
  | [], _ => 0
  | a :: as, x => a * Cheb.U k x + chebEvalFrom (k + 1) as x

def chebEval (a : List Q') (x : Q') : Q' := chebEvalFrom 0 a x

def chebSynthesisFrom (k : Nat) : List Q' -> Poly
  | [] => pzero
  | a :: as => padd (pscale a (chebPoly k))
      (chebSynthesisFrom (k + 1) as)

def chebSynthesis (a : List Q') : Poly := chebSynthesisFrom 0 a

theorem chebEvalFrom_padd (k : Nat) : forall (a b : List Q') (x : Q'),
    (chebEvalFrom k (padd a b) x).eqv
      (chebEvalFrom k a x + chebEvalFrom k b x)
  | [], b, x => Q'.eqv_symm (q_zero_add_eqv _)
  | a :: as, [], x => by
      simpa [padd, chebEvalFrom] using
        (Q'.eqv_symm (q_add_zero_eqv (chebEvalFrom k (a :: as) x)))
  | a :: as, b :: bs, x => by
      show ((a + b) * Cheb.U k x +
          chebEvalFrom (k + 1) (padd as bs) x).eqv
        ((a * Cheb.U k x + chebEvalFrom (k + 1) as x) +
          (b * Cheb.U k x + chebEvalFrom (k + 1) bs x))
      refine Q'.eqv_trans _
        ((a * Cheb.U k x + b * Cheb.U k x) +
          (chebEvalFrom (k + 1) as x + chebEvalFrom (k + 1) bs x)) _ ?_ ?_
      · exact q_add_congr (q_add_mul a b (Cheb.U k x))
          (chebEvalFrom_padd (k + 1) as bs x)
      · exact q_interchange (a * Cheb.U k x) (b * Cheb.U k x)
          (chebEvalFrom (k + 1) as x) (chebEvalFrom (k + 1) bs x)

theorem chebEvalFrom_pscale (c : Q') (k : Nat) :
    forall (a : List Q') (x : Q'),
    (chebEvalFrom k (pscale c a) x).eqv (c * chebEvalFrom k a x)
  | [], _ => Q'.eqv_symm (q_mul_zero c)
  | a :: as, x => by
      show ((c * a) * Cheb.U k x +
          chebEvalFrom (k + 1) (pscale c as) x).eqv
        (c * (a * Cheb.U k x + chebEvalFrom (k + 1) as x))
      refine Q'.eqv_trans _
        (c * (a * Cheb.U k x) +
          c * chebEvalFrom (k + 1) as x) _ ?_ ?_
      · exact q_add_congr (Q'.mul_assoc_eqv c a (Cheb.U k x))
          (chebEvalFrom_pscale c (k + 1) as x)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv c (a * Cheb.U k x)
            (chebEvalFrom (k + 1) as x))

theorem eval_chebSynthesisFrom (k : Nat) : forall (a : List Q') (x : Q'),
    (eval (chebSynthesisFrom k a) x).eqv (chebEvalFrom k a x)
  | [], x => eval_pzero x
  | a :: as, x => by
      refine Q'.eqv_trans _ _ _
        (eval_padd (pscale a (chebPoly k))
          (chebSynthesisFrom (k + 1) as) x) ?_
      exact q_add_congr
        (Q'.eqv_trans _ _ _ (eval_pscale a (chebPoly k) x)
          (Q'.mul_eqv_congr_left a _ _ (eval_chebPoly k x)))
        (eval_chebSynthesisFrom (k + 1) as x)

theorem eval_chebSynthesis (a : List Q') (x : Q') :
    (eval (chebSynthesis a) x).eqv (chebEval a x) :=
  eval_chebSynthesisFrom 0 a x

/-! ## The exact `x` action on coefficient lists -/

private theorem half_two : (half * (2 : Q')).eqv 1 := by decide

private theorem half_two_mul (a : Q') :
    (half * ((2 : Q') * a)).eqv a := by
  refine Q'.eqv_trans _ ((half * (2 : Q')) * a) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv half 2 a)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ half_two) (Q'.one_mul_eqv a)

private theorem scale_swap (a b c : Q') :
    (a * (b * c)).eqv (b * (a * c)) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

private theorem xU_zero (x : Q') :
    (half * Cheb.U 1 x).eqv (x * Cheb.U 0 x) := by
  rw [Cheb.U_one, Cheb.U_zero]
  refine Q'.eqv_trans _ x _ (half_two_mul x) ?_
  exact Q'.eqv_symm (Q'.mul_one_eqv x)

private theorem half_U_pair (n : Nat) (x : Q') :
    (half * Cheb.U n x + half * Cheb.U (n + 2) x).eqv
      (x * Cheb.U (n + 1) x) := by
  have hfold : ((2 : Q') * x * Cheb.U (n + 1) x).eqv
      (Cheb.U (n + 2) x + Cheb.U n x) :=
    ChebOrthogonality.twoX_U_fold n x
  refine Q'.eqv_trans _
    (half * (Cheb.U n x + Cheb.U (n + 2) x)) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_add_eqv half (Cheb.U n x) (Cheb.U (n + 2) x))
  · refine Q'.eqv_trans _
      (half * ((2 : Q') * x * Cheb.U (n + 1) x)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left half _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv (Cheb.U n x) (Cheb.U (n + 2) x))
          (Q'.eqv_symm hfold))
    · refine Q'.eqv_trans _
        (half * ((2 : Q') * (x * Cheb.U (n + 1) x))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left half _ _
          (Q'.mul_assoc_eqv 2 x (Cheb.U (n + 1) x))
      · exact half_two_mul (x * Cheb.U (n + 1) x)

private theorem half_scaled_U_pair (a : Q') (n : Nat) (x : Q') :
    (half * (a * Cheb.U n x) +
      half * (a * Cheb.U (n + 2) x)).eqv
      (x * (a * Cheb.U (n + 1) x)) := by
  refine Q'.eqv_trans _
    (a * (half * Cheb.U n x) + a * (half * Cheb.U (n + 2) x)) _ ?_ ?_
  · exact q_add_congr (scale_swap half a (Cheb.U n x))
      (scale_swap half a (Cheb.U (n + 2) x))
  · refine Q'.eqv_trans _
      (a * (half * Cheb.U n x + half * Cheb.U (n + 2) x)) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_add_eqv a (half * Cheb.U n x)
          (half * Cheb.U (n + 2) x))
    · refine Q'.eqv_trans _ (a * (x * Cheb.U (n + 1) x)) _
        (Q'.mul_eqv_congr_left a _ _ (half_U_pair n x)) ?_
      exact scale_swap a x (Cheb.U (n + 1) x)

private theorem half_shift_pair : forall (a : List Q') (k : Nat) (x : Q'),
    (half * chebEvalFrom k a x +
      half * chebEvalFrom (k + 2) a x).eqv
      (x * chebEvalFrom (k + 1) a x)
  | [], k, x => by
      exact Q'.eqv_trans _ _ _ (q_add_congr (q_mul_zero half) (q_mul_zero half))
        (Q'.eqv_symm (q_mul_zero x))
  | a :: as, k, x => by
      show (half * (a * Cheb.U k x + chebEvalFrom (k + 1) as x) +
          half * (a * Cheb.U (k + 2) x +
            chebEvalFrom (k + 3) as x)).eqv
        (x * (a * Cheb.U (k + 1) x +
          chebEvalFrom (k + 2) as x))
      refine Q'.eqv_trans _
        ((half * (a * Cheb.U k x) +
            half * chebEvalFrom (k + 1) as x) +
          (half * (a * Cheb.U (k + 2) x) +
            half * chebEvalFrom (k + 3) as x)) _ ?_ ?_
      · exact q_add_congr
          (Q'.mul_add_eqv half (a * Cheb.U k x)
            (chebEvalFrom (k + 1) as x))
          (Q'.mul_add_eqv half (a * Cheb.U (k + 2) x)
            (chebEvalFrom (k + 3) as x))
      · refine Q'.eqv_trans _
          ((half * (a * Cheb.U k x) +
              half * (a * Cheb.U (k + 2) x)) +
            (half * chebEvalFrom (k + 1) as x +
              half * chebEvalFrom (k + 3) as x)) _ ?_ ?_
        · exact q_interchange (half * (a * Cheb.U k x))
            (half * chebEvalFrom (k + 1) as x)
            (half * (a * Cheb.U (k + 2) x))
            (half * chebEvalFrom (k + 3) as x)
        · refine Q'.eqv_trans _
            (x * (a * Cheb.U (k + 1) x) +
              x * chebEvalFrom (k + 2) as x) _ ?_ ?_
          · exact q_add_congr (half_scaled_U_pair a k x)
              (half_shift_pair as (k + 1) x)
          · exact Q'.eqv_symm
              (Q'.mul_add_eqv x (a * Cheb.U (k + 1) x)
                (chebEvalFrom (k + 2) as x))

/-- Tridiagonal coefficient action of multiplication by the class coordinate
`x`: upward shift plus downward shift, each weighted by `1/2`; the vacuum
boundary has no fictitious `U_{-1}` term. -/
def xLift (a : List Q') : List Q' :=
  padd (0 :: pscale half a) (pscale half a.tail)

/-- `xLift` is exactly multiplication by `x` at every rational class point. -/
theorem chebEval_xLift (a : List Q') (x : Q') :
    (chebEval (xLift a) x).eqv (x * chebEval a x) := by
  cases a with
  | nil =>
      exact Q'.eqv_trans _ _ _
        (chebEvalFrom_padd 0 [0] [] x)
        (Q'.eqv_trans _ _ _
          (q_add_congr (q_add_congr (q_zero_mul _) (Q'.eqv_refl 0))
            (Q'.eqv_refl 0))
          (Q'.eqv_symm (q_mul_zero x)))
  | cons a as =>
      refine Q'.eqv_trans _
        (chebEvalFrom 0 (0 :: pscale half (a :: as)) x +
          chebEvalFrom 0 (pscale half as) x) _
        (chebEvalFrom_padd 0 _ _ x) ?_
      refine Q'.eqv_trans _
        (half * chebEvalFrom 1 (a :: as) x +
          half * chebEvalFrom 0 as x) _ ?_ ?_
      · exact q_add_congr
          (Q'.eqv_trans _ _ _
            (q_add_congr (q_zero_mul (Cheb.U 0 x))
              (chebEvalFrom_pscale half 1 (a :: as) x))
            (q_zero_add_eqv _))
          (chebEvalFrom_pscale half 0 as x)
      · refine Q'.eqv_trans _
          (half * (a * Cheb.U 1 x) +
            (half * chebEvalFrom 2 as x +
              half * chebEvalFrom 0 as x)) _ ?_ ?_
        · refine Q'.eqv_trans _
            ((half * (a * Cheb.U 1 x) +
              half * chebEvalFrom 2 as x) +
              half * chebEvalFrom 0 as x) _ ?_ ?_
          · exact Q'.add_eqv_congr_right _ _ _
              (Q'.mul_add_eqv half (a * Cheb.U 1 x)
                (chebEvalFrom 2 as x))
          · exact Q'.add_assoc_eqv _ _ _
        · refine Q'.eqv_trans _
            (x * (a * Cheb.U 0 x) +
              x * chebEvalFrom 1 as x) _ ?_ ?_
          · exact q_add_congr
              (Q'.eqv_trans _
                (a * (half * Cheb.U 1 x)) _
                (scale_swap half a (Cheb.U 1 x))
                (Q'.eqv_trans _ _ _
                  (Q'.mul_eqv_congr_left a _ _ (xU_zero x))
                  (scale_swap a x (Cheb.U 0 x))))
              (Q'.eqv_trans _ _ _
                (Q'.add_comm_eqv _ _)
                (half_shift_pair as 0 x))
          · exact Q'.eqv_symm
              (Q'.mul_add_eqv x (a * Cheb.U 0 x)
                (chebEvalFrom 1 as x))

/-! ## Horner extraction and finite expansion -/

def chebExtract : Poly -> List Q'
  | [] => []
  | c :: cs => padd [c] (xLift (chebExtract cs))

theorem chebEval_extract : forall (p : Poly) (x : Q'),
    (chebEval (chebExtract p) x).eqv (eval p x)
  | [], _ => Q'.eqv_refl 0
  | c :: cs, x => by
      refine Q'.eqv_trans _
        (chebEval [c] x + chebEval (xLift (chebExtract cs)) x) _
        (chebEvalFrom_padd 0 [c] (xLift (chebExtract cs)) x) ?_
      exact q_add_congr
        (Q'.eqv_trans _ _ _
          (q_add_zero_eqv _)
          (Q'.mul_one_eqv c))
        (Q'.eqv_trans _ _ _ (chebEval_xLift (chebExtract cs) x)
          (Q'.mul_eqv_congr_left x _ _ (chebEval_extract cs x)))

/-- Every arbitrary bare `QPoly` has a computably extracted finite
Chebyshev-U expansion. -/
theorem chebExtract_expands (p : Poly) :
    PolyEqv (chebSynthesis (chebExtract p)) p := by
  intro x
  exact Q'.eqv_trans _ _ _
    (eval_chebSynthesis (chebExtract p) x) (chebEval_extract p x)

end YMGap.Continuum.SU2ClassPolynomialChebExtraction

#print axioms YMGap.Continuum.SU2ClassPolynomialChebExtraction.eval_chebSynthesisFrom
#print axioms YMGap.Continuum.SU2ClassPolynomialChebExtraction.half_U_pair
#print axioms YMGap.Continuum.SU2ClassPolynomialChebExtraction.half_shift_pair
#print axioms YMGap.Continuum.SU2ClassPolynomialChebExtraction.chebEval_xLift
#print axioms YMGap.Continuum.SU2ClassPolynomialChebExtraction.chebEval_extract
#print axioms YMGap.Continuum.SU2ClassPolynomialChebExtraction.chebExtract_expands
