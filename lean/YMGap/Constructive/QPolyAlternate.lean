/-
# Alternating-sign recoding for constructive rational polynomials

`alternate` substitutes `-z` coefficientwise by multiplying coefficient
`n` by `(-1)^n`.  The implementation stays on finite coefficient lists and
the proofs show that this recoding respects addition, scaling, and
multiplication up to the project's rational equivalence.

This is the algebraic bridge from reflected Euler coefficients to a
nonnegative companion polynomial.  It uses no classical coefficient choice
or normalized rational representatives.
-/

import YMGap.Constructive.QPolyFormalDerivative

namespace YMGap.Constructive.QPolyAlternate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative

/-- Coefficient-list substitution `p(z) -> p(-z)`. -/
def alternate : Poly -> Poly
  | [] => []
  | c :: cs => c :: pneg (alternate cs)

/-- Exact padded coefficient formula for alternating-sign recoding. -/
theorem coeff_alternate : forall (p : Poly) (index : Nat),
    (coeff (alternate p) index).eqv
      (((-1 : Q') ^ index) * coeff p index)
  | [], index => Q'.eqv_symm (q_mul_zero ((-1 : Q') ^ index))
  | c :: cs, 0 => Q'.eqv_symm (Q'.one_mul_eqv c)
  | c :: cs, index + 1 => by
      change (coeff (pneg (alternate cs)) index).eqv
        (((-1 : Q') ^ (index + 1)) * coeff cs index)
      rw [Q'.pow_succ]
      refine Q'.eqv_trans _
        ((-1 : Q') * coeff (alternate cs) index) _
        (coeff_pneg (alternate cs) index) ?_
      refine Q'.eqv_trans _
        ((-1 : Q') * (((-1 : Q') ^ index) * coeff cs index)) _
        (Q'.mul_eqv_congr_left (-1) _ _ (coeff_alternate cs index)) ?_
      refine Q'.eqv_trans _
        (((-1 : Q') * ((-1 : Q') ^ index)) * coeff cs index) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (-1) ((-1 : Q') ^ index) (coeff cs index))) ?_
      exact Q'.eqv_refl _

/-- Coefficientwise equivalence is preserved by adding one leading zero. -/
theorem CoeffEqv.zeroCons {p q : Poly} (h : CoeffEqv p q) :
    CoeffEqv ((0 : Q') :: p) ((0 : Q') :: q)
  | 0 => Q'.eqv_refl 0
  | index + 1 => h index

/-- Alternating-sign recoding respects polynomial addition. -/
theorem alternate_padd (p q : Poly) :
    CoeffEqv (alternate (padd p q)) (padd (alternate p) (alternate q)) := by
  intro index
  let sign : Q' := (-1 : Q') ^ index
  exact Q'.eqv_trans _ (sign * coeff (padd p q) index) _
    (coeff_alternate (padd p q) index)
    (Q'.eqv_trans _ (sign * (coeff p index + coeff q index)) _
      (Q'.mul_eqv_congr_left sign _ _ (coeff_padd index p q))
      (Q'.eqv_trans _
        (sign * coeff p index + sign * coeff q index) _
        (Q'.mul_add_eqv sign (coeff p index) (coeff q index))
        (Q'.eqv_trans _
          (coeff (alternate p) index + coeff (alternate q) index) _
          (q_add_congr
            (Q'.eqv_symm (coeff_alternate p index))
            (Q'.eqv_symm (coeff_alternate q index)))
          (Q'.eqv_symm (coeff_padd index (alternate p) (alternate q))))))

/-- Alternating-sign recoding respects scalar multiplication. -/
theorem alternate_pscale (k : Q') (p : Poly) :
    CoeffEqv (alternate (pscale k p)) (pscale k (alternate p)) := by
  intro index
  let sign : Q' := (-1 : Q') ^ index
  exact Q'.eqv_trans _ (sign * coeff (pscale k p) index) _
    (coeff_alternate (pscale k p) index)
    (Q'.eqv_trans _ (sign * (k * coeff p index)) _
      (Q'.mul_eqv_congr_left sign _ _ (coeff_pscale k p index))
      (Q'.eqv_trans _ (k * (sign * coeff p index)) _
        (Q'.eqv_trans _ ((sign * k) * coeff p index) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv sign k (coeff p index)))
          (Q'.eqv_trans _ ((k * sign) * coeff p index) _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv sign k))
            (Q'.mul_assoc_eqv k sign (coeff p index))))
        (Q'.eqv_trans _ (k * coeff (alternate p) index) _
          (Q'.mul_eqv_congr_left k _ _
            (Q'.eqv_symm (coeff_alternate p index)))
          (Q'.eqv_symm (coeff_pscale k (alternate p) index)))))

/-- Alternating-sign recoding is multiplicative for finite polynomials. -/
theorem alternate_pmul : forall p q : Poly,
    CoeffEqv (alternate (pmul p q)) (pmul (alternate p) (alternate q))
  | [], q => CoeffEqv.refl []
  | a :: ps, q => by
      change CoeffEqv
        (alternate (padd (pscale a q) ((0 : Q') :: pmul ps q)))
        (pmul (a :: pneg (alternate ps)) (alternate q))
      refine CoeffEqv.trans (alternate_padd _ _) ?_
      refine CoeffEqv.trans
        (CoeffEqv.padd
          (alternate_pscale a q)
          (CoeffEqv.zeroCons
            (CoeffEqv.pneg (alternate_pmul ps q)))) ?_
      refine CoeffEqv.trans
        (CoeffEqv.padd (CoeffEqv.refl _)
          (CoeffEqv.zeroCons
            (CoeffEqv.symm
              (coeffEqv_pscale_pmul
                (-1) (alternate ps) (alternate q))))) ?_
      change CoeffEqv
        (padd (pscale a (alternate q))
          ((0 : Q') :: pmul (pneg (alternate ps)) (alternate q)))
        (padd (pscale a (alternate q))
          ((0 : Q') :: pmul (pneg (alternate ps)) (alternate q)))
      exact CoeffEqv.refl _

end YMGap.Constructive.QPolyAlternate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.QPolyAlternate.coeff_alternate
#print axioms YMGap.Constructive.QPolyAlternate.alternate_padd
#print axioms YMGap.Constructive.QPolyAlternate.alternate_pscale
#print axioms YMGap.Constructive.QPolyAlternate.alternate_pmul
