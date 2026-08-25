/-
# Arbitrary coefficients of constructive rational polynomials

The coefficient-list carrier already supports executable finite-prefix checks.
This module supplies the scalable proof-facing view: an arbitrary padded
coefficient extractor, its laws under the polynomial operations, and the exact
equivalence between pointwise coefficient vanishing below `count` and the
Boolean-backed `zeroPrefix count` predicate.

No classical choice, normalization of rational representatives, or
metaprogrammed ring tactic is used.
-/

import YMGap.Constructive.QPolyJetOne

namespace YMGap.Constructive.QPolyCoefficient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Constructive.QPolyJetOne

/-- Coefficient at an arbitrary degree, with implicit zero padding. -/
def coeff : Poly -> Nat -> Q'
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, n + 1 => coeff cs n

theorem coeff_zero_eq_constantCoeff (p : Poly) :
    (coeff p 0).eqv (constantCoeff p) := by
  cases p <;> exact Q'.eqv_refl _

theorem coeff_one_eq_linearCoeff (p : Poly) :
    (coeff p 1).eqv (linearCoeff p) := by
  cases p with
  | nil => exact Q'.eqv_refl 0
  | cons c cs => exact coeff_zero_eq_constantCoeff cs

theorem coeff_padd : forall (n : Nat) (p q : Poly),
    (coeff (padd p q) n).eqv (coeff p n + coeff q n)
  | 0, p, q =>
      Q'.eqv_trans _ _ _ (coeff_zero_eq_constantCoeff (padd p q))
        (Q'.eqv_trans _ _ _ (constantCoeff_padd p q)
          (q_add_congr
            (Q'.eqv_symm (coeff_zero_eq_constantCoeff p))
            (Q'.eqv_symm (coeff_zero_eq_constantCoeff q))))
  | n + 1, [], q => Q'.eqv_symm (q_zero_add_eqv (coeff q (n + 1)))
  | n + 1, a :: ps, [] =>
      Q'.eqv_symm (q_add_zero_eqv (coeff (a :: ps) (n + 1)))
  | n + 1, _ :: ps, _ :: qs => coeff_padd n ps qs

theorem coeff_pscale (k : Q') : forall (p : Poly) (n : Nat),
    (coeff (pscale k p) n).eqv (k * coeff p n)
  | [], _ => Q'.eqv_symm (q_mul_zero k)
  | c :: _, 0 => Q'.eqv_refl (k * c)
  | _ :: cs, n + 1 => coeff_pscale k cs n

theorem coeff_pneg (p : Poly) (n : Nat) :
    (coeff (pneg p) n).eqv ((-1 : Q') * coeff p n) :=
  coeff_pscale (-1) p n

theorem coeff_psub (p q : Poly) (n : Nat) :
    (coeff (psub p q) n).eqv
      (coeff p n + ((-1 : Q') * coeff q n)) :=
  Q'.eqv_trans _ _ _ (coeff_padd n p (pneg q))
    (q_add_congr (Q'.eqv_refl _) (coeff_pneg q n))

/-- Equal input coefficients make the corresponding subtraction coefficient
vanish. -/
theorem coeff_psub_eqv_zero_of_eqv
    (p q : Poly) (n : Nat)
    (hcoeff : (coeff p n).eqv (coeff q n)) :
    (coeff (psub p q) n).eqv 0 := by
  have hneg : (((-1 : Q') * coeff q n)).eqv (-(coeff q n)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (coeff q n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (coeff q n)))
  exact Q'.eqv_trans _
    (coeff p n + ((-1 : Q') * coeff q n)) _
    (coeff_psub p q n)
    (Q'.eqv_trans _ (coeff p n + -(coeff q n)) _
      (q_add_congr (Q'.eqv_refl _) hneg)
      (Q'.eqv_trans _ (coeff q n + -(coeff q n)) _
        (Q'.add_eqv_congr_right _ _ (-(coeff q n)) hcoeff)
        (Q'.add_neg_self_eqv (coeff q n))))

/-- Recursive convolution coefficient.  The recursion follows the first
polynomial, matching the implementation of `pmul`. -/
def mulCoeff : Poly -> Poly -> Nat -> Q'
  | [], _, _ => 0
  | a :: _, q, 0 => a * coeff q 0
  | a :: ps, q, n + 1 => a * coeff q (n + 1) + mulCoeff ps q n

theorem coeff_pmul : forall (p q : Poly) (n : Nat),
    (coeff (pmul p q) n).eqv (mulCoeff p q n)
  | [], q, n => Q'.eqv_refl 0
  | a :: ps, q, 0 => by
      refine Q'.eqv_trans _
        (coeff (pscale a q) 0 + coeff (0 :: pmul ps q) 0) _
        (coeff_padd 0 (pscale a q) (0 :: pmul ps q)) ?_
      exact Q'.eqv_trans _ (a * coeff q 0 + 0) _
        (q_add_congr (coeff_pscale a q 0) (Q'.eqv_refl 0))
        (q_add_zero_eqv (a * coeff q 0))
  | a :: ps, q, n + 1 => by
      refine Q'.eqv_trans _
        (coeff (pscale a q) (n + 1) +
          coeff (0 :: pmul ps q) (n + 1)) _
        (coeff_padd (n + 1) (pscale a q) (0 :: pmul ps q)) ?_
      exact q_add_congr (coeff_pscale a q (n + 1))
        (coeff_pmul ps q n)

/-- A passed executable prefix check yields pointwise coefficient vanishing at
every smaller degree. -/
theorem coeff_eqv_zero_of_zeroPrefix :
    forall (count : Nat) (p : Poly),
      zeroPrefix count p ->
      forall index : Nat, index < count -> (coeff p index).eqv 0
  | 0, p, hprefix, index, hindex => by omega
  | count + 1, [], hprefix, index, hindex => Q'.eqv_refl 0
  | count + 1, c :: cs, hprefix, 0, hindex => by
      have hparts := hprefix
      unfold zeroPrefix zeroPrefixB at hparts
      rw [Bool.and_eq_true] at hparts
      exact of_decide_eq_true hparts.1
  | count + 1, c :: cs, hprefix, index + 1, hindex => by
      have hparts := hprefix
      unfold zeroPrefix zeroPrefixB at hparts
      rw [Bool.and_eq_true] at hparts
      exact coeff_eqv_zero_of_zeroPrefix count cs hparts.2 index (by omega)

/-- Pointwise vanishing below `count` constructs the executable Boolean prefix
certificate. -/
theorem zeroPrefix_of_coeff_eqv_zero :
    forall (count : Nat) (p : Poly),
      (forall index : Nat, index < count -> (coeff p index).eqv 0) ->
      zeroPrefix count p
  | 0, p, hcoeff => rfl
  | count + 1, [], hcoeff => rfl
  | count + 1, c :: cs, hcoeff => by
      have hc : c.eqv 0 := hcoeff 0 (by omega)
      have htail : forall index : Nat, index < count ->
          (coeff cs index).eqv 0 := by
        intro index hindex
        exact hcoeff (index + 1) (by omega)
      unfold zeroPrefix zeroPrefixB
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true hc,
        zeroPrefix_of_coeff_eqv_zero count cs htail⟩

theorem zeroPrefix_iff_coeff_eqv_zero (count : Nat) (p : Poly) :
    zeroPrefix count p <->
      forall index : Nat, index < count -> (coeff p index).eqv 0 :=
  ⟨coeff_eqv_zero_of_zeroPrefix count p,
    zeroPrefix_of_coeff_eqv_zero count p⟩

end YMGap.Constructive.QPolyCoefficient

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.QPolyCoefficient.coeff_pmul
#print axioms YMGap.Constructive.QPolyCoefficient.coeff_psub_eqv_zero_of_eqv
#print axioms YMGap.Constructive.QPolyCoefficient.coeff_eqv_zero_of_zeroPrefix
#print axioms YMGap.Constructive.QPolyCoefficient.zeroPrefix_of_coeff_eqv_zero
#print axioms YMGap.Constructive.QPolyCoefficient.zeroPrefix_iff_coeff_eqv_zero
