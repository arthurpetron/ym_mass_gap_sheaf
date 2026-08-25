/-
# Constructive zero-prefix valuation for rational polynomials

The Boolean-backed `zeroPrefix` predicate is the constructive analogue of a
lower bound on polynomial valuation.  This module proves the algebra needed by
formal power-series truncations: zero prefixes are preserved by addition and
scaling, and the prefix lengths of two factors add under multiplication.

All statements are about explicit coefficient lists and rational equivalence.
No normalization, classical choice, or metaprogrammed algebra tactic is used.
-/

import YMGap.Constructive.QPolyCoefficient

namespace YMGap.Constructive.QPolyValuation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Constructive.QPolyCoefficient

theorem zeroPrefix_nil (count : Nat) : zeroPrefix count ([] : Poly) := by
  cases count <;> rfl

/-- A longer proved zero prefix can be restricted to any shorter prefix. -/
theorem zeroPrefix_mono
    {short long : Nat} {p : Poly} (hshort : short <= long)
    (hlong : zeroPrefix long p) :
    zeroPrefix short p :=
  zeroPrefix_of_coeff_eqv_zero short p (fun index hindex =>
    coeff_eqv_zero_of_zeroPrefix long p hlong index
      (Nat.lt_of_lt_of_le hindex hshort))

theorem zeroPrefix_padd
    (count : Nat) (p q : Poly)
    (hp : zeroPrefix count p) (hq : zeroPrefix count q) :
    zeroPrefix count (padd p q) :=
  zeroPrefix_of_coeff_eqv_zero count (padd p q) (fun index hindex =>
    Q'.eqv_trans _
      (coeff p index + coeff q index) _
      (coeff_padd index p q)
      (Q'.eqv_trans _ (0 + 0) _
        (q_add_congr
          (coeff_eqv_zero_of_zeroPrefix count p hp index hindex)
          (coeff_eqv_zero_of_zeroPrefix count q hq index hindex))
        (q_add_zero_eqv 0)))

theorem zeroPrefix_pscale
    (count : Nat) (k : Q') (p : Poly)
    (hp : zeroPrefix count p) :
    zeroPrefix count (pscale k p) :=
  zeroPrefix_of_coeff_eqv_zero count (pscale k p) (fun index hindex =>
    Q'.eqv_trans _ (k * coeff p index) _
      (coeff_pscale k p index)
      (Q'.eqv_trans _ (k * 0) _
        (Q'.mul_eqv_congr_left k _ 0
          (coeff_eqv_zero_of_zeroPrefix count p hp index hindex))
        (q_mul_zero k)))

/-- Scaling by a rational equivalent to zero gives an arbitrarily long zero
prefix, independently of the input polynomial. -/
theorem zeroPrefix_pscale_of_eqv_zero
    (count : Nat) (k : Q') (p : Poly) (hk : k.eqv 0) :
    zeroPrefix count (pscale k p) :=
  zeroPrefix_of_coeff_eqv_zero count (pscale k p) (fun index _hindex =>
    Q'.eqv_trans _ (k * coeff p index) _
      (coeff_pscale k p index)
      (Q'.eqv_trans _ (0 * coeff p index) _
        (Q'.mul_eqv_congr_right k 0 (coeff p index) hk)
        (q_zero_mul (coeff p index))))

/-- Prepending an exact zero raises the zero-prefix length by one. -/
theorem zeroPrefix_zero_cons_succ
    (count : Nat) (p : Poly) (hp : zeroPrefix count p) :
    zeroPrefix (count + 1) ((0 : Q') :: p) := by
  unfold zeroPrefix zeroPrefixB
  rw [Bool.and_eq_true]
  exact ⟨by decide, hp⟩

/-- Prepending zero also preserves any already known prefix length. -/
theorem zeroPrefix_zero_cons
    (count : Nat) (p : Poly) (hp : zeroPrefix count p) :
    zeroPrefix count ((0 : Q') :: p) :=
  zeroPrefix_mono (Nat.le_add_right count 1)
    (zeroPrefix_zero_cons_succ count p hp)

/-- A zero prefix on the right factor is inherited by the product. -/
theorem zeroPrefix_pmul_right
    (count : Nat) (q : Poly) (hq : zeroPrefix count q) :
    forall p : Poly, zeroPrefix count (pmul p q)
  | [] => zeroPrefix_nil count
  | a :: ps =>
      zeroPrefix_padd count _ _
        (zeroPrefix_pscale count a q hq)
        (zeroPrefix_zero_cons count (pmul ps q)
          (zeroPrefix_pmul_right count q hq ps))

/-- Polynomial valuation is additive: if the first `left` coefficients of
`p` and first `right` coefficients of `q` vanish, then the first
`left + right` coefficients of their product vanish. -/
theorem zeroPrefix_pmul_add :
    forall (left right : Nat) (p q : Poly),
      zeroPrefix left p -> zeroPrefix right q ->
      zeroPrefix (left + right) (pmul p q)
  | 0, right, p, q, hp, hq => by
      simpa using zeroPrefix_pmul_right right q hq p
  | left + 1, right, [], q, hp, hq => zeroPrefix_nil (left + 1 + right)
  | left + 1, right, a :: ps, q, hp, hq => by
      have hparts := hp
      unfold zeroPrefix zeroPrefixB at hparts
      rw [Bool.and_eq_true] at hparts
      have ha : a.eqv 0 := of_decide_eq_true hparts.1
      have hps : zeroPrefix left ps := hparts.2
      have htail : zeroPrefix (left + right) (pmul ps q) :=
        zeroPrefix_pmul_add left right ps q hps hq
      have hshift : zeroPrefix ((left + right) + 1)
          ((0 : Q') :: pmul ps q) :=
        zeroPrefix_zero_cons_succ (left + right) (pmul ps q) htail
      have hshift' : zeroPrefix (left + 1 + right)
          ((0 : Q') :: pmul ps q) := by
        have hcount : left + 1 + right = (left + right) + 1 := by omega
        rw [hcount]
        exact hshift
      change zeroPrefix (left + 1 + right)
        (padd (pscale a q) ((0 : Q') :: pmul ps q))
      exact zeroPrefix_padd (left + 1 + right) _ _
        (zeroPrefix_pscale_of_eqv_zero (left + 1 + right) a q ha)
        hshift'

end YMGap.Constructive.QPolyValuation

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.QPolyValuation.zeroPrefix_mono
#print axioms YMGap.Constructive.QPolyValuation.zeroPrefix_padd
#print axioms YMGap.Constructive.QPolyValuation.zeroPrefix_pscale
#print axioms YMGap.Constructive.QPolyValuation.zeroPrefix_pmul_add
