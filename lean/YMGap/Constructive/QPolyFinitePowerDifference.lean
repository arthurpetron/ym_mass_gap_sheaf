/-
Finite difference-of-powers and exponent identities for the ACTUAL rational
polynomial coefficient lists.  The recursive row is
`p^(m-1) + p^(m-2)q + ... + q^(m-1)` when m>0, and is empty at zero.
No scalar evaluation, division, or analytic positivity premise is used.
-/

import YMGap.Constructive.QPolyFiniteGeometric

namespace YMGap.Constructive.QPolyFinitePowerDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower)

/-- Computed finite difference-of-powers row, including the empty case. -/
def powerDifferenceRow (p q : Poly) : Nat → Poly
  | 0 => []
  | m + 1 => padd (pmul p (powerDifferenceRow p q m)) (polynomialPower q m)

private theorem mul_sub_right (p q r : Poly) :
    CoeffEqv (pmul p (psub q r)) (psub (pmul p q) (pmul p r)) :=
  (coeffEqv_pmul_padd_right p q (pneg r)).trans
    (CoeffEqv.padd (CoeffEqv.refl _) (coeffEqv_pmul_pscale (-1) p r))

private theorem sub_mul_left (p q r : Poly) :
    CoeffEqv (pmul (psub p q) r) (psub (pmul p r) (pmul q r)) :=
  (coeffEqv_padd_pmul_left p (pneg q) r).trans
    (CoeffEqv.padd (CoeffEqv.refl _) (coeffEqv_pscale_pmul (-1) q r))

/-- Difference-of-powers factorization at every padded coefficient, including
m=0 and arbitrary (possibly signed) input polynomials. -/
theorem powerDifference_telescope (p q : Poly) (m : Nat) :
    CoeffEqv (pmul (psub p q) (powerDifferenceRow p q m))
      (psub (polynomialPower p m) (polynomialPower q m)) := by
  induction m with
  | zero =>
      exact (coeffEqv_pmul_comm (psub p q) []).trans
        (coeffEqv_padd_pneg_self [1]).symm
  | succ m ih =>
      let row := powerDifferenceRow p q m
      have hleft :
          CoeffEqv (pmul (psub p q) (pmul p row))
            (psub (pmul p (polynomialPower p m))
              (pmul p (polynomialPower q m))) :=
        (coeffEqv_pmul_assoc (psub p q) p row).symm.trans
          (((coeffEqv_pmul_comm (psub p q) p).pmul (CoeffEqv.refl row)).trans
            ((coeffEqv_pmul_assoc p (psub p q) row).trans
              (((CoeffEqv.refl p).pmul ih).trans (mul_sub_right _ _ _))))
      have hright :
          CoeffEqv (pmul (psub p q) (polynomialPower q m))
            (psub (pmul p (polynomialPower q m))
              (pmul q (polynomialPower q m))) :=
        sub_mul_left _ _ _
      exact (coeffEqv_pmul_padd_right (psub p q) (pmul p row)
          (polynomialPower q m)).trans
        ((CoeffEqv.padd hleft hright).trans
          (coeffEqv_padd_pneg_cancel (pmul p (polynomialPower p m))
            (pmul p (polynomialPower q m))
            (pneg (pmul q (polynomialPower q m)))))

/-- Addition of polynomial exponents, proved coefficientwise without
evaluating or normalizing the arbitrary polynomial p. -/
theorem polynomialPower_add (p : Poly) (a b : Nat) :
    CoeffEqv (pmul (polynomialPower p a) (polynomialPower p b))
      (polynomialPower p (a + b)) := by
  induction a with
  | zero =>
      simpa only [Nat.zero_add, polynomialPower] using
        (coeffEqv_pmul_one_left (polynomialPower p b))
  | succ a ih =>
      have hi : (a + 1) + b = (a + b) + 1 := by omega
      rw [hi]
      exact (coeffEqv_pmul_assoc p (polynomialPower p a)
          (polynomialPower p b)).trans
        ((CoeffEqv.refl p).pmul ih)

/-- Iterated polynomial powers multiply their exponents, including n=0 or
m=0.  This is the original coefficient carrier, not a scalar power pin. -/
theorem polynomialPower_iterated (p : Poly) (n m : Nat) :
    CoeffEqv (polynomialPower (polynomialPower p n) m)
      (polynomialPower p (n * m)) := by
  induction m with
  | zero =>
      rw [Nat.mul_zero]
      exact CoeffEqv.refl [1]
  | succ m ih =>
      have hi : n + n * m = n * (m + 1) := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [← hi]
      exact ((CoeffEqv.refl (polynomialPower p n)).pmul ih).trans
        (polynomialPower_add p n (n * m))

end YMGap.Constructive.QPolyFinitePowerDifference

#print axioms YMGap.Constructive.QPolyFinitePowerDifference.powerDifferenceRow
#print axioms YMGap.Constructive.QPolyFinitePowerDifference.powerDifference_telescope
#print axioms YMGap.Constructive.QPolyFinitePowerDifference.polynomialPower_add
#print axioms YMGap.Constructive.QPolyFinitePowerDifference.polynomialPower_iterated
