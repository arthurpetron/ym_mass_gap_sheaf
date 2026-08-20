/-
Constructive representation invariance for the direct rational logarithm.

`Q'` deliberately stores unreduced numerator/denominator pairs.  Analytic
constructions must therefore respect the rational equivalence relation rather
than relying on structural equality.  This module proves that the artanh
argument, every odd-power partial sum, and hence `logRat` are invariant under
`Q'.eqv`.

The result is needed when binary range reduction has exponent zero: its
mantissa is represented as `q * 1`, which is equivalent to `q` but need not be
definitionally the same `Q'` value.
-/

import YMGap.Constructive.CRealLog
import YMGap.Constructive.TrigAdd

namespace YMGap.Constructive

namespace Q'

/-- Positive reciprocal respects rational equivalence. -/
theorem recipPos_eqv_congr (a b : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b)
    (hab : a.eqv b) :
    (recipPos a ha).eqv (recipPos b hb) := by
  unfold Q'.eqv
  rw [recipPos_num, recipPos_den, recipPos_num, recipPos_den]
  calc
    (a.den : Int) * b.num = b.num * (a.den : Int) := by
      rw [Int.mul_comm]
    _ = a.num * (b.den : Int) := hab.symm
    _ = (b.den : Int) * a.num := by
      rw [Int.mul_comm]

/-- Natural powers respect rational equivalence in their base. -/
theorem pow_eqv_congr {a b : Q'} (hab : a.eqv b) :
    forall n : Nat, (a ^ n).eqv (b ^ n)
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      show (a * a ^ n).eqv (b * b ^ n)
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right a b (a ^ n) hab)
        (Q'.mul_eqv_congr_left b (a ^ n) (b ^ n)
          (pow_eqv_congr hab n))

end Q'

namespace CRealLog

/-- The artanh coordinate `(m-1)/(m+1)` respects rational equivalence. -/
theorem yOf_eqv_congr {a b : Q'}
    (ha : (0 : Q') < a + 1) (hb : (0 : Q') < b + 1)
    (hab : a.eqv b) :
    (yOf a ha).eqv (yOf b hb) := by
  have hminus : (a + -1).eqv (b + -1) :=
    Q'.add_eqv_congr_right a b (-1) hab
  have hplus : (a + 1).eqv (b + 1) :=
    Q'.add_eqv_congr_right a b 1 hab
  have hrecip :
      (Q'.recipPos (a + 1) ha).eqv
        (Q'.recipPos (b + 1) hb) :=
    Q'.recipPos_eqv_congr (a + 1) (b + 1) ha hb hplus
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (a + -1) (b + -1)
      (Q'.recipPos (a + 1) ha) hminus)
    (Q'.mul_eqv_congr_left (b + -1)
      (Q'.recipPos (a + 1) ha) (Q'.recipPos (b + 1) hb) hrecip)

/-- Every signed artanh term respects equivalence of its argument. -/
theorem artanhTerm_eqv_congr {x y : Q'} (hxy : x.eqv y) (k : Nat) :
    (term x k).eqv (term y k) :=
  Q'.mul_eqv_congr_right
    (x ^ (2 * k + 1)) (y ^ (2 * k + 1)) (recipOdd k)
    (Q'.pow_eqv_congr hxy (2 * k + 1))

/-- Every finite artanh partial sum respects equivalence of its argument. -/
theorem artanhPartial_eqv_congr {x y : Q'} (hxy : x.eqv y) :
    forall n : Nat, (partialSum x n).eqv (partialSum y n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      show (partialSum x n + term x n).eqv
        (partialSum y n + term y n)
      exact Q'.add_eqv_congr'
        (artanhPartial_eqv_congr hxy n)
        (artanhTerm_eqv_congr hxy n)

/-- Pointwise approximation form of `logRat` representation invariance. -/
theorem logRat_approx_eqv_congr {a b : Q'}
    (ha : (0 : Q') < a + 1) (hb : (0 : Q') < b + 1)
    (wa : Q'.abs (yOf a ha) <= recipOdd 1)
    (wb : Q'.abs (yOf b hb) <= recipOdd 1)
    (hab : a.eqv b) (n : Nat) :
    ((logRat a ha wa).approx n).eqv
      ((logRat b hb wb).approx n) := by
  have hy : (yOf a ha).eqv (yOf b hb) := yOf_eqv_congr ha hb hab
  exact Q'.add_eqv_congr'
    (artanhPartial_eqv_congr hy n)
    (artanhPartial_eqv_congr hy n)

/-- `logRat` depends only on the represented positive rational, not its stored
numerator/denominator presentation or proof terms. -/
theorem logRat_eqv_congr {a b : Q'}
    (ha : (0 : Q') < a + 1) (hb : (0 : Q') < b + 1)
    (wa : Q'.abs (yOf a ha) <= recipOdd 1)
    (wb : Q'.abs (yOf b hb) <= recipOdd 1)
    (hab : a.eqv b) :
    CReal.Equiv (logRat a ha wa) (logRat b hb wb) :=
  TrigAdd.equiv_of_approx_eqv
    (logRat_approx_eqv_congr ha hb wa wb hab)

end CRealLog

end YMGap.Constructive

#print axioms YMGap.Constructive.Q'.recipPos_eqv_congr
#print axioms YMGap.Constructive.Q'.pow_eqv_congr
#print axioms YMGap.Constructive.CRealLog.yOf_eqv_congr
#print axioms YMGap.Constructive.CRealLog.artanhPartial_eqv_congr
#print axioms YMGap.Constructive.CRealLog.logRat_eqv_congr
