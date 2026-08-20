/-
M2i -- quantitative lower ingredients for the full binary logarithm reduction.

This module extracts the direct-window inequality `1-q <= -log(q)` from the
physical-separator-specific presentation and proves the fixed lower estimate
`1/2 <= log(2)`.  These are the two analytic ingredients needed to transport
the rational margin floor through `HamiltonianAllSep` when `q < 1/2`.

No physical separator or uniform rate bound is constructed here; all statements
are generic constructive inequalities for positive rationals.
-/

import YMGap.Continuum.PhysicalSeparatorFullLogRate
import YMGap.Continuum.HamiltonianScalar

namespace YMGap.Continuum.FullLogMarginLower

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.HamiltonianAllSep

/-! ## 1. Generic direct-window inequality -/

/-- Rational transfer margin `1-q`. -/
def rationalMargin (q : Q') : Q' := (1 : Q') - q

/-- The transfer margin is positive when `q < 1`. -/
theorem rationalMargin_pos (q : Q') (hq1 : q < (1 : Q')) :
    (0 : Q') < rationalMargin q :=
  one_sub_pos_of_lt_one hq1

/-- The rational margin is bounded by the first doubled artanh term. -/
theorem rationalMargin_le_neg_two_y (q : Q')
    (hq0 : (0 : Q') <= q) (hq1 : q < (1 : Q'))
    (hqplus : (0 : Q') < q + 1) :
    rationalMargin q <=
      -(term (yOf q hqplus) 0 + term (yOf q hqplus) 0) := by
  have hdpos : (0 : Q') < rationalMargin q := rationalMargin_pos q hq1
  have hdnonneg : (0 : Q') <= rationalMargin q := Q'.le_of_lt hdpos
  have hqTwo : q + 1 <= (2 : Q') := by
    exact Q'.add_le_add_right _ _ 1 (Q'.le_of_lt hq1)
  have hrecip :
      Q'.recipPos (2 : Q') (by decide) <= Q'.recipPos (q + 1) hqplus :=
    ArtanhMonotone.recipPos_antitone (q + 1) (2 : Q')
      hqplus (by decide) hqTwo
  have hmul :
      rationalMargin q * Q'.recipPos (2 : Q') (by decide) <=
        rationalMargin q * Q'.recipPos (q + 1) hqplus :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrecip hdnonneg
  have hsum :
      rationalMargin q * Q'.recipPos (2 : Q') (by decide)
          + rationalMargin q * Q'.recipPos (2 : Q') (by decide) <=
        rationalMargin q * Q'.recipPos (q + 1) hqplus
          + rationalMargin q * Q'.recipPos (q + 1) hqplus :=
    Q'.add_le_add hmul hmul
  have htwo :
      (Q'.recipPos (2 : Q') (by decide) +
        Q'.recipPos (2 : Q') (by decide)).eqv 1 := by
    decide
  have hmarginEq :
      (rationalMargin q).eqv
        (rationalMargin q * Q'.recipPos (2 : Q') (by decide)
          + rationalMargin q * Q'.recipPos (2 : Q') (by decide)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv (rationalMargin q))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (rationalMargin q) 1
        (Q'.recipPos (2 : Q') (by decide) + Q'.recipPos (2 : Q') (by decide))
        (Q'.eqv_symm htwo)) ?_
    exact Q'.mul_add_eqv (rationalMargin q)
      (Q'.recipPos (2 : Q') (by decide)) (Q'.recipPos (2 : Q') (by decide))
  have hmarginSum :
      rationalMargin q <=
        rationalMargin q * Q'.recipPos (q + 1) hqplus
          + rationalMargin q * Q'.recipPos (q + 1) hqplus :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hmarginEq) hsum
  have hnum : (q + -1).eqv (-(rationalMargin q)) := by
    unfold rationalMargin
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-q)) ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) (-(-q)) q (Q'.neg_neg_eqv q)) ?_
    exact Q'.add_comm_eqv (-1) q
  have hy :
      (yOf q hqplus).eqv
        (-(rationalMargin q * Q'.recipPos (q + 1) hqplus)) := by
    show ((q + -1) * Q'.recipPos (q + 1) hqplus).eqv _
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (q + -1) (-(rationalMargin q))
        (Q'.recipPos (q + 1) hqplus) hnum) ?_
    exact Q'.neg_mul_eqv (rationalMargin q) (Q'.recipPos (q + 1) hqplus)
  have hterm := term_zero_eqv_self (yOf q hqplus)
  have htarget :
      (-(term (yOf q hqplus) 0 + term (yOf q hqplus) 0)).eqv
        (rationalMargin q * Q'.recipPos (q + 1) hqplus
          + rationalMargin q * Q'.recipPos (q + 1) hqplus) := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hterm hterm)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hy hy)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv
        (-(rationalMargin q * Q'.recipPos (q + 1) hqplus))
        (-(rationalMargin q * Q'.recipPos (q + 1) hqplus))) ?_
    exact Q'.add_eqv_congr'
      (Q'.neg_neg_eqv (rationalMargin q * Q'.recipPos (q + 1) hqplus))
      (Q'.neg_neg_eqv (rationalMargin q * Q'.recipPos (q + 1) hqplus))
  exact Q'.le_trans' _ _ _ hmarginSum (Q'.ge_of_eqv htarget)

/-- Generic direct-window inequality `1-q <= -log(q)`. -/
theorem rationalMargin_le_negLogRat (q : Q')
    (hq0 : (0 : Q') <= q) (hq1 : q < (1 : Q'))
    (hqplus : (0 : Q') < q + 1)
    (hwin : Q'.abs (yOf q hqplus) <= recipOdd 1) :
    CReal.leEv (CReal.ofQ' (rationalMargin q))
      (CReal.neg (logRat q hqplus hwin)) := by
  have hyneg : yOf q hqplus <= (0 : Q') :=
    Q'.le_of_lt (YMGap.Continuum.yOf_sep_neg q hqplus hq1)
  have hlog := logRat_leRat_of_arg_nonpos q hqplus hwin hyneg
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hlog epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  show rationalMargin q <= -(logRat q hqplus hwin).approx n + epsilon
  exact Q'.le_trans' _ _ _
    (rationalMargin_le_neg_two_y q hq0 hq1 hqplus)
    (Q'.neg_le_neg_add (hN n hn))

/-! ## 2. A constructive fixed lower bound for `log 2` -/

/-- The first doubled artanh term for `log(2)` dominates `1/2`. -/
theorem half_le_log2 :
    CReal.leEv (CReal.ofQ' HalfPow.half) log2 := by
  intro epsilon hepsilon
  refine ⟨1, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ k =>
      show HalfPow.half <= log2.approx (k + 1) + epsilon
      have hmono := partialSum_mono_of_nonneg
        (yOf (2 : Q') (by decide)) yOf_two_nonneg 1 k
      have hone :
          partialSum (yOf (2 : Q') (by decide)) 1 =
            term (yOf (2 : Q') (by decide)) 0 := by
        rw [partialSum_succ, partialSum_zero, Q'.zero_add']
      rw [hone] at hmono
      have hterm :
          HalfPow.half <=
            term (yOf (2 : Q') (by decide)) 0 +
              term (yOf (2 : Q') (by decide)) 0 := by
        decide
      have hsum := Q'.add_le_add hmono hmono
      have hbase :
          HalfPow.half <=
            partialSum (yOf (2 : Q') (by decide)) (1 + k) +
              partialSum (yOf (2 : Q') (by decide)) (1 + k) :=
        Q'.le_trans' _ _ _ hterm hsum
      have hidx : 1 + k = k + 1 := by omega
      rw [hidx] at hbase
      exact Q'.le_trans' _ _ _ hbase
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-- `k/2`, represented recursively so its addition structure matches `kLog2`. -/
def binaryHalfLower : Nat -> Q'
  | 0 => 0
  | k + 1 => HalfPow.half + binaryHalfLower k

/-- The accumulated binary contribution satisfies `k/2 <= k log(2)`. -/
theorem binaryHalfLower_le_kLog2 (k : Nat) :
    CReal.leEv (CReal.ofQ' (binaryHalfLower k)) (kLog2 k) := by
  induction k with
  | zero => exact CReal.leEv_refl _
  | succ k ih =>
      change CReal.leEv
        (CReal.add (CReal.ofQ' HalfPow.half)
          (CReal.ofQ' (binaryHalfLower k)))
        (CReal.add log2 (kLog2 k))
      exact CReal.leEv_add half_le_log2 ih

/-! ## 3. The rational inequality carried by binary reduction -/

/-- The recursive binary lower bound is nonnegative. -/
theorem binaryHalfLower_nonnegative (k : Nat) :
    (0 : Q') <= binaryHalfLower k := by
  induction k with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      exact Q'.zero_le_add HalfPow.half (binaryHalfLower k)
        (Q'.le_of_lt (by decide)) ih

/-- Two or more binary steps contribute at least one. -/
theorem one_le_binaryHalfLower_two_add (k : Nat) :
    (1 : Q') <= binaryHalfLower (k + 2) := by
  change (1 : Q') <= HalfPow.half +
    (HalfPow.half + binaryHalfLower k)
  have hrest := binaryHalfLower_nonnegative k
  have hadd : (1 : Q') <= (1 : Q') + binaryHalfLower k :=
    Q'.add_le_self_of_nonneg 1 (binaryHalfLower k) hrest
  have heq :
      (HalfPow.half + (HalfPow.half + binaryHalfLower k)).eqv
        ((1 : Q') + binaryHalfLower k) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv HalfPow.half HalfPow.half
        (binaryHalfLower k))) ?_
    exact Q'.add_eqv_congr_right
      (HalfPow.half + HalfPow.half) 1 (binaryHalfLower k)
      (ExpNeg.two_halves 1)
  exact Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv heq)

/-- A nonnegative `q` has transfer margin at most one. -/
theorem rationalMargin_le_one (q : Q') (hq0 : (0 : Q') <= q) :
    rationalMargin q <= (1 : Q') := by
  have hneg : -q <= -(0 : Q') := Q'.neg_le_neg hq0
  have hadd := Q'.add_le_add_left 1 (-q) (-(0 : Q')) hneg
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 (-(0 : Q')) 0 (by decide)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' 1)))

/-- The zero-exponent mantissa is equivalent to the original rational. -/
theorem mant_zero_eqv (q : Q') : (mant q 0).eqv q := by
  unfold mant
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q (Q'.ofNat (2 ^ 0)) 1 (by decide))
    (Q'.mul_one_eqv q)

/-- The one-exponent mantissa is equivalent to `q+q`. -/
theorem mant_one_eqv_double (q : Q') : (mant q 1).eqv (q + q) := by
  unfold mant
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q (Q'.ofNat (2 ^ 1)) ((1 : Q') + 1) (by decide)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv q 1 1) ?_
  exact Q'.add_eqv_congr' (Q'.mul_one_eqv q) (Q'.mul_one_eqv q)

/-- In the one-step branch, the binary half plus the mantissa margin is the
original margin plus the nonnegative remainder `1/2-q`. -/
theorem half_add_doubleMargin_eqv (q : Q') :
    (HalfPow.half + rationalMargin (mant q 1)).eqv
      (rationalMargin q + (HalfPow.half + -q)) := by
  have hm := mant_one_eqv_double q
  unfold rationalMargin
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left HalfPow.half
      (1 + -(mant q 1)) (1 + -(q + q))
      (Q'.add_eqv_congr_left 1 (-(mant q 1)) (-(q + q))
        (Q'.neg_eqv_congr _ _ hm))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left HalfPow.half
      (1 + -(q + q)) (1 + (-q + -q))
      (Q'.add_eqv_congr_left 1 (-(q + q)) (-q + -q)
        (Q'.neg_add_eqv q q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv HalfPow.half 1 (-q + -q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner HalfPow.half 1 (-q) (-q)) ?_
  exact Q'.add_comm_eqv (HalfPow.half + -q) (1 + -q)

/-- The purely rational core of the global logarithm comparison.  For the
computed binary exponent, the original margin is paid by `k/2` plus the direct
mantissa margin. -/
theorem rationalMargin_le_binaryHalf_add_mantMargin
    (q : Q') (hq0 : (0 : Q') <= q) (be : BinExpData q) :
    rationalMargin q <=
      binaryHalfLower be.k + rationalMargin (mant q be.k) := by
  cases hk : be.k with
  | zero =>
      have hm : (rationalMargin (mant q 0)).eqv (rationalMargin q) := by
        unfold rationalMargin
        exact Q'.add_eqv_congr_left 1 (-(mant q 0)) (-q)
          (Q'.neg_eqv_congr _ _ (mant_zero_eqv q))
      have hrhs :
          (binaryHalfLower 0 + rationalMargin (mant q 0)).eqv
            (rationalMargin q) := by
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.zero_add' (rationalMargin (mant q 0)))) hm
      exact Q'.ge_of_eqv hrhs
  | succ k =>
      cases k with
      | zero =>
          have hqhalf : q <= HalfPow.half := by
            show q.num * (HalfPow.half.den : Int) <=
              HalfPow.half.num * (q.den : Int)
            unfold HalfPow.half
            rw [Q'.mkPos_num, Q'.mkPos_den]
            have hlt := be.hlt
            rw [hk] at hlt
            change q.num * (2 : Int) < (q.den : Int) at hlt
            omega
          have hrem : (0 : Q') <= HalfPow.half + -q :=
            Q'.sub_nonneg_of_le hqhalf
          have hadd :
              rationalMargin q <=
                rationalMargin q + (HalfPow.half + -q) :=
            Q'.add_le_self_of_nonneg _ _ hrem
          have hrhs :
              (binaryHalfLower 1 + rationalMargin (mant q 1)).eqv
                (rationalMargin q + (HalfPow.half + -q)) :=
            half_add_doubleMargin_eqv q
          exact Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hrhs)
      | succ k =>
          have hmargin : rationalMargin q <= (1 : Q') :=
            rationalMargin_le_one q hq0
          have hbin : (1 : Q') <= binaryHalfLower (k + 2) :=
            one_le_binaryHalfLower_two_add k
          have hmm : (0 : Q') <= rationalMargin (mant q (k + 2)) :=
            Q'.le_of_lt (rationalMargin_pos (mant q (k + 2))
              (mant_lt_one q (k + 2) (by simpa [hk] using be.hlt)))
          exact Q'.le_trans' _ _ _ hmargin
            (Q'.le_trans' _ _ _ hbin
              (Q'.add_le_self_of_nonneg _ _ hmm))

end YMGap.Continuum.FullLogMarginLower

#print axioms YMGap.Continuum.FullLogMarginLower.rationalMargin_le_neg_two_y
#print axioms YMGap.Continuum.FullLogMarginLower.rationalMargin_le_negLogRat
#print axioms YMGap.Continuum.FullLogMarginLower.half_le_log2
#print axioms YMGap.Continuum.FullLogMarginLower.binaryHalfLower_le_kLog2
#print axioms YMGap.Continuum.FullLogMarginLower.rationalMargin_le_binaryHalf_add_mantMargin
