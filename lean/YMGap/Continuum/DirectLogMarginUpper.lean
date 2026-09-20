/-
# Generic upper estimate for the negative rational logarithm

This is the upper counterpart to `FullLogMarginLower.rationalMargin_le_negLogRat`.
It reuses the constructive logarithm approximation estimate and identifies
the computed binary logarithm with it when q>=1/2. No physical separator is
constructed here; the original Wilson survival estimate is its consumer.
-/

import YMGap.Continuum.FullLogMarginLower
import YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow

namespace YMGap.Continuum.DirectLogMarginUpper

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.EffMassConvergence
open YMGap.Continuum.FullLogMarginLower
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow

/-- On the direct logarithm window, `-log(q)` is bounded above by the rational
margin `c94 * (1-q)` whenever `0 ≤ q ≤ 1`. -/
theorem negLogRat_le_c94_margin (q : Q') (hq0 : (0 : Q') ≤ q)
    (hq1 : q ≤ (1 : Q')) (hqplus : (0 : Q') < q + 1)
    (hwin : Q'.abs (yOf q hqplus) ≤ recipOdd 1) :
    CReal.leEv (CReal.neg (logRat q hqplus hwin))
      (CReal.ofQ' (c94 * FullLogMarginLower.rationalMargin q)) := by
  refine CReal.leEv_le_ofQ'_of_approx_le (fun n => ?_)
  change -(logRat q hqplus hwin).approx n ≤
    c94 * FullLogMarginLower.rationalMargin q
  have hqsum : (1 : Q') ≤ q + 1 := by
    exact Q'.add_le_add_right _ _ 1 hq0
  have hyabs : Q'.abs (yOf q hqplus) ≤ Q'.abs (q + -1) :=
    absYOf_le q hqplus hqsum
  have hlog := logRat_approx_abs_le q hqplus hwin n
  have hlog' : Q'.abs ((logRat q hqplus hwin).approx n) ≤
      c94 * Q'.abs (q + -1) :=
    Q'.le_trans' _ _ _ hlog
      (Q'.mul_le_mul_of_nonneg_left _ _ c94 hyabs (by decide : (0 : Q') ≤ c94))
  have hmargin : (Q'.abs (q + -1)).eqv
      (FullLogMarginLower.rationalMargin q) := by
    have hneg : (q + -1).eqv
        (-FullLogMarginLower.rationalMargin q) := by
      unfold FullLogMarginLower.rationalMargin
      refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-q)) ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (-1) (-(-q)) q (Q'.neg_neg_eqv q)) ?_
      exact Q'.add_comm_eqv (-1) q
    refine Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hneg) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.abs_neg' (FullLogMarginLower.rationalMargin q)) ?_
    exact Q'.eqv_of_eq (TrigAdd.abs_of_nonneg (Q'.sub_nonneg_of_le hq1))
  have hlog'' : Q'.abs ((logRat q hqplus hwin).approx n) ≤
      c94 * FullLogMarginLower.rationalMargin q :=
    Q'.le_trans' _ _ _ hlog' (Q'.mul_le_mul_of_nonneg_left _ _ c94
      (Q'.le_of_eqv hmargin) (by decide : (0 : Q') ≤ c94))
  exact Q'.le_trans' _ _ _ (Q'.neg_le_abs _) hlog''

/-! The same upper estimate after the binary full-range representation has
stopped at exponent zero.  The statement is still generic in `q`; no physical
separator or Wilson observable is introduced. -/

/-- A half-window full-range Hamiltonian mass is bounded by the direct margin. -/
theorem binaryMass_le_c94_margin (q : Q') (hnum : 0 < q.num)
    (hlt : q.num < (q.den : Int)) (hhalf : HalfPow.half ≤ q) :
    CReal.leEv
      (hamiltonianGapRealAll (mant q (binExpOf q hnum hlt).k)
        (binExpOf q hnum hlt).k
        (mant_pos q (binExpOf q hnum hlt).k hnum)
        (mant_window q (binExpOf q hnum hlt) hnum))
      (CReal.ofQ' (c94 * FullLogMarginLower.rationalMargin q)) := by
  have hhalfInt : (q.den : Int) ≤ q.num * 2 := by
    unfold HalfPow.half at hhalf
    change (1 : Int) * (q.den : Int) ≤ q.num * (2 : Int) at hhalf
    simpa only [Int.one_mul] using hhalf
  have hk : (binExpOf q hnum hlt).k = 0 :=
    binExpOf_k_eq_zero_of_half q hnum hlt hhalfInt
  have hqpos : (0 : Q') < q := CReal.pos_of_num_pos hnum
  have hqplus : (0 : Q') < q + 1 :=
    Q'.add_pos hqpos (by decide : (0 : Q') < 1)
  have hq1 : q ≤ (1 : Q') := by
    change q.num * (1 : Int) ≤ (1 : Int) * (q.den : Int)
    exact Int.le_of_lt (by simpa only [Int.mul_one, Int.one_mul] using hlt)
  have hwin : Q'.abs (yOf q hqplus) ≤ recipOdd 1 := by
    apply window_neg q hqplus
      (by
        change q.num * (1 : Int) < (1 : Int) * (q.den : Int)
        simpa only [Int.mul_one, Int.one_mul] using hlt)
      hhalfInt
  have hequiv : CReal.Equiv
      (hamiltonianGapRealAll (mant q (binExpOf q hnum hlt).k)
        (binExpOf q hnum hlt).k
        (mant_pos q (binExpOf q hnum hlt).k hnum)
        (mant_window q (binExpOf q hnum hlt) hnum))
      (CReal.neg (logRat q hqplus hwin)) := by
    refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
    have hklog : ((kLog2 (binExpOf q hnum hlt).k).approx n).eqv 0 := by
      rw [hk]
      exact Q'.eqv_refl 0
    have hmant : (mant q (binExpOf q hnum hlt).k).eqv q := by
      rw [hk]
      exact Q'.mul_one_eqv q
    have hlog := logRat_approx_eqv_congr
      (mant_pos q (binExpOf q hnum hlt).k hnum) hqplus
      (mant_window q (binExpOf q hnum hlt) hnum) hwin hmant n
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hklog (Q'.neg_eqv_congr _ _ hlog))
      (Q'.eqv_of_eq (Q'.zero_add' _))
  exact CReal.leEv_trans (CReal.leEv_of_equiv hequiv)
    (negLogRat_le_c94_margin q (Q'.le_of_lt hqpos) hq1 hqplus hwin)

#print axioms YMGap.Continuum.DirectLogMarginUpper.negLogRat_le_c94_margin
#print axioms YMGap.Continuum.DirectLogMarginUpper.binaryMass_le_c94_margin

end YMGap.Continuum.DirectLogMarginUpper
