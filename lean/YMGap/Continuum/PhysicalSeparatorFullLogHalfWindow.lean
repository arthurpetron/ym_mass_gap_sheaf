/-
M2n -- agreement of the binary full-range logarithm with the direct artanh
logarithm on the half-window.

For `q >= 1/2`, the well-founded binary search must stop at its initial
exponent `k = 0`.  The resulting mantissa is represented as `q * 1`; the
representation-invariance theorem for `logRat` then identifies the computed
full-range logarithm with the direct logarithm.
-/

import YMGap.Continuum.PhysicalSeparatorFullLogRate
import YMGap.Continuum.PhysicalSeparatorHalfWindow
import YMGap.Constructive.CRealLogRatCongruence
import YMGap.Continuum.FullLogRateCeilingGlue

namespace YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorHalfWindow
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

/-! ## 1. The binary search stops at zero in the half-window -/

/-- If `q >= 1/2`, the computable exponent selected by `binExpOf` is zero. -/
theorem binExpOf_k_eq_zero_of_half (q : Q')
    (hnum : 0 < q.num) (hlt : q.num < (q.den : Int))
    (hhalf : (q.den : Int) <= q.num * 2) :
    (binExpOf q hnum hlt).k = 0 := by
  have hcast : ((q.num.toNat : Nat) : Int) = q.num :=
    Int.toNat_of_nonneg (Int.le_of_lt hnum)
  have hltInt : ((q.num.toNat : Nat) : Int) < (q.den : Int) := by
    simpa only [hcast] using hlt
  have hltNat : q.num.toNat < q.den := by
    exact_mod_cast hltInt
  have hhalfInt :
      ((q.den : Nat) : Int) <= ((q.num.toNat * 2 : Nat) : Int) := by
    simpa only [Int.natCast_mul, hcast] using hhalf
  have hhalfNat : q.den <= q.num.toNat * 2 := by
    exact_mod_cast hhalfInt
  have hstop : q.den <= q.num.toNat * 2 ^ (0 + 1) := by
    simpa only [Nat.zero_add, Nat.pow_one] using hhalfNat
  change (searchBin q.num.toNat q.den (by omega) 0 (by simpa using hltNat)).1 = 0
  rw [searchBin]
  rw [dif_pos hstop]

/-- Pointwise half-window bound in the integer form consumed by the binary
search and the negative-branch artanh theorem. -/
theorem denominator_le_twice_numerator_of_half
    (P : PhysicalSeparator) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    (P.sep j).den <= (P.sep j).num * 2 := by
  unfold HalfPow.half at hhalf
  change (1 : Int) * ((P.sep j).den : Int) <=
    (P.sep j).num * (2 : Int) at hhalf
  simpa only [Int.one_mul] using hhalf

/-- The physical separator's computed binary exponent is zero at every index
which lies in the half-window. -/
theorem separatorBinExp_k_eq_zero_of_half
    (P : PhysicalSeparator) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    (separatorBinExp P j).k = 0 :=
  binExpOf_k_eq_zero_of_half (P.sep j)
    (separatorNum_pos P j) (separatorNum_lt_den P j)
    (denominator_le_twice_numerator_of_half P j hhalf)

/-! ## 2. Pointwise direct logarithm and representation agreement -/

/-- Direct artanh-window certificate at a single half-window index. -/
def directWindowAt (P : PhysicalSeparator) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    Q'.abs (yOf (P.sep j) (separatorPlusOne_pos P j)) <= recipOdd 1 :=
  window_neg (P.sep j) (separatorPlusOne_pos P j) (P.sep_lt_one j)
    (denominator_le_twice_numerator_of_half P j hhalf)

/-- The direct logarithmic mass at one half-window index. -/
def directLogMassAt (P : PhysicalSeparator) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) : CReal :=
  CReal.neg (logRat (P.sep j) (separatorPlusOne_pos P j)
    (directWindowAt P j hhalf))

/-- At exponent zero, the binary mantissa `q * 1` represents the original
separator `q`. -/
theorem reducedMantissa_eqv_sep_of_half
    (P : PhysicalSeparator) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    (reducedMantissa P j).eqv (P.sep j) := by
  unfold reducedMantissa
  rw [separatorBinExp_k_eq_zero_of_half P j hhalf]
  change (P.sep j * (1 : Q')).eqv (P.sep j)
  exact Q'.mul_one_eqv (P.sep j)

/-- Strong pointwise agreement of the binary full-range mass with the direct
artanh mass on the half-window. -/
theorem fullLogMass_approx_eqv_directLogMassAt
    (P : PhysicalSeparator) (j n : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    ((fullLogMass P j).approx n).eqv
      ((directLogMassAt P j hhalf).approx n) := by
  have hk : (separatorBinExp P j).k = 0 :=
    separatorBinExp_k_eq_zero_of_half P j hhalf
  have hklog : ((kLog2 (separatorBinExp P j).k).approx n).eqv 0 := by
    rw [hk]
    exact Q'.eqv_refl 0
  have hlog :
      ((logRat (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)
        (reducedMantissa_window P j)).approx n).eqv
      ((logRat (P.sep j) (separatorPlusOne_pos P j)
        (directWindowAt P j hhalf)).approx n) :=
    logRat_approx_eqv_congr
      (reducedMantissaPlusOne_pos P j) (separatorPlusOne_pos P j)
      (reducedMantissa_window P j) (directWindowAt P j hhalf)
      (reducedMantissa_eqv_sep_of_half P j hhalf) n
  change
    ((kLog2 (separatorBinExp P j).k).approx n +
      -((logRat (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)
        (reducedMantissa_window P j)).approx n)).eqv
      (-((logRat (P.sep j) (separatorPlusOne_pos P j)
        (directWindowAt P j hhalf)).approx n))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hklog
      (Q'.neg_eqv_congr _ _ hlog)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- CReal-level agreement of the two exact logarithm presentations on the
half-window. -/
theorem fullLogMass_equiv_directLogMassAt
    (P : PhysicalSeparator) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    CReal.Equiv (fullLogMass P j) (directLogMassAt P j hhalf) :=
  TrigAdd.equiv_of_approx_eqv
    (fun n => fullLogMass_approx_eqv_directLogMassAt P j n hhalf)

/-! ## 3. The direct upper estimate transported to the full-range rate -/

/-- The pointwise direct logarithm satisfies the same explicit `9/4` margin
bound as the globally bundled direct-window logarithm. -/
theorem directLogMassAt_le_c94_margin
    (P : PhysicalSeparator) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    CReal.leEv (directLogMassAt P j hhalf)
      (CReal.ofQ' (EffMassConvergence.c94 * P.physMargin j)) := by
  have hsepNonnegative : (0 : Q') <= P.sep j := P.sep_nonneg j
  have hsepOne : (1 : Q') <= P.sep j + 1 := by
    have h := Q'.add_le_add_left 1 0 (P.sep j) hsepNonnegative
    rw [Q'.add_zero'] at h
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_comm_eqv 1 (P.sep j)))
  refine CReal.leEv_le_ofQ'_of_approx_le (fun n => ?_)
  show
    -((logRat (P.sep j) (separatorPlusOne_pos P j)
      (directWindowAt P j hhalf)).approx n) <=
      EffMassConvergence.c94 * P.physMargin j
  have hnegAbs :
      -((logRat (P.sep j) (separatorPlusOne_pos P j)
        (directWindowAt P j hhalf)).approx n) <=
        Q'.abs (-((logRat (P.sep j) (separatorPlusOne_pos P j)
          (directWindowAt P j hhalf)).approx n)) :=
    Q'.le_abs_self _
  have habsNeg :
      Q'.abs (-((logRat (P.sep j) (separatorPlusOne_pos P j)
        (directWindowAt P j hhalf)).approx n)) <=
        Q'.abs ((logRat (P.sep j) (separatorPlusOne_pos P j)
          (directWindowAt P j hhalf)).approx n) :=
    Q'.le_of_eqv (Q'.abs_neg' _)
  have hlog := EffMassConvergence.logRat_approx_abs_le
    (P.sep j) (separatorPlusOne_pos P j) (directWindowAt P j hhalf) n
  have hy := EffMassConvergence.absYOf_le
    (P.sep j) (separatorPlusOne_pos P j) hsepOne
  have hscale :
      EffMassConvergence.c94 *
          Q'.abs (yOf (P.sep j) (separatorPlusOne_pos P j)) <=
        EffMassConvergence.c94 * Q'.abs (P.sep j + -1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ EffMassConvergence.c94 hy (by decide)
  have hmargin :
      EffMassConvergence.c94 * Q'.abs (P.sep j + -1) <=
        EffMassConvergence.c94 * P.physMargin j :=
    Q'.mul_le_mul_of_nonneg_left _ _ EffMassConvergence.c94
      (Q'.le_of_eqv (abs_sep_sub_one_eqv_margin P j)) (by decide)
  exact Q'.le_trans' _ _ _ hnegAbs
    (Q'.le_trans' _ _ _ habsNeg
      (Q'.le_trans' _ _ _ hlog
        (Q'.le_trans' _ _ _ hscale hmargin)))

/-- Direct dimensionful rate at a single half-window index. -/
def directMassRateAt (P : PhysicalSeparator) (A : PhysicalSpacing)
    (j : Nat) (hhalf : HalfPow.half <= P.sep j) : CReal :=
  CReal.mul (directLogMassAt P j hhalf)
    (CReal.ofQ' (reciprocalSpacing A j))

/-- Strong pointwise agreement of the full and direct physical rates on a
half-window index. -/
theorem fullMassRate_approx_eqv_directMassRateAt
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j n : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    ((fullMassRate P A j).approx n).eqv
      ((directMassRateAt P A j hhalf).approx n) :=
  Q'.mul_eqv_congr_right
    ((fullLogMass P j).approx n) ((directLogMassAt P j hhalf).approx n)
    (reciprocalSpacing A j)
    (fullLogMass_approx_eqv_directLogMassAt P j n hhalf)

/-- CReal-level agreement of full and direct physical rates on the
half-window. -/
theorem fullMassRate_equiv_directMassRateAt
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    CReal.Equiv (fullMassRate P A j) (directMassRateAt P A j hhalf) :=
  TrigAdd.equiv_of_approx_eqv
    (fun n => fullMassRate_approx_eqv_directMassRateAt P A j n hhalf)

/-- Scaling the pointwise direct-log estimate by positive reciprocal spacing
gives the direct physical-rate estimate. -/
theorem directMassRateAt_le_c94_marginRate
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    CReal.leEv (directMassRateAt P A j hhalf)
      (CReal.ofQ' (EffMassConvergence.c94 * marginRate P A j)) := by
  have hscaled := CReal.leEv_smul_nonneg
    (Q'.le_of_lt (reciprocalSpacing_pos A j))
    (directLogMassAt_le_c94_margin P j hhalf)
  have hleft :
      CReal.Equiv (directMassRateAt P A j hhalf)
        (CReal.mul (CReal.ofQ' (reciprocalSpacing A j))
          (directLogMassAt P j hhalf)) :=
    CRealAlg.cmul_comm (directLogMassAt P j hhalf)
      (CReal.ofQ' (reciprocalSpacing A j))
  have hright :
      CReal.Equiv (CReal.ofQ' (EffMassConvergence.c94 * marginRate P A j))
        (CReal.mul (CReal.ofQ' (reciprocalSpacing A j))
          (CReal.ofQ' (EffMassConvergence.c94 * P.physMargin j))) := by
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    unfold marginRate reciprocalSpacing Q'.divPos
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv EffMassConvergence.c94
        (P.physMargin j)
        (Q'.recipPos (A.spacing j) (A.spacing_pos j)))) ?_
    exact Q'.mul_comm_eqv
      (EffMassConvergence.c94 * P.physMargin j)
      (Q'.recipPos (A.spacing j) (A.spacing_pos j))
  exact (CReal.leEv_congr hleft hright).mpr hscaled

/-- **Full-range half-window upper comparison.**  At any index with
`q_j >= 1/2`, the computed binary logarithmic rate inherits the direct
`9/4` margin-rate bound. -/
theorem fullMassRate_le_c94_marginRate_of_half
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    CReal.leEv (fullMassRate P A j)
      (CReal.ofQ' (EffMassConvergence.c94 * marginRate P A j)) :=
  (CReal.leEv_congr
    (fullMassRate_equiv_directMassRateAt P A j hhalf)
    (CReal.Equiv.refl _)).mpr
      (directMassRateAt_le_c94_marginRate P A j hhalf)

/-! ## 4. Eventual half-window tail certificates -/

/-- A separator enters the direct half-window from a named scale onward. -/
structure EventualSeparatorHalfWindow
    (P : PhysicalSeparator) (start : Nat) : Type where
  sep_ge_half : forall j : Nat, start <= j -> HalfPow.half <= P.sep j

/-- An independent rational margin-rate ceiling on the same tail. -/
structure TailMarginRateCeiling
    (P : PhysicalSeparator) (A : PhysicalSpacing) (start : Nat) : Type where
  ceiling : Q'
  margin_bound : forall j : Nat, start <= j ->
    marginRate P A j <= ceiling

/-- An eventual half-window and rational tail margin ceiling construct the
exact full-range logarithmic tail ceiling. -/
def exactTailCeilingOfEventualHalfWindow
    (P : PhysicalSeparator) (A : PhysicalSpacing) (start : Nat)
    (H : EventualSeparatorHalfWindow P start)
    (U : TailMarginRateCeiling P A start) :
    TailFullRangeLogRateCeiling
      (fullRangeRateFamilyOfPhysicalData P A.spacing A.spacing_pos) start where
  ceiling := EffMassConvergence.c94 * U.ceiling
  tail_bound := fun j hj => by
    have hexact := fullMassRate_le_c94_marginRate_of_half
      P A j (H.sep_ge_half j hj)
    have hscaled :
        EffMassConvergence.c94 * marginRate P A j <=
          EffMassConvergence.c94 * U.ceiling :=
      Q'.mul_le_mul_of_nonneg_left _ _ EffMassConvergence.c94
        (U.margin_bound j hj) (by decide)
    have hconstants :
        CReal.leEv
          (CReal.ofQ' (EffMassConvergence.c94 * marginRate P A j))
          (CReal.ofQ' (EffMassConvergence.c94 * U.ceiling)) :=
      CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hscaled)
    exact CReal.leEv_trans hexact hconstants

/-- A finite exact prefix plus the eventual half-window tail data yield the
single global exact-rate ceiling. -/
def globalExactCeilingOfPrefixEventualHalfWindow
    (P : PhysicalSeparator) (A : PhysicalSpacing) (start : Nat)
    (pre : PrefixFullRangeLogRateCeiling
      (fullRangeRateFamilyOfPhysicalData P A.spacing A.spacing_pos) start)
    (H : EventualSeparatorHalfWindow P start)
    (U : TailMarginRateCeiling P A start) :
    FullRangeLogRateCeiling
      (fullRangeRateFamilyOfPhysicalData P A.spacing A.spacing_pos) :=
  pre.glue (exactTailCeilingOfEventualHalfWindow P A start H U)

@[simp] theorem globalExactCeiling_ceiling
    (P : PhysicalSeparator) (A : PhysicalSpacing) (start : Nat)
    (pre : PrefixFullRangeLogRateCeiling
      (fullRangeRateFamilyOfPhysicalData P A.spacing A.spacing_pos) start)
    (H : EventualSeparatorHalfWindow P start)
    (U : TailMarginRateCeiling P A start) :
    (globalExactCeilingOfPrefixEventualHalfWindow P A start pre H U).ceiling =
      Q'.max' pre.ceiling (EffMassConvergence.c94 * U.ceiling) := rfl

end YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow

#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.binExpOf_k_eq_zero_of_half
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.separatorBinExp_k_eq_zero_of_half
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.reducedMantissa_eqv_sep_of_half
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.fullLogMass_equiv_directLogMassAt
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.directLogMassAt_le_c94_margin
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.fullMassRate_equiv_directMassRateAt
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.fullMassRate_le_c94_marginRate_of_half
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.exactTailCeilingOfEventualHalfWindow
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow.globalExactCeilingOfPrefixEventualHalfWindow
