/-
M2h -- exact physical logarithmic rates for every positive rational separator.

`PhysicalSeparatorLogRate` uses the direct artanh expression for `log(q)` and
therefore asks for `q >= 1/2`.  That window is convenient for the sharp
comparison with `(1-q)/a`, but it is not needed merely to define `-log(q)` or
prove its strict positivity.  `HamiltonianAllSep` already implements the
constructive binary range reduction

    q = 2^(-k) m,    1/2 <= m < 1,
    -log(q) = k log(2) - log(m).

This file applies that algorithm pointwise to the physical separator and then
divides by the positive physical spacing.  The result removes the global
half-window assumption from exact per-scale positivity.  It deliberately does
not claim the two-sided uniform physical rate band: transporting the quantitative
`(1-q)/a` comparison through the range reduction is a further theorem.
-/

import YMGap.Continuum.PhysicalSeparatorLogRate
import YMGap.Continuum.HamiltonianAllSep

namespace YMGap.Continuum.PhysicalSeparatorFullLogRate

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.TuranPositivity

/-! ## 1. Computable binary reduction of each physical separator -/

/-- Strict positivity of a physical separator, exposed at numerator level for
the well-founded binary search. -/
theorem separatorNum_pos (P : PhysicalSeparator) (j : Nat) :
    0 < (P.sep j).num :=
  Q'.num_pos_of_pos (P.sep_pos j)

/-- `q_j < 1` in the numerator/denominator form consumed by `binExpOf`. -/
theorem separatorNum_lt_den (P : PhysicalSeparator) (j : Nat) :
    (P.sep j).num < ((P.sep j).den : Int) := by
  have h := P.sep_lt_one j
  change (P.sep j).num * (1 : Int) <
    (1 : Int) * ((P.sep j).den : Int) at h
  simpa only [Int.mul_one, Int.one_mul] using h

/-- The computable binary exponent placing `q_j 2^k` in `[1/2,1)`. -/
def separatorBinExp (P : PhysicalSeparator) (j : Nat) : BinExpData (P.sep j) :=
  binExpOf (P.sep j) (separatorNum_pos P j) (separatorNum_lt_den P j)

/-- The reduced mantissa `m_j = q_j 2^{k_j}`. -/
def reducedMantissa (P : PhysicalSeparator) (j : Nat) : Q' :=
  mant (P.sep j) (separatorBinExp P j).k

/-- The reduced mantissa is strictly below one. -/
theorem reducedMantissa_lt_one (P : PhysicalSeparator) (j : Nat) :
    reducedMantissa P j < (1 : Q') :=
  mant_lt_one (P.sep j) (separatorBinExp P j).k
    (separatorBinExp P j).hlt

/-- The reduced mantissa plus one is positive. -/
theorem reducedMantissaPlusOne_pos (P : PhysicalSeparator) (j : Nat) :
    (0 : Q') < reducedMantissa P j + 1 :=
  mant_pos (P.sep j) (separatorBinExp P j).k (separatorNum_pos P j)

/-- The reduced mantissa lies in the direct artanh window. -/
theorem reducedMantissa_window (P : PhysicalSeparator) (j : Nat) :
    Q'.abs (yOf (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)) <=
      recipOdd 1 :=
  mant_window (P.sep j) (separatorBinExp P j) (separatorNum_pos P j)

/-! ## 2. Full-range exact logarithmic mass and physical rate -/

/-- The exact full-range transfer mass `-log(q_j)`, represented by its binary
range reduction. -/
def fullLogMass (P : PhysicalSeparator) (j : Nat) : CReal :=
  hamiltonianGapRealAll (reducedMantissa P j) (separatorBinExp P j).k
    (reducedMantissaPlusOne_pos P j) (reducedMantissa_window P j)

/-- The full-range transfer mass is constructively strictly positive for every
physical separator index, with no half-window assumption. -/
theorem fullLogMass_isPositive (P : PhysicalSeparator) (j : Nat) :
    CReal.IsPositive (fullLogMass P j) :=
  hamiltonianGapRealAll_pos
    (reducedMantissa P j) (separatorBinExp P j).k
    (reducedMantissaPlusOne_pos P j) (reducedMantissa_lt_one P j)
    (reducedMantissa_window P j)

/-- The genuine constructive logarithm range-reduction datum for `q_j`. -/
def fullLogReduction (P : PhysicalSeparator) (j : Nat) :
    CRealLogRangeReduction (CReal.ofQ' (P.sep j)) :=
  reductionOf (P.sep j) (separatorBinExp P j) (separatorNum_pos P j)

/-- The range-reduced mass is genuinely `-log(q_j)`, not merely a positive
surrogate. -/
theorem fullLogMass_equiv_neg_log (P : PhysicalSeparator) (j : Nat) :
    CReal.Equiv (fullLogMass P j)
      (CReal.neg (CReal.log (CReal.ofQ' (P.sep j)) (fullLogReduction P j))) := by
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  exact add_neg_eqv_neg_neg_add
    ((kLog2 (separatorBinExp P j).k).approx n)
    ((logRat (reducedMantissa P j) (reducedMantissaPlusOne_pos P j)
      (reducedMantissa_window P j)).approx n)

/-- The exact full-range dimensionful rate `-log(q_j)/a_j`. -/
def fullMassRate (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat) : CReal :=
  CReal.mul (fullLogMass P j) (CReal.ofQ' (reciprocalSpacing A j))

/-- Exact full-range physical rate positivity at every scale.  This is still a
per-scale statement; it does not supply a scale-independent lower bound. -/
theorem fullMassRate_posEv (P : PhysicalSeparator) (A : PhysicalSpacing)
    (j : Nat) : PosEv (fullMassRate P A j) :=
  posEv_mul (posEv_of_isPositive (fullLogMass_isPositive P j))
    (reciprocalSpacing_posEv A j)

/-! ## 3. Bundled full-range family -/

/-- A full-range exact physical logarithmic rate family.  Unlike the direct
family, its only datum beyond the physical separator is the positive spacing;
the binary logarithm reduction is computed. -/
structure FullRangeExactPhysicalLogRateFamily (P : PhysicalSeparator) : Type where
  physicalSpacing : PhysicalSpacing

namespace FullRangeExactPhysicalLogRateFamily

/-- The full-range exact mass rate carried by the family. -/
def rate {P : PhysicalSeparator} (F : FullRangeExactPhysicalLogRateFamily P)
    (j : Nat) : CReal :=
  fullMassRate P F.physicalSpacing j

/-- The computed logarithm range reduction at an indexed scale. -/
def reduction {P : PhysicalSeparator}
    (_F : FullRangeExactPhysicalLogRateFamily P) (j : Nat) :
    CRealLogRangeReduction (CReal.ofQ' (P.sep j)) :=
  fullLogReduction P j

/-- Every member of a full-range family is constructively strictly positive. -/
theorem rate_posEv {P : PhysicalSeparator}
    (F : FullRangeExactPhysicalLogRateFamily P) (j : Nat) : PosEv (F.rate j) :=
  fullMassRate_posEv P F.physicalSpacing j

end FullRangeExactPhysicalLogRateFamily

/-- Build the full-range exact family from an explicit positive spacing
sequence. -/
def fullRangeRateFamilyOfPhysicalData (P : PhysicalSeparator) (a : Nat -> Q')
    (ha : forall j : Nat, (0 : Q') < a j) :
    FullRangeExactPhysicalLogRateFamily P where
  physicalSpacing := ⟨a, ha⟩

end YMGap.Continuum.PhysicalSeparatorFullLogRate

#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.separatorNum_pos
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.separatorBinExp
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.reducedMantissa_window
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.fullLogMass_isPositive
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.fullLogReduction
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.fullLogMass_equiv_neg_log
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.fullMassRate_posEv
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogRate.FullRangeExactPhysicalLogRateFamily.rate_posEv
