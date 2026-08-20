/-
Computed approximation-index regularity for the exact full logarithmic rate.

The exact rate at cutoff `j` is built from a finite binary range reduction,
the constructive `artanh` series, finite addition/negation, and multiplication
by the positive rational `1/a_j`.  Every one of those operations now has a
Type-level inner-modulus constructor, so the per-cutoff `CReal` regularity is
computed here rather than carried as an analytic residual.

This file does not compare different cutoffs.  The two-sided physical estimate
between rates at `j` and `j+1` remains a separate Yang--Mills input.
-/

import YMGap.Constructive.CRealLogInnerRegularity
import YMGap.Continuum.PhysicalSeparatorFullLogRate

namespace YMGap.Continuum.FullLogRateInnerRegularity

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogRate

/-- The finite sum `k * log 2` has a computed inner modulus, obtained by
recursion through pointwise constructive-real addition. -/
def kLog2InnerRegularity : forall k : Nat,
    CReal.InnerRegularity (kLog2 k)
  | 0 => CReal.InnerRegularity.ofQ' 0
  | k + 1 => CReal.InnerRegularity.add log2InnerRegularity
      (kLog2InnerRegularity k)

/-- The binary range-reduced Hamiltonian logarithmic gap has a computed inner
modulus for every rational mantissa in the artanh window. -/
def hamiltonianGapRealAllInnerRegularity
    (m : Q') (k : Nat) (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) <= recipOdd 1) :
    CReal.InnerRegularity (hamiltonianGapRealAll m k hm1 hyb) :=
  CReal.InnerRegularity.add (kLog2InnerRegularity k)
    (CReal.InnerRegularity.neg (logRatInnerRegularity m hm1 hyb))

/-- The exact full-range transfer mass at one physical cutoff has a computed
inner modulus. -/
def fullLogMassInnerRegularity (P : PhysicalSeparator) (j : Nat) :
    CReal.InnerRegularity (fullLogMass P j) :=
  hamiltonianGapRealAllInnerRegularity
    (reducedMantissa P j) (separatorBinExp P j).k
    (reducedMantissaPlusOne_pos P j) (reducedMantissa_window P j)

/-- The exact dimensionful rate `-log(q_j)/a_j` has a computed Type-level
approximation-index modulus. -/
def fullMassRateInnerRegularity
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat) :
    CReal.InnerRegularity (fullMassRate P A j) :=
  CReal.InnerRegularity.scaleRight (fullLogMassInnerRegularity P j)
    (reciprocalSpacing A j) (Q'.le_of_lt (reciprocalSpacing_pos A j))

end YMGap.Continuum.FullLogRateInnerRegularity

#print axioms YMGap.Continuum.FullLogRateInnerRegularity.kLog2InnerRegularity
#print axioms YMGap.Continuum.FullLogRateInnerRegularity.hamiltonianGapRealAllInnerRegularity
#print axioms YMGap.Continuum.FullLogRateInnerRegularity.fullLogMassInnerRegularity
#print axioms YMGap.Continuum.FullLogRateInnerRegularity.fullMassRateInnerRegularity
