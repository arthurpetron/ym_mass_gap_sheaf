/-
Computed Type-level inner moduli for the constructive rational logarithm.

`CRealLog.artanh` already proves its legacy `CReal.cauchy` field using the
explicit stage `((8/9) * epsilon).den`.  This module exposes the same stage as
`CReal.InnerRegularity` data, then composes it through `scaleTwo`, `logRat`, and
`log2`.  It does not extract a witness from the propositional Cauchy field.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Constructive.CRealLog

namespace YMGap.Constructive.CRealLog

open YMGap.Constructive

/-- The explicit approximation-index modulus used by the constructive artanh
series. -/
def artanhInnerRegularity (y : Q')
    (hy : Q'.abs y <= recipOdd 1) :
    CReal.InnerRegularity (artanh y hy) where
  rate epsilon := (Q'.mkPos 8 9 (by decide) * epsilon).den
  regular := by
    intro epsilon hepsilon p q hp hq
    have hepsilonNonnegative : (0 : Q') <= epsilon := Q'.le_of_lt hepsilon
    have hscaledPositive :
        (0 : Q') < Q'.mkPos 8 9 (by decide) * epsilon :=
      eightNinths_eps_pos epsilon hepsilon
    have directed : forall k l : Nat,
        (Q'.mkPos 8 9 (by decide) * epsilon).den <= k -> k <= l ->
          partialSum y l <= partialSum y k + epsilon /\
          partialSum y k <= partialSum y l + epsilon := by
      intro k l hk hkl
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have hterm : termAbs y k <= Q'.mkPos 8 9 (by decide) * epsilon :=
        termAbs_le_of_den_le y hy
          (Q'.mkPos 8 9 (by decide) * epsilon) hscaledPositive k hk
      have hrecurrence : termAbs y k + oneNinth * epsilon <= epsilon :=
        recurrence_from_term y k epsilon hterm
      have htail : blockAbs y k d <= epsilon :=
        blockAbs_le y hy epsilon k hepsilonNonnegative hrecurrence d
      exact
        ⟨Q'.le_trans' _ _ _ (block_upper y k d)
            (Q'.add_le_add_left (partialSum y k) (blockAbs y k d)
              epsilon htail),
         Q'.le_trans' _ _ _ (block_lower y k d)
            (Q'.add_le_add_left (partialSum y (k + d)) (blockAbs y k d)
              epsilon htail)⟩
    change partialSum y p <= partialSum y q + epsilon /\
      partialSum y q <= partialSum y p + epsilon
    rcases Nat.le_total p q with hpq | hqp
    · exact ⟨(directed p q hp hpq).2, (directed p q hp hpq).1⟩
    · exact ⟨(directed q p hq hqp).1, (directed q p hq hqp).2⟩

/-- Doubling a constructive real composes its inner modulus by the generic
addition constructor. -/
def scaleTwoInnerRegularity {x : CReal} (X : CReal.InnerRegularity x) :
    CReal.InnerRegularity (scaleTwo x) :=
  CReal.InnerRegularity.add X X

/-- A computed inner modulus for the directly range-reduced rational
logarithm. -/
def logRatInnerRegularity (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) <= recipOdd 1) :
    CReal.InnerRegularity (logRat m hm1 hyb) :=
  scaleTwoInnerRegularity (artanhInnerRegularity (yOf m hm1) hyb)

/-- A computed inner modulus for the repository's constructive `log 2`. -/
def log2InnerRegularity : CReal.InnerRegularity log2 :=
  logRatInnerRegularity (2 : Q') (by decide) yOf_two_window

end YMGap.Constructive.CRealLog

#print axioms YMGap.Constructive.CRealLog.artanhInnerRegularity
#print axioms YMGap.Constructive.CRealLog.scaleTwoInnerRegularity
#print axioms YMGap.Constructive.CRealLog.logRatInnerRegularity
#print axioms YMGap.Constructive.CRealLog.log2InnerRegularity
