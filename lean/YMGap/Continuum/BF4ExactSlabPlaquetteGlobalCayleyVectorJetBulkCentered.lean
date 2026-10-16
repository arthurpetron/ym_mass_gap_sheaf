/-
# Centered weighted bulk-source Cayley vector-jet split

The exact weighted two-source product split is combined with the two exact
one-source mean splits.  The centered cleared ORIGINAL response becomes the
centered weighted quadratic response plus one explicit residual.  That
residual contains the aggregate pair residual and exactly the three
mean-product terms carrying at least one one-source Cayley residual.

No residual bound, denominator removal, FREE Gaussian identification,
strict-margin payment, cutoff removal, continuum theory, or mass gap is
asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem centeredSplitQ
    (quadraticPair pairRemainder leftQuadratic leftRemainder
      rightQuadratic rightRemainder : Q') :
    (quadraticPair + pairRemainder) +
        -((leftQuadratic + leftRemainder) *
          (rightQuadratic + rightRemainder)) ≈
      (quadraticPair + -(leftQuadratic * rightQuadratic)) +
        (pairRemainder +
          -(leftQuadratic * rightRemainder +
            (leftRemainder * rightQuadratic +
              leftRemainder * rightRemainder))) := by
  let leading := leftQuadratic * rightQuadratic
  let residual := leftQuadratic * rightRemainder +
    (leftRemainder * rightQuadratic + leftRemainder * rightRemainder)
  have hproduct :
      (leftQuadratic + leftRemainder) *
          (rightQuadratic + rightRemainder) ≈
        leading + residual := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv leftQuadratic leftRemainder
        (rightQuadratic + rightRemainder))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv leftQuadratic rightQuadratic rightRemainder)
          (Q'.mul_add_eqv leftRemainder rightQuadratic rightRemainder))
        (Q'.add_assoc_eqv
          (leftQuadratic * rightQuadratic)
          (leftQuadratic * rightRemainder)
          (leftRemainder * rightQuadratic +
            leftRemainder * rightRemainder)))
  have hnegative :
      -((leftQuadratic + leftRemainder) *
          (rightQuadratic + rightRemainder)) ≈
        -leading + -residual :=
    Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hproduct)
      (Q'.neg_add_eqv leading residual)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hnegative)
    (Q'.add_swap_inner quadraticPair pairRemainder
      (-leading) (-residual))

/-- Centered normalized ORIGINAL response of the two complete weighted
cleared vector-jet sources. -/
def globalCayleyVectorJetBulkCenteredClearedResponse
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkPairClearedExpectation
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.mul
      (globalCayleyVectorJetBulkClearedExpectation
        w hw0 hw1 half s hs leftTime)
      (globalCayleyVectorJetBulkClearedExpectation
        w hw0 hw1 half s hs rightTime))

/-- Centered normalized ORIGINAL response of the two extracted weighted
quadratic sources. -/
def globalCayleyVectorJetBulkCenteredQuadraticResponse
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkPairQuadraticExpectation
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.mul
      (globalCayleyVectorJetBulkQuadraticExpectation
        w hw0 hw1 half s hs leftTime)
      (globalCayleyVectorJetBulkQuadraticExpectation
        w hw0 hw1 half s hs rightTime))

/-- Exact centered error: the aggregate pair residual minus the three
mean-product terms containing at least one one-source Cayley residual. -/
def globalCayleyVectorJetBulkCenteredRemainder
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  let leftQuadratic := globalCayleyVectorJetBulkQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightQuadratic := globalCayleyVectorJetBulkQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftRemainder := globalCayleyVectorJetBulkRemainderExpectation
    w hw0 hw1 half s hs leftTime
  let rightRemainder := globalCayleyVectorJetBulkRemainderExpectation
    w hw0 hw1 half s hs rightTime
  let pairRemainder := globalCayleyVectorJetBulkPairRemainderExpectation
    w hw0 hw1 half s hs leftTime rightTime
  CReal.sub pairRemainder
    (CReal.add
      (CReal.mul leftQuadratic rightRemainder)
      (CReal.add
        (CReal.mul leftRemainder rightQuadratic)
        (CReal.mul leftRemainder rightRemainder)))

/-- Exact centered split under the same normalized ORIGINAL action.  The
quadratic covariance and every remaining Cayley contribution are separated
without changing either center. -/
theorem globalCayleyVectorJetBulkCentered_quadratic_remainder_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredClearedResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredQuadraticResponse
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredRemainder
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let clearedPair := globalCayleyVectorJetBulkPairClearedExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let quadraticPair := globalCayleyVectorJetBulkPairQuadraticExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let pairRemainder := globalCayleyVectorJetBulkPairRemainderExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let leftCleared := globalCayleyVectorJetBulkClearedExpectation
    w hw0 hw1 half s hs leftTime
  let rightCleared := globalCayleyVectorJetBulkClearedExpectation
    w hw0 hw1 half s hs rightTime
  let leftQuadratic := globalCayleyVectorJetBulkQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightQuadratic := globalCayleyVectorJetBulkQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftRemainder := globalCayleyVectorJetBulkRemainderExpectation
    w hw0 hw1 half s hs leftTime
  let rightRemainder := globalCayleyVectorJetBulkRemainderExpectation
    w hw0 hw1 half s hs rightTime
  have hpair := globalCayleyVectorJetBulkPair_originalExpectation_split
    w hw0 hw1 half s hs leftTime rightTime
      hwidth hleftTime hrightTime
  change CReal.Equiv clearedPair
    (CReal.add quadraticPair pairRemainder) at hpair
  have hleft := globalCayleyVectorJetBulk_originalExpectation_split
    w hw0 hw1 half s hs leftTime hwidth hleftTime
  change CReal.Equiv leftCleared
    (CReal.add leftQuadratic leftRemainder) at hleft
  have hright := globalCayleyVectorJetBulk_originalExpectation_split
    w hw0 hw1 half s hs rightTime hwidth hrightTime
  change CReal.Equiv rightCleared
    (CReal.add rightQuadratic rightRemainder) at hright
  have hmeans : CReal.Equiv
      (CReal.mul leftCleared rightCleared)
      (CReal.mul
        (CReal.add leftQuadratic leftRemainder)
        (CReal.add rightQuadratic rightRemainder)) :=
    Pivot2.mul_congr hleft hright
  have hsub : CReal.Equiv
      (CReal.sub clearedPair (CReal.mul leftCleared rightCleared))
      (CReal.sub
        (CReal.add quadraticPair pairRemainder)
        (CReal.mul
          (CReal.add leftQuadratic leftRemainder)
          (CReal.add rightQuadratic rightRemainder))) :=
    (CReal.sub_congr_left hpair).trans (CReal.sub_congr_right hmeans)
  have hregroup : CReal.Equiv
      (CReal.sub
        (CReal.add quadraticPair pairRemainder)
        (CReal.mul
          (CReal.add leftQuadratic leftRemainder)
          (CReal.add rightQuadratic rightRemainder)))
      (CReal.add
        (CReal.sub quadraticPair
          (CReal.mul leftQuadratic rightQuadratic))
        (CReal.sub pairRemainder
          (CReal.add
            (CReal.mul leftQuadratic rightRemainder)
            (CReal.add
              (CReal.mul leftRemainder rightQuadratic)
              (CReal.mul leftRemainder rightRemainder))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      centeredSplitQ
        (quadraticPair.approx n) (pairRemainder.approx n)
        (leftQuadratic.approx n) (leftRemainder.approx n)
        (rightQuadratic.approx n) (rightRemainder.approx n))
  change CReal.Equiv
    (CReal.sub clearedPair (CReal.mul leftCleared rightCleared)) _
  exact hsub.trans hregroup

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered.globalCayleyVectorJetBulkCentered_quadratic_remainder_split
