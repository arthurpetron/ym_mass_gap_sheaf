/-
# Constructive finite bounds for the direct all-chart FREE comparison

The centered chart-quadratic mismatch and the complete centered all-chart
homogeneous residual are bounded using the actual normalized ORIGINAL
polynomial expectation bound for their pair and one-source terms.  These two
bounds are then added to the existing ORIGINAL-to-FREE law-defect bound.

The resulting quantity is explicit and finite, but is not claimed to be
small, cutoff-uniform, or sufficient to pay a neighboring strict margin.  No
cutoff removal, continuum Hamiltonian, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Explicit absolute bound for one normalized ORIGINAL chart-quadratic
mismatch expectation. -/
def globalCayleyVectorJetBulkChartQuadraticMismatchOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkChartQuadraticMismatchSource
      s hs (centralExtent half) time)

/-- Explicit absolute bound for the normalized ORIGINAL mismatch-bearing
chart-quadratic pair expectation. -/
def globalCayleyVectorJetBulkPairChartQuadraticMismatchOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkPairChartQuadraticMismatchSource
      s hs (centralExtent half) leftTime rightTime)

/-- Fully explicit finite absolute bound for the centered chart-quadratic
mismatch. -/
def globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : Q' :=
  globalCayleyVectorJetBulkPairChartQuadraticMismatchOriginalAbsBound
      w hw0 hw1 half s hs leftTime rightTime +
    (globalCayleyVectorJetBulkIdentityQuadraticOriginalAbsBound
        w hw0 hw1 half s hs leftTime *
      globalCayleyVectorJetBulkChartQuadraticMismatchOriginalAbsBound
        w hw0 hw1 half s hs rightTime +
      (globalCayleyVectorJetBulkChartQuadraticMismatchOriginalAbsBound
          w hw0 hw1 half s hs leftTime *
        globalCayleyVectorJetBulkIdentityQuadraticOriginalAbsBound
          w hw0 hw1 half s hs rightTime +
        globalCayleyVectorJetBulkChartQuadraticMismatchOriginalAbsBound
            w hw0 hw1 half s hs leftTime *
          globalCayleyVectorJetBulkChartQuadraticMismatchOriginalAbsBound
            w hw0 hw1 half s hs rightTime))

/-- Explicit absolute bound for one normalized ORIGINAL all-chart quadratic
expectation. -/
def globalCayleyVectorJetBulkChartQuadraticOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkChartQuadraticSource
      s hs (centralExtent half) time)

/-- Explicit absolute bound for one normalized ORIGINAL complete all-chart
homogeneous remainder expectation. -/
def globalCayleyVectorJetBulkChartRemainderOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkChartRemainderSource
      s hs (centralExtent half) time)

/-- Explicit absolute bound for the normalized ORIGINAL pair expectation
containing every all-chart homogeneous remainder product. -/
def globalCayleyVectorJetBulkPairChartRemainderOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkPairChartRemainderSource
      s hs (centralExtent half) leftTime rightTime)

/-- Fully explicit finite absolute bound for the complete centered all-chart
homogeneous residual. -/
def globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : Q' :=
  globalCayleyVectorJetBulkPairChartRemainderOriginalAbsBound
      w hw0 hw1 half s hs leftTime rightTime +
    (globalCayleyVectorJetBulkChartQuadraticOriginalAbsBound
        w hw0 hw1 half s hs leftTime *
      globalCayleyVectorJetBulkChartRemainderOriginalAbsBound
        w hw0 hw1 half s hs rightTime +
      (globalCayleyVectorJetBulkChartRemainderOriginalAbsBound
          w hw0 hw1 half s hs leftTime *
        globalCayleyVectorJetBulkChartQuadraticOriginalAbsBound
          w hw0 hw1 half s hs rightTime +
        globalCayleyVectorJetBulkChartRemainderOriginalAbsBound
            w hw0 hw1 half s hs leftTime *
          globalCayleyVectorJetBulkChartRemainderOriginalAbsBound
            w hw0 hw1 half s hs rightTime))

/-- Explicit direct-comparison residual budget: the existing law-defect bound
plus the chart-mismatch and all-chart homogeneous bounds. -/
def globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : Q' :=
  globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound
      w hw0 hw1 half s hs stage leftTime rightTime +
    (globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound
        w hw0 hw1 half s hs leftTime rightTime +
      globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound
        w hw0 hw1 half s hs leftTime rightTime)

private theorem abs_neg_le {value bound : Q'}
    (h : Q'.abs value ≤ bound) : Q'.abs (-value) ≤ bound :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' value)) h

private theorem abs_mul_le_of_bounds
    {left right leftBound rightBound : Q'}
    (hleft : Q'.abs left ≤ leftBound)
    (hright : Q'.abs right ≤ rightBound)
    (hleftBound : (0 : Q') ≤ leftBound) :
    Q'.abs (left * right) ≤ leftBound * rightBound :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le left right)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hleft (Q'.abs_nonneg right))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftBound))

private theorem abs_centered_three_product_le
    (pair leftBase leftError rightBase rightError
      pairBound leftBaseBound leftErrorBound rightBaseBound rightErrorBound : Q')
    (hpair : Q'.abs pair ≤ pairBound)
    (hleftBase : Q'.abs leftBase ≤ leftBaseBound)
    (hleftError : Q'.abs leftError ≤ leftErrorBound)
    (hrightBase : Q'.abs rightBase ≤ rightBaseBound)
    (hrightError : Q'.abs rightError ≤ rightErrorBound)
    (hleftBaseBound : (0 : Q') ≤ leftBaseBound)
    (hleftErrorBound : (0 : Q') ≤ leftErrorBound) :
    Q'.abs
        (pair +
          -(leftBase * rightError +
            (leftError * rightBase + leftError * rightError))) ≤
      pairBound +
        (leftBaseBound * rightErrorBound +
          (leftErrorBound * rightBaseBound +
            leftErrorBound * rightErrorBound)) := by
  have hbaseError : Q'.abs (leftBase * rightError) ≤
      leftBaseBound * rightErrorBound :=
    abs_mul_le_of_bounds hleftBase hrightError hleftBaseBound
  have herrorBase : Q'.abs (leftError * rightBase) ≤
      leftErrorBound * rightBaseBound :=
    abs_mul_le_of_bounds hleftError hrightBase hleftErrorBound
  have herrorError : Q'.abs (leftError * rightError) ≤
      leftErrorBound * rightErrorBound :=
    abs_mul_le_of_bounds hleftError hrightError hleftErrorBound
  have hinner : Q'.abs
      (leftError * rightBase + leftError * rightError) ≤
        leftErrorBound * rightBaseBound +
          leftErrorBound * rightErrorBound :=
    Q'.le_trans' _ _ _
      (Q'.abs_add_le' (leftError * rightBase) (leftError * rightError))
      (Q'.add_le_add herrorBase herrorError)
  have hsum : Q'.abs
      (leftBase * rightError +
        (leftError * rightBase + leftError * rightError)) ≤
        leftBaseBound * rightErrorBound +
          (leftErrorBound * rightBaseBound +
            leftErrorBound * rightErrorBound) :=
    Q'.le_trans' _ _ _
      (Q'.abs_add_le' (leftBase * rightError)
        (leftError * rightBase + leftError * rightError))
      (Q'.add_le_add hbaseError hinner)
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le' pair
      (-(leftBase * rightError +
        (leftError * rightBase + leftError * rightError))))
    (Q'.add_le_add hpair (abs_neg_le hsum))

theorem globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound_nonnegative
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    (0 : Q') ≤
      globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound
        w hw0 hw1 half s hs leftTime rightTime := by
  apply Q'.zero_le_add
  · exact expectationAbsBound_nonnegative w hw0 hw1 half _
  · apply Q'.zero_le_add
    · exact Q'.mul_nonneg _ _
        (expectationAbsBound_nonnegative w hw0 hw1 half _)
        (expectationAbsBound_nonnegative w hw0 hw1 half _)
    · apply Q'.zero_le_add
      · exact Q'.mul_nonneg _ _
          (expectationAbsBound_nonnegative w hw0 hw1 half _)
          (expectationAbsBound_nonnegative w hw0 hw1 half _)
      · exact Q'.mul_nonneg _ _
          (expectationAbsBound_nonnegative w hw0 hw1 half _)
          (expectationAbsBound_nonnegative w hw0 hw1 half _)

/-- Every approximant of the centered chart-quadratic mismatch obeys its
explicit finite bound. -/
theorem globalCayleyVectorJetBulkCenteredChartQuadraticMismatch_approx_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime n : Nat) :
    Q'.abs
        ((globalCayleyVectorJetBulkCenteredChartQuadraticMismatch
          w hw0 hw1 half s hs leftTime rightTime).approx n) ≤
      globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound
        w hw0 hw1 half s hs leftTime rightTime := by
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs (centralExtent half) leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs (centralExtent half) rightTime
  let leftMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchSource
    s hs (centralExtent half) leftTime
  let rightMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchSource
    s hs (centralExtent half) rightTime
  let pairMismatch :=
    globalCayleyVectorJetBulkPairChartQuadraticMismatchSource
      s hs (centralExtent half) leftTime rightTime
  change Q'.abs
      ((expectation w hw0 hw1 half pairMismatch).approx n +
        -((expectation w hw0 hw1 half leftIdentity).approx n *
            (expectation w hw0 hw1 half rightMismatch).approx n +
          ((expectation w hw0 hw1 half leftMismatch).approx n *
              (expectation w hw0 hw1 half rightIdentity).approx n +
            (expectation w hw0 hw1 half leftMismatch).approx n *
              (expectation w hw0 hw1 half rightMismatch).approx n))) ≤
    expectationAbsBound w hw0 hw1 half pairMismatch +
      (expectationAbsBound w hw0 hw1 half leftIdentity *
          expectationAbsBound w hw0 hw1 half rightMismatch +
        (expectationAbsBound w hw0 hw1 half leftMismatch *
            expectationAbsBound w hw0 hw1 half rightIdentity +
          expectationAbsBound w hw0 hw1 half leftMismatch *
            expectationAbsBound w hw0 hw1 half rightMismatch))
  exact abs_centered_three_product_le
    ((expectation w hw0 hw1 half pairMismatch).approx n)
    ((expectation w hw0 hw1 half leftIdentity).approx n)
    ((expectation w hw0 hw1 half leftMismatch).approx n)
    ((expectation w hw0 hw1 half rightIdentity).approx n)
    ((expectation w hw0 hw1 half rightMismatch).approx n)
    (expectationAbsBound w hw0 hw1 half pairMismatch)
    (expectationAbsBound w hw0 hw1 half leftIdentity)
    (expectationAbsBound w hw0 hw1 half leftMismatch)
    (expectationAbsBound w hw0 hw1 half rightIdentity)
    (expectationAbsBound w hw0 hw1 half rightMismatch)
    (expectation_approx_abs_le w hw0 hw1 half pairMismatch n)
    (expectation_approx_abs_le w hw0 hw1 half leftIdentity n)
    (expectation_approx_abs_le w hw0 hw1 half leftMismatch n)
    (expectation_approx_abs_le w hw0 hw1 half rightIdentity n)
    (expectation_approx_abs_le w hw0 hw1 half rightMismatch n)
    (expectationAbsBound_nonnegative w hw0 hw1 half leftIdentity)
    (expectationAbsBound_nonnegative w hw0 hw1 half leftMismatch)

/-- Constructive-real bound for the centered chart-quadratic mismatch. -/
theorem globalCayleyVectorJetBulkCenteredChartQuadraticMismatch_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.leEv
      (CReal.abs
        (globalCayleyVectorJetBulkCenteredChartQuadraticMismatch
          w hw0 hw1 half s hs leftTime rightTime))
      (CReal.ofQ'
        (globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound
          w hw0 hw1 half s hs leftTime rightTime)) :=
  CReal.leEv_le_ofQ'_of_approx_le
    (globalCayleyVectorJetBulkCenteredChartQuadraticMismatch_approx_abs_le
      w hw0 hw1 half s hs leftTime rightTime)

theorem globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound_nonnegative
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    (0 : Q') ≤
      globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound
        w hw0 hw1 half s hs leftTime rightTime := by
  apply Q'.zero_le_add
  · exact expectationAbsBound_nonnegative w hw0 hw1 half _
  · apply Q'.zero_le_add
    · exact Q'.mul_nonneg _ _
        (expectationAbsBound_nonnegative w hw0 hw1 half _)
        (expectationAbsBound_nonnegative w hw0 hw1 half _)
    · apply Q'.zero_le_add
      · exact Q'.mul_nonneg _ _
          (expectationAbsBound_nonnegative w hw0 hw1 half _)
          (expectationAbsBound_nonnegative w hw0 hw1 half _)
      · exact Q'.mul_nonneg _ _
          (expectationAbsBound_nonnegative w hw0 hw1 half _)
          (expectationAbsBound_nonnegative w hw0 hw1 half _)

/-- Every approximant of the complete centered all-chart homogeneous residual
obeys its explicit finite bound. -/
theorem globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual_approx_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime n : Nat) :
    Q'.abs
        ((globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
          w hw0 hw1 half s hs leftTime rightTime).approx n) ≤
      globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound
        w hw0 hw1 half s hs leftTime rightTime := by
  let leftQuadratic := globalCayleyVectorJetBulkChartQuadraticSource
    s hs (centralExtent half) leftTime
  let rightQuadratic := globalCayleyVectorJetBulkChartQuadraticSource
    s hs (centralExtent half) rightTime
  let leftRemainder := globalCayleyVectorJetBulkChartRemainderSource
    s hs (centralExtent half) leftTime
  let rightRemainder := globalCayleyVectorJetBulkChartRemainderSource
    s hs (centralExtent half) rightTime
  let pairRemainder := globalCayleyVectorJetBulkPairChartRemainderSource
    s hs (centralExtent half) leftTime rightTime
  change Q'.abs
      ((expectation w hw0 hw1 half pairRemainder).approx n +
        -((expectation w hw0 hw1 half leftQuadratic).approx n *
            (expectation w hw0 hw1 half rightRemainder).approx n +
          ((expectation w hw0 hw1 half leftRemainder).approx n *
              (expectation w hw0 hw1 half rightQuadratic).approx n +
            (expectation w hw0 hw1 half leftRemainder).approx n *
              (expectation w hw0 hw1 half rightRemainder).approx n))) ≤
    expectationAbsBound w hw0 hw1 half pairRemainder +
      (expectationAbsBound w hw0 hw1 half leftQuadratic *
          expectationAbsBound w hw0 hw1 half rightRemainder +
        (expectationAbsBound w hw0 hw1 half leftRemainder *
            expectationAbsBound w hw0 hw1 half rightQuadratic +
          expectationAbsBound w hw0 hw1 half leftRemainder *
            expectationAbsBound w hw0 hw1 half rightRemainder))
  exact abs_centered_three_product_le
    ((expectation w hw0 hw1 half pairRemainder).approx n)
    ((expectation w hw0 hw1 half leftQuadratic).approx n)
    ((expectation w hw0 hw1 half leftRemainder).approx n)
    ((expectation w hw0 hw1 half rightQuadratic).approx n)
    ((expectation w hw0 hw1 half rightRemainder).approx n)
    (expectationAbsBound w hw0 hw1 half pairRemainder)
    (expectationAbsBound w hw0 hw1 half leftQuadratic)
    (expectationAbsBound w hw0 hw1 half leftRemainder)
    (expectationAbsBound w hw0 hw1 half rightQuadratic)
    (expectationAbsBound w hw0 hw1 half rightRemainder)
    (expectation_approx_abs_le w hw0 hw1 half pairRemainder n)
    (expectation_approx_abs_le w hw0 hw1 half leftQuadratic n)
    (expectation_approx_abs_le w hw0 hw1 half leftRemainder n)
    (expectation_approx_abs_le w hw0 hw1 half rightQuadratic n)
    (expectation_approx_abs_le w hw0 hw1 half rightRemainder n)
    (expectationAbsBound_nonnegative w hw0 hw1 half leftQuadratic)
    (expectationAbsBound_nonnegative w hw0 hw1 half leftRemainder)

/-- Constructive-real bound for the complete centered all-chart homogeneous
residual. -/
theorem globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.leEv
      (CReal.abs
        (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
          w hw0 hw1 half s hs leftTime rightTime))
      (CReal.ofQ'
        (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound
          w hw0 hw1 half s hs leftTime rightTime)) :=
  CReal.leEv_le_ofQ'_of_approx_le
    (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual_approx_abs_le
      w hw0 hw1 half s hs leftTime rightTime)

theorem globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound_nonnegative
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) :
    (0 : Q') ≤
      globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound
        w hw0 hw1 half s hs stage leftTime rightTime := by
  apply Q'.zero_le_add
  · exact
      globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound_nonnegative
        w hw0 hw1 half s hs stage leftTime rightTime
  · exact Q'.zero_le_add _ _
      (globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound_nonnegative
        w hw0 hw1 half s hs leftTime rightTime)
      (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound_nonnegative
        w hw0 hw1 half s hs leftTime rightTime)

/-- Every approximant of the direct comparison's complete three-family
residual obeys the summed explicit finite bound. -/
theorem globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual_approx_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime n : Nat) :
    Q'.abs
        ((globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
          w hw0 hw1 half s hs stage leftTime rightTime).approx n) ≤
      globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound
        w hw0 hw1 half s hs stage leftTime rightTime := by
  let law := globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
    w hw0 hw1 half s hs stage leftTime rightTime
  let mismatch := globalCayleyVectorJetBulkCenteredChartQuadraticMismatch
    w hw0 hw1 half s hs leftTime rightTime
  let homogeneous :=
    globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
      w hw0 hw1 half s hs leftTime rightTime
  let lawBound :=
    globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound
      w hw0 hw1 half s hs stage leftTime rightTime
  let mismatchBound :=
    globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound
      w hw0 hw1 half s hs leftTime rightTime
  let homogeneousBound :=
    globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound
      w hw0 hw1 half s hs leftTime rightTime
  change Q'.abs (law.approx n + (mismatch.approx n + homogeneous.approx n)) ≤
    lawBound + (mismatchBound + homogeneousBound)
  have hinner : Q'.abs (mismatch.approx n + homogeneous.approx n) ≤
      mismatchBound + homogeneousBound :=
    Q'.le_trans' _ _ _
      (Q'.abs_add_le' (mismatch.approx n) (homogeneous.approx n))
      (Q'.add_le_add
        (globalCayleyVectorJetBulkCenteredChartQuadraticMismatch_approx_abs_le
          w hw0 hw1 half s hs leftTime rightTime n)
        (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual_approx_abs_le
          w hw0 hw1 half s hs leftTime rightTime n))
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le' (law.approx n)
      (mismatch.approx n + homogeneous.approx n))
    (Q'.add_le_add
      (globalCayleyVectorJetBulkCenteredOriginalToFreeComparison_approx_abs_le
        w hw0 hw1 half s hs stage leftTime rightTime n)
      hinner)

/-- Constructive-real finite bound for the complete direct all-chart
ORIGINAL-to-FREE comparison residual. -/
theorem globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) :
    CReal.leEv
      (CReal.abs
        (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
          w hw0 hw1 half s hs stage leftTime rightTime))
      (CReal.ofQ'
        (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound
          w hw0 hw1 half s hs stage leftTime rightTime)) :=
  CReal.leEv_le_ofQ'_of_approx_le
    (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual_approx_abs_le
      w hw0 hw1 half s hs stage leftTime rightTime)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredChartQuadraticMismatchAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredChartQuadraticMismatch_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredChartQuadraticMismatch_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidualAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidualAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparisonBound.globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual_abs_le
