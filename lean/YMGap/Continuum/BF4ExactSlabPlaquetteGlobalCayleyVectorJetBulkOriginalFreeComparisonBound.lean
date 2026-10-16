/-
# Finite constructive bound for the ORIGINAL-to-FREE comparison remainder

The exact comparison remainder isolated in the preceding leaf is now bounded
without identifying the ORIGINAL interacting law with the finite FREE
Gaussian law.  The bound uses the actual polynomial numerator estimate and
partition-reciprocal ceiling for the pair and both one-source ORIGINAL
expectations, together with the absolute value of the exact finite FREE
covariance.

This is a finite, parameter-dependent bound.  It is not claimed to be small,
cutoff-uniform, or sufficient to pay the neighboring strict margin.  No bound
for the inner-denominator, outer-denominator, or Cayley remainders is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Explicit absolute bound for one normalized ORIGINAL identity-quadratic
source expectation. -/
def globalCayleyVectorJetBulkIdentityQuadraticOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkIdentityQuadraticSource
      s hs (centralExtent half) time)

/-- Explicit absolute bound for the normalized ORIGINAL pair expectation. -/
def globalCayleyVectorJetBulkPairIdentityQuadraticOriginalAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : Q' :=
  expectationAbsBound w hw0 hw1 half
    (globalCayleyVectorJetBulkPairIdentityQuadraticSource
      s hs (centralExtent half) leftTime rightTime)

/-- Absolute value of the exact finite FREE physical-link pullback
covariance. -/
def globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeAbsBound
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : Q' :=
  Q'.abs
    (finiteGaussianCovariance
      (bulkSourceNoiseCount (centralExtent half) s)
      (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
        (centralExtent half) s hs stage leftTime)
      (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
        (centralExtent half) s hs stage rightTime))

/-- Fully explicit finite absolute bound for the named ORIGINAL-to-FREE
comparison remainder. -/
def globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : Q' :=
  globalCayleyVectorJetBulkPairIdentityQuadraticOriginalAbsBound
      w hw0 hw1 half s hs leftTime rightTime +
    globalCayleyVectorJetBulkIdentityQuadraticOriginalAbsBound
        w hw0 hw1 half s hs leftTime *
      globalCayleyVectorJetBulkIdentityQuadraticOriginalAbsBound
        w hw0 hw1 half s hs rightTime +
    globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeAbsBound
      half s hs stage leftTime rightTime

theorem globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound_nonnegative
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) :
    (0 : Q') ≤
      globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound
        w hw0 hw1 half s hs stage leftTime rightTime := by
  apply Q'.zero_le_add
  · apply Q'.zero_le_add
    · exact expectationAbsBound_nonnegative w hw0 hw1 half _
    · exact Q'.mul_nonneg _ _
        (expectationAbsBound_nonnegative w hw0 hw1 half _)
        (expectationAbsBound_nonnegative w hw0 hw1 half _)
  · exact Q'.abs_nonneg _

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

private theorem abs_centered_comparison_le
    (pair left right free pairBound leftBound rightBound : Q')
    (hpair : Q'.abs pair ≤ pairBound)
    (hleft : Q'.abs left ≤ leftBound)
    (hright : Q'.abs right ≤ rightBound)
    (hleftBound : (0 : Q') ≤ leftBound) :
    Q'.abs ((pair + -(left * right)) + -free) ≤
      pairBound + leftBound * rightBound + Q'.abs free := by
  have hproduct : Q'.abs (left * right) ≤ leftBound * rightBound :=
    abs_mul_le_of_bounds hleft hright hleftBound
  have hcentered : Q'.abs (pair + -(left * right)) ≤
      pairBound + leftBound * rightBound :=
    Q'.le_trans' _ _ _ (Q'.abs_add_le' pair (-(left * right)))
      (Q'.add_le_add hpair (abs_neg_le hproduct))
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le' (pair + -(left * right)) (-free))
    (Q'.add_le_add hcentered
      (Q'.le_of_eqv (Q'.abs_neg' free)))

/-- Every approximant of the named comparison remainder obeys the explicit
finite bound. -/
theorem globalCayleyVectorJetBulkCenteredOriginalToFreeComparison_approx_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime n : Nat) :
    Q'.abs
        ((globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
          w hw0 hw1 half s hs stage leftTime rightTime).approx n) ≤
      globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound
        w hw0 hw1 half s hs stage leftTime rightTime := by
  let pairSource := globalCayleyVectorJetBulkPairIdentityQuadraticSource
    s hs (centralExtent half) leftTime rightTime
  let leftSource := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs (centralExtent half) leftTime
  let rightSource := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs (centralExtent half) rightTime
  let free := finiteGaussianCovariance
    (bulkSourceNoiseCount (centralExtent half) s)
    (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
      (centralExtent half) s hs stage leftTime)
    (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
      (centralExtent half) s hs stage rightTime)
  change Q'.abs
      (((expectation w hw0 hw1 half pairSource).approx n +
          -((expectation w hw0 hw1 half leftSource).approx n *
            (expectation w hw0 hw1 half rightSource).approx n)) +
        -free) ≤
    expectationAbsBound w hw0 hw1 half pairSource +
      expectationAbsBound w hw0 hw1 half leftSource *
        expectationAbsBound w hw0 hw1 half rightSource + Q'.abs free
  exact abs_centered_comparison_le
    ((expectation w hw0 hw1 half pairSource).approx n)
    ((expectation w hw0 hw1 half leftSource).approx n)
    ((expectation w hw0 hw1 half rightSource).approx n)
    free
    (expectationAbsBound w hw0 hw1 half pairSource)
    (expectationAbsBound w hw0 hw1 half leftSource)
    (expectationAbsBound w hw0 hw1 half rightSource)
    (expectation_approx_abs_le w hw0 hw1 half pairSource n)
    (expectation_approx_abs_le w hw0 hw1 half leftSource n)
    (expectation_approx_abs_le w hw0 hw1 half rightSource n)
    (expectationAbsBound_nonnegative w hw0 hw1 half leftSource)

/-- Constructive-real finite bound for the complete named ORIGINAL-to-FREE
comparison remainder. -/
theorem globalCayleyVectorJetBulkCenteredOriginalToFreeComparison_abs_le
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) :
    CReal.leEv
      (CReal.abs
        (globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
          w hw0 hw1 half s hs stage leftTime rightTime))
      (CReal.ofQ'
        (globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound
          w hw0 hw1 half s hs stage leftTime rightTime)) :=
  CReal.leEv_le_ofQ'_of_approx_le
    (globalCayleyVectorJetBulkCenteredOriginalToFreeComparison_approx_abs_le
      w hw0 hw1 half s hs stage leftTime rightTime)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound.globalCayleyVectorJetBulkIdentityQuadraticOriginalAbsBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound.globalCayleyVectorJetBulkPairIdentityQuadraticOriginalAbsBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound.globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeAbsBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound.globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound.globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonAbsBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound.globalCayleyVectorJetBulkCenteredOriginalToFreeComparison_approx_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparisonBound.globalCayleyVectorJetBulkCenteredOriginalToFreeComparison_abs_le
