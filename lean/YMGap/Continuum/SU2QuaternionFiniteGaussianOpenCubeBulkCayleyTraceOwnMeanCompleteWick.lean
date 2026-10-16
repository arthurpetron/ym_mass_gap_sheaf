/-
# Complete finite Wick form of the Cayley trace-source OWN means

This leaf joins the checked source expectation, source/action covariance,
complete even-density covariance, and repeated-cubic cumulant compilers into
one explicit finite Wick expression for the fourth OWN source coefficient.
It then substitutes the exact `a2` and `a4` certificates into the literal
parity-normalized OLD-centered order-six response `P6`.

The supplied OLD coefficients remain arbitrary: in particular the residual
`(-c3)*(-c3)` is retained.  The result is finite FREE reference algebra, not
an ORIGINAL-law center identification, a higher-remainder estimate, a
uniform signed bound, or a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanCompleteWick

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceConnectedR6
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-- The complete explicit finite Wick value of the fourth OWN source mean. -/
def openCubeBulkCayleyTraceOwnA4MeanWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : Q' :=
  ((openCubeBulkCayleyTraceA4ExpectationWickSum
        timeBonds side sidePositive stage time -
      openCubeBulkCayleyTraceA3ActionV3CovarianceWickSum
        timeBonds side sidePositive stage time) +
    openCubeBulkCayleyTraceA2J2MinusV4CovarianceWickSum
      timeBonds side sidePositive stage time) +
  cubicPairHalf *
    openCubeBulkCayleyTraceA2ActionV3V3CumulantWickSum
      timeBonds side sidePositive stage time

/-- The literal fourth OWN source coefficient has no remaining unevaluated
Gaussian expectation, covariance, or cumulant: it equals the displayed
complete finite Wick-family sum. -/
theorem openCubeBulkCayleyTraceOwnA4Mean_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeBulkCayleyTraceOwnA4Mean
        timeBonds side sidePositive stage time ≈
      openCubeBulkCayleyTraceOwnA4MeanWickSum
        timeBonds side sidePositive stage time := by
  unfold openCubeBulkCayleyTraceOwnA4Mean
    openCubeBulkCayleyTraceOwnA4MeanWickSum
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (finiteProductGaussian_openCube_bulk_cayley_trace_A4_wick
          timeBonds side sidePositive stage time)
        (Q'.neg_eqv_congr _ _
          (finiteGaussianCovariance_openCube_bulk_cayley_trace_A3_actionV3_wick
            timeBonds side sidePositive stage time)))
      (finiteGaussianCovariance_openCube_bulk_cayley_trace_A2_J2MinusV4_wick
        timeBonds side sidePositive stage time))
    (Q'.mul_eqv_congr_left cubicPairHalf _ _
      (finiteGaussianThirdCumulant_openCube_bulk_cayley_trace_A2_actionV3_actionV3_wick
        timeBonds side sidePositive stage time))

/-- Complete explicit finite Wick form of the parity-normalized OLD-centered
order-six response. -/
def openCubeBulkCayleyTraceP6CompleteWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  ((openCubeBulkCayleyTraceConnectedR6WickSum
        timeBonds side sidePositive stage leftTime rightTime +
      (openCubeBulkCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage leftTime - oldCenter.c2) *
        (openCubeBulkCayleyTraceOwnA4MeanWickSum
          timeBonds side sidePositive stage rightTime - oldCenter.c4)) +
    (-oldCenter.c3) * (-oldCenter.c3)) +
  (openCubeBulkCayleyTraceOwnA4MeanWickSum
      timeBonds side sidePositive stage leftTime - oldCenter.c4) *
    (openCubeBulkCayleyTraceOwnA2MeanGramSum
      timeBonds side sidePositive stage rightTime - oldCenter.c2)

/-- Exact finite Wick certificate for the complete parity-normalized `P6`.
The theorem retains all OWN/OLD residual products and the supplied OLD cubic
center square. -/
theorem openCubeBulkCayleyTraceP6_complete_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    openCubeBulkCayleyTraceP6
        timeBonds side sidePositive stage leftTime rightTime oldCenter ≈
      openCubeBulkCayleyTraceP6CompleteWickSum
        timeBonds side sidePositive stage leftTime rightTime oldCenter := by
  have leftA2Residual :
      openCubeBulkCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c2 ≈
        openCubeBulkCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage leftTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeBulkCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage leftTime)
      (Q'.eqv_refl _)
  have rightA2Residual :
      openCubeBulkCayleyTraceOwnA2Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c2 ≈
        openCubeBulkCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage rightTime - oldCenter.c2 :=
    Q'.add_eqv_congr'
      (openCubeBulkCayleyTraceOwnA2Mean_gram
        timeBonds side sidePositive stage rightTime)
      (Q'.eqv_refl _)
  have leftA4Residual :
      openCubeBulkCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage leftTime - oldCenter.c4 ≈
        openCubeBulkCayleyTraceOwnA4MeanWickSum
          timeBonds side sidePositive stage leftTime - oldCenter.c4 :=
    Q'.add_eqv_congr'
      (openCubeBulkCayleyTraceOwnA4Mean_wick
        timeBonds side sidePositive stage leftTime)
      (Q'.eqv_refl _)
  have rightA4Residual :
      openCubeBulkCayleyTraceOwnA4Mean
          timeBonds side sidePositive stage rightTime - oldCenter.c4 ≈
        openCubeBulkCayleyTraceOwnA4MeanWickSum
          timeBonds side sidePositive stage rightTime - oldCenter.c4 :=
    Q'.add_eqv_congr'
      (openCubeBulkCayleyTraceOwnA4Mean_wick
        timeBonds side sidePositive stage rightTime)
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (openCubeBulkCayleyTraceP6_parity
      timeBonds side sidePositive stage leftTime rightTime oldCenter)
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (mul_congr leftA2Residual rightA4Residual))
        (Q'.eqv_refl _))
      (mul_congr leftA4Residual rightA2Residual))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanCompleteWick

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanCompleteWick.openCubeBulkCayleyTraceOwnA4Mean_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanCompleteWick.openCubeBulkCayleyTraceP6_complete_wick
