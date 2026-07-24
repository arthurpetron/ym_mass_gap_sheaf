/-
# Core-B base row at the worst-coupling endpoint

The general base-row theorem in `CoreBResidualBaseUniform` is stated on the
strong-coupling simplex `4w <= 1`.  The Core-B cross-ratio consumer instead
orients its determinant from the fixed endpoint `wH = 1/2` down to the
physical coupling.  This module records the small endpoint adapter: although
`4wH <= 1` is false, the reduced residual only needs

  2 * wH^2 <= 1  and  3 * wH^2 <= 1,

which hold exactly because `wH^2 = 1/4`.

This is an algebraic endpoint specialization.  It does not prove the
all-row cumulative residual and does not inhabit `CrossRatioMonotone` or any
frontier bundle.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Continuum.CoreBResidualBaseUniform

namespace YMGap.Continuum.CoreBResidualBaseWorstEndpoint

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualBaseUniform

/-- Every base-row residual is nonnegative when its upper coupling is the
fixed worst-case endpoint `wH = 1/2`.  The proof uses the exact square bound
`wH^2 = 1/4`, rather than the inapplicable linear cap `4wH <= 1`. -/
theorem boundaryResidualAt_zero_nonneg_wH {h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhH : h ≤ wH) (r : Nat) :
    (0 : Q') ≤ boundaryResidualAt wH h 0 r := by
  cases r with
  | zero =>
      exact CoreBResidualAbel.boundaryResidualAt_zero_zero_nonneg hh0 hhH
  | succ r =>
      let x := qpow wH 2
      let y := qpow h 2
      have hx0 : (0 : Q') ≤ x := qpow_nonneg wH (by decide) 2
      have hy0 : (0 : Q') ≤ y := qpow_nonneg h hh0 2
      have hyx : y ≤ x := qpow_mono hh0 hhH 2
      have h2x : (2 : Q') * x ≤ (1 : Q') := by
        decide
      have h3x : (3 : Q') * x ≤ (1 : Q') := by
        decide
      have hred : (0 : Q') ≤ reducedPart x y (r + 1) :=
        reducedPart_nonneg hx0 hy0 hyx h2x h3x (r + 1)
      have hdiff : (0 : Q') ≤ x + -y := Q'.sub_nonneg_of_le hyx
      have hcommon : (0 : Q') ≤
          qpow wH (commonExp (r + 1)) * qpow h (commonExp (r + 1)) :=
        Q'.mul_nonneg _ _
          (qpow_nonneg wH (by decide) _)
          (qpow_nonneg h hh0 _)
      have hfact := boundaryResidualAt_zero_factor (w := wH) (h := h)
        (r := r + 1) (by omega)
      exact Q'.le_trans' _ _ _
        (Q'.mul_nonneg _ _ hcommon (Q'.mul_nonneg _ _ hdiff hred))
        (Q'.ge_of_eqv hfact)

#print axioms boundaryResidualAt_zero_nonneg_wH

end YMGap.Continuum.CoreBResidualBaseWorstEndpoint
