/-
# Radius-independent caps on the actual intrinsic Wilson form

The original placed polynomial has a two-sided Haar interval certificate.
Integration against the SAME positive selected action cancels its SAME
partition, so the normalized finite scalar retains the interval cap with
no volume or cutoff penalty. Every approximation of the existing spatial
limit is one such finite scalar at its computed three-regulator diagonal.

The cap of an intrinsic expression depends only on its spins, rational
coefficients and algebraic operations. Centering charts and reflection
change offsets but not this cap. Increasing a recorded radius while keeping
the expression fixed therefore changes no bound. This is an absolute bound on the actual original
reflected form, not an ordinary-L2 substitution or a quotient contraction.
Time nonexpansiveness, a strict bound and continuum control are separate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
import YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds (finiteValue_abs_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- No radius, placement, regulator, nome or spacing appears in this cap. -/
def intrinsicCap {base : Nat} (x : IntrinsicExpression base) : Q' :=
  windowCap x.expression

theorem intrinsicCap_nonnegative {base : Nat} (x : IntrinsicExpression base) :
    (0 : Q') ≤ intrinsicCap x :=
  (chart_interval 0 x.radius 0 x.expression
    (within_mono (by omega : x.radius ≤ 2*x.radius) _ x.within)).nonnegative

/-- Valid or otherwise, chart offset recoding leaves the cap literally unchanged. -/
theorem chart_cap {base : Nat} (H : Nat) (x : IntrinsicExpression base) :
    windowCap (chart H x) = intrinsicCap x :=
  windowCap_mapOffsets (fun offset => offset+(H-x.radius)) x.expression

/-- Actual original selected-action scalar, with arbitrary independent regulators. -/
theorem chartScalar_abs_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)
    (r stage t : Nat) :
    Q'.abs (chartScalar hw0 hw1 H e r stage t) ≤ windowCap e := by
  unfold chartScalar
  exact finiteValue_abs_bound w hw0 hw1 _ _ _ _ _ (chart_interval r H t e he) stage

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

/-- The bound holds on every actual representative term, not only eventually. -/
theorem spatialLimit_approx_abs_bound (H : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) (k : Nat) :
    Q'.abs ((spatialLimit hw0 hw1 H e he hsmall hd hs hb).approx k) ≤ windowCap e := by
  let c := spatialCauchy hw0 hw1 H e he hsmall hd hs hb
  exact chartScalar_abs_bound hw0 hw1 H e he (QMhat _ c k) (QMhat _ c k) (QMhat _ c k)

/-- Each operand contributes only its placement-independent expression cap. -/
theorem intrinsicForm_approx_abs_bound (x y : IntrinsicExpression base) (k : Nat) :
    Q'.abs ((intrinsicForm hw0 hw1 hsmall hd hs hb x y).approx k) ≤
      intrinsicCap x*intrinsicCap y := by
  let H := max x.radius y.radius
  have h := spatialLimit_approx_abs_bound hw0 hw1 hsmall hd hs hb H
    (.mul (mirror H (chart H x)) (chart H y))
    ⟨mirror_within H (chart H x), within_mono (by omega : H ≤ 2*H) _
      (chart_within H y (Nat.le_max_right _ _))⟩ k
  change Q'.abs ((intrinsicForm hw0 hw1 hsmall hd hs hb x y).approx k) ≤
    windowCap (.mul (mirror H (chart H x)) (chart H y)) at h
  simpa only [windowCap, windowCap_mirror, chart_cap] using h

/-- Absolute cap for the SAME limiting reflected pairing, independent of radii. -/
theorem intrinsicForm_abs_bound (x y : IntrinsicExpression base) :
    leEv (CReal.abs (intrinsicForm hw0 hw1 hsmall hd hs hb x y))
      (ofQ' (intrinsicCap x*intrinsicCap y)) :=
  leEv_le_ofQ'_of_approx_le (intrinsicForm_approx_abs_bound hw0 hw1 hsmall hd hs hb x y)

/-- Signed upper bound, directly usable by midpoint-doubling arguments. -/
theorem intrinsicForm_upper_bound (x y : IntrinsicExpression base) :
    leEv (intrinsicForm hw0 hw1 hsmall hd hs hb x y)
      (ofQ' (intrinsicCap x*intrinsicCap y)) :=
  leEv_le_ofQ'_of_approx_le (fun k =>
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (intrinsicForm_approx_abs_bound hw0 hw1 hsmall hd hs hb x y k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.intrinsicCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.intrinsicCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.chart_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.chartScalar_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.spatialLimit_approx_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.intrinsicForm_approx_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.intrinsicForm_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap.intrinsicForm_upper_bound
