/-
# The actual one-step Wilson form has an odd-window source

For a radius-R expression, the common intrinsic chart R+1 represents the
one-step form by an upper reversed copy on slices R+1 through 2R+1 and the
original copy on slices 0 through R. This is an exact signed-expression
identity, retaining the order inside every Wilson loop.

The displayed chart has length 2R+2, not 2R+1. Its finite symmetric external
depths therefore trim to unequal depths (t,t+1). Only the already proved
original joint-limit padding theorem removes the extra slice. Consequently
the balanced odd-window joint limits, after spatial recentering, converge
to the SAME existing intrinsic one-step form. No finite stationarity,
positivity, strict bound, new state or continuum claim is assumed here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Reverse slice offsets in a window; do not reverse the ordered loop words. -/
def reverse {base : Nat} (R : Nat) (e : WindowExpression base) : WindowExpression base :=
  mapOffsets (fun offset => R-offset) e

theorem reverse_within {base : Nat} (R : Nat) :
    ∀ e : WindowExpression base, Within R (reverse R e)
  | .one => True.intro
  | .loop _ _ _ => Nat.sub_le _ _
  | .add e f => ⟨reverse_within R e, reverse_within R f⟩
  | .mul e f => ⟨reverse_within R e, reverse_within R f⟩
  | .smul _ e => reverse_within R e

/-- The support guard excludes information lost by truncated subtraction. -/
theorem reverse_reverse {base : Nat} (R : Nat) :
    ∀ e : WindowExpression base, Within R e → reverse R (reverse R e) = e
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have h : R-(R-offset)=offset := by change offset ≤ R at he; omega
      change WindowExpression.loop (R-(R-offset)) value spin = .loop offset value spin
      rw [h]
  | .add e f, he => by
      change WindowExpression.add (reverse R (reverse R e)) (reverse R (reverse R f)) = .add e f
      rw [reverse_reverse R e he.1, reverse_reverse R f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (reverse R (reverse R e)) (reverse R (reverse R f)) = .mul e f
      rw [reverse_reverse R e he.1, reverse_reverse R f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (reverse R (reverse R e)) = .smul c e
      rw [reverse_reverse R e he]

/-- Upper copy first, exactly as in the existing reflected form. -/
def oddPair {base : Nat} (R : Nat) (e : WindowExpression base) : WindowExpression base :=
  .mul (shift (R+1) (reverse R e)) e

theorem oddPair_within {base : Nat} (R : Nat) (e : WindowExpression base)
    (he : Within R e) : Within (2*R+1) (oddPair R e) := by
  constructor
  · exact within_mono (by omega : R+(R+1) ≤ 2*R+1) _
      (shift_within R (R+1) (reverse R e) (reverse_within R e))
  · exact within_mono (by omega : R ≤ 2*R+1) e he

/-- The actual signed source is a pair of separated windows with one
central transition. Commutativity is only that of scalar polynomials. -/
theorem oddPair_source {base : Nat} (blocks R : Nat) (e : WindowExpression base) :
    PaddedPolynomialCoeffEqv blocks (sourcePolynomial (oddPair R e))
      (polyMul (sourcePolynomial e)
        (liftBoundary ((R+1)*(baseLinks base).length) (sourcePolynomial (reverse R e)))) :=
  ((source_shift blocks (R+1) (reverse R e)).mul (.refl blocks (sourcePolynomial e))).trans
    (.of_coeff (RatPolyCoeffEqv.mul_comm _ _))

private theorem mirror_shift_one {base : Nat} (R : Nat) :
    ∀ e : WindowExpression base, Within R e →
      mirror (R+1) (shift 1 e) = shift (R+1) (reverse R e)
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have h : 2*(R+1)-(offset+1) = (R-offset)+(R+1) := by
        change offset ≤ R at he
        omega
      change WindowExpression.loop (2*(R+1)-(offset+1)) value spin =
        .loop ((R-offset)+(R+1)) value spin
      rw [h]
  | .add e f, he => by
      change WindowExpression.add (mirror (R+1) (shift 1 e)) (mirror (R+1) (shift 1 f)) =
        .add (shift (R+1) (reverse R e)) (shift (R+1) (reverse R f))
      rw [mirror_shift_one R e he.1, mirror_shift_one R f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (mirror (R+1) (shift 1 e)) (mirror (R+1) (shift 1 f)) =
        .mul (shift (R+1) (reverse R e)) (shift (R+1) (reverse R f))
      rw [mirror_shift_one R e he.1, mirror_shift_one R f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mirror (R+1) (shift 1 e)) =
        .smul c (shift (R+1) (reverse R e))
      rw [mirror_shift_one R e he]

/-- Exact common-chart geometry for the CURRENT one-step time map. -/
theorem oneStep_chart_source {base : Nat} (x : IntrinsicExpression base) :
    WindowExpression.mul (mirror (x.radius+1) (chart (x.radius+1) x))
      (chart (x.radius+1) (advance 1 x)) = oddPair x.radius x.expression := by
  rw [chart_advance_add_center, chart_self]
  change WindowExpression.mul (mirror (x.radius+1) (shift (x.radius+1-x.radius) x.expression))
    x.expression = oddPair x.radius x.expression
  rw [show x.radius+1-x.radius=1 by omega, mirror_shift_one x.radius x.expression x.within]
  rfl

theorem centered_oddPair {base : Nat} (r R : Nat) (e : WindowExpression base) :
    centeredExpression r (oddPair R e) = oddPair R (centeredExpression r e) := by
  simp only [centeredExpression, oddPair, reverse, shift, recenterExpression, recenter_mapOffsets]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

attribute [local irreducible] intrinsicForm spatialLimit originalJointLimit

/-- The existing form is the existing even-chart spatial limit; its
insertion fits in the strictly shorter odd window. -/
theorem intrinsicForm_oneStep_oddPair (x : IntrinsicExpression base) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb x (advance 1 x))
      (spatialLimit hw0 hw1 (x.radius+1) (oddPair x.radius x.expression)
        (within_mono (by omega : 2*x.radius+1 ≤ 2*(x.radius+1)) _
          (oddPair_within x.radius x.expression x.within)) hsmall hd hs hb) := by
  have h := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x (advance 1 x) (x.radius+1)
    (by omega) (Nat.le_refl _)
  simpa only [form, oneStep_chart_source] using h

/-- Balanced odd-window joint limits converge to the SAME intrinsic form.
The extra displayed slice is removed after the time/cutoff limit, never
by equating finite symmetric and unequal boundary depths. -/
theorem oddJointLimits_oneStep_converge (x : IntrinsicExpression base) :
    ConvergesTo
      (fun r => originalJointLimit hw0 hw1 (2*x.radius+1)
        (centeredExpression r (oddPair x.radius x.expression))
        ((centered_within r (2*x.radius+1) _).mpr
          (oddPair_within x.radius x.expression x.within)))
      (intrinsicForm hw0 hw1 hsmall hd hs hb x (advance 1 x)) := by
  have hc := jointLimits_spatial_converge hw0 hw1 (x.radius+1) (oddPair x.radius x.expression)
    (within_mono (by omega : 2*x.radius+1 ≤ 2*(x.radius+1)) _
      (oddPair_within x.radius x.expression x.within)) hsmall hd hs hb
  apply ArctanTrigConvergesProof.convergesTo_of_equiv
    (hLL' := (intrinsicForm_oneStep_oddPair hw0 hw1 hsmall hd hs hb x).symm)
  apply TrigAddCReal.convergesTo_congr_seq (hs := hc)
  intro r
  have h := originalJoint_padding hw0 hw1 (2*x.radius+1) 0 1
    (centeredExpression r (oddPair x.radius x.expression))
    ((centered_within r (2*x.radius+1) _).mpr
      (oddPair_within x.radius x.expression x.within))
  simpa only [shift_zero, show 2*x.radius+1+0+1=2*(x.radius+1) by omega] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.reverse_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.reverse_reverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.oddPair_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.oddPair_source
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.oneStep_chart_source
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.centered_oddPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.intrinsicForm_oneStep_oddPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow.oddJointLimits_oneStep_converge
