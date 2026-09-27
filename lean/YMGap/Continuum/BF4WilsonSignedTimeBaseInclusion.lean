/-
# Spatial-base inclusion of signed-time Wilson expressions

Inclusion changes only the witnessed spatial source box. It preserves every
integer time, ordered loop, spin and rational expression operation. The
original spatial-limit inclusion theorem identifies the corresponding means;
no quotient or base-uniform Cauchy support is selected here.
-/

import YMGap.Continuum.BF4WilsonSignedTimeExpectation
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence

namespace YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation (mean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence (spatialLimit_inclusion)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Spatial source-box enlargement at unchanged signed time. -/
def inclusion {base larger : Nat} (h : base ≤ larger) :
    Expression base → Expression larger
  | .one => .one
  | .loop time value spin =>
      .loop time (recenterLoop (space := 0) (by simpa only [Nat.add_zero] using h) value) spin
  | .add e f => .add (inclusion h e) (inclusion h f)
  | .mul e f => .mul (inclusion h e) (inclusion h f)
  | .smul c e => .smul c (inclusion h e)

theorem radius_include {base larger : Nat} (h : base ≤ larger) :
    ∀ e : Expression base, radius (inclusion h e) = radius e
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e f => by
      change max (radius (inclusion h e)) (radius (inclusion h f)) = max (radius e) (radius f)
      rw [radius_include h e, radius_include h f]
  | .mul e f => by
      change max (radius (inclusion h e)) (radius (inclusion h f)) = max (radius e) (radius f)
      rw [radius_include h e, radius_include h f]
  | .smul _ e => radius_include h e

theorem include_within {base larger : Nat} (h : base ≤ larger) (H : Nat) :
    ∀ e : Expression base, Within H (inclusion h e) ↔ Within H e
  | .one => Iff.rfl
  | .loop _ _ _ => Iff.rfl
  | .add e f => and_congr (include_within h H e) (include_within h H f)
  | .mul e f => and_congr (include_within h H e) (include_within h H f)
  | .smul _ e => include_within h H e

/-- Evaluation commutes exactly with the pre-existing natural-window inclusion. -/
theorem window_include {base larger : Nat} (h : base ≤ larger) (H : Nat) :
    ∀ e : Expression base,
      window H (inclusion h e) = includeExpression h (window H e)
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e f => by
      change WindowExpression.add (window H (inclusion h e)) (window H (inclusion h f)) =
        .add (includeExpression h (window H e)) (includeExpression h (window H f))
      rw [window_include h H e, window_include h H f]
  | .mul e f => by
      change WindowExpression.mul (window H (inclusion h e)) (window H (inclusion h f)) =
        .mul (includeExpression h (window H e)) (includeExpression h (window H f))
      rw [window_include h H e, window_include h H f]
  | .smul c e => by
      change WindowExpression.smul c (window H (inclusion h e)) =
        .smul c (includeExpression h (window H e))
      rw [window_include h H e]

theorem include_reflect {base larger : Nat} (h : base ≤ larger) :
    ∀ e : Expression base, inclusion h (reflect e) = reflect (inclusion h e)
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e f => by
      change Expression.add (inclusion h (reflect e)) (inclusion h (reflect f)) =
        .add (reflect (inclusion h e)) (reflect (inclusion h f))
      rw [include_reflect h e, include_reflect h f]
  | .mul e f => by
      change Expression.mul (inclusion h (reflect e)) (inclusion h (reflect f)) =
        .mul (reflect (inclusion h e)) (reflect (inclusion h f))
      rw [include_reflect h e, include_reflect h f]
  | .smul c e => by
      change Expression.smul c (inclusion h (reflect e)) = .smul c (reflect (inclusion h e))
      rw [include_reflect h e]

theorem include_forward {base larger : Nat} (h : base ≤ larger) (n : Nat) :
    ∀ e : Expression base, inclusion h (forward n e) = forward n (inclusion h e)
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e f => by
      change Expression.add (inclusion h (forward n e)) (inclusion h (forward n f)) =
        .add (forward n (inclusion h e)) (forward n (inclusion h f))
      rw [include_forward h n e, include_forward h n f]
  | .mul e f => by
      change Expression.mul (inclusion h (forward n e)) (inclusion h (forward n f)) =
        .mul (forward n (inclusion h e)) (forward n (inclusion h f))
      rw [include_forward h n e, include_forward h n f]
  | .smul c e => by
      change Expression.smul c (inclusion h (forward n e)) = .smul c (forward n (inclusion h e))
      rw [include_forward h n e]

theorem include_backward {base larger : Nat} (h : base ≤ larger) (n : Nat) :
    ∀ e : Expression base, inclusion h (backward n e) = backward n (inclusion h e)
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e f => by
      change Expression.add (inclusion h (backward n e)) (inclusion h (backward n f)) =
        .add (backward n (inclusion h e)) (backward n (inclusion h f))
      rw [include_backward h n e, include_backward h n f]
  | .mul e f => by
      change Expression.mul (inclusion h (backward n e)) (inclusion h (backward n f)) =
        .mul (backward n (inclusion h e)) (backward n (inclusion h f))
      rw [include_backward h n e, include_backward h n f]
  | .smul c e => by
      change Expression.smul c (inclusion h (backward n e)) = .smul c (backward n (inclusion h e))
      rw [include_backward h n e]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

/-- The SAME original spatial expectation after enlarging only its finite
source box. The chosen representatives may have different Cauchy moduli. -/
theorem mean_include {base larger : Nat} (h : base ≤ larger) (hb : 0 < base)
    (e : Expression base) :
    Equiv (mean hw0 hw1 hsmall hd hs hb e)
      (mean hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h) (inclusion h e)) := by
  have hp := spatialLimit_inclusion hw0 hw1 hsmall hd hs h (radius e) hb
    (window (radius e) e) (window_within (radius e) e (within_radius e))
  simpa only [mean, radius_include, window_include] using hp

end YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion

#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.inclusion
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.radius_include
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.include_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.window_include
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.include_reflect
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.include_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.include_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion.mean_include
