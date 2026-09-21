/-
# Time-zero offset laws for signed Wilson expressions

An expression supported at time zero has no hidden temporal offsets: applying
an arbitrary offset map is the same syntax as shifting the whole expression by
the image of zero.  The reverse and mirror formulas below are consequently
exact even with truncated natural subtraction.

These are purely syntactic identities.  They do not assert stationarity,
reflection positivity, a covariance estimate, or any continuum conclusion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow

namespace YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow (reverse)

/-- On time-zero syntax, an arbitrary offset map is its single common shift. -/
theorem mapOffsets_timeZero {width : Nat} (f : Nat → Nat) :
    ∀ e : WindowExpression width, Within 0 e →
      mapOffsets f e = shift (f 0) e
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have hoffset : offset = 0 := Nat.eq_zero_of_le_zero he
      subst offset
      simp only [shift, mapOffsets, Nat.zero_add]
  | .add e g, he => by
      change WindowExpression.add (mapOffsets f e) (mapOffsets f g) =
        WindowExpression.add (shift (f 0) e) (shift (f 0) g)
      rw [mapOffsets_timeZero f e he.1, mapOffsets_timeZero f g he.2]
  | .mul e g, he => by
      change WindowExpression.mul (mapOffsets f e) (mapOffsets f g) =
        WindowExpression.mul (shift (f 0) e) (shift (f 0) g)
      rw [mapOffsets_timeZero f e he.1, mapOffsets_timeZero f g he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mapOffsets f e) =
        WindowExpression.smul c (shift (f 0) e)
      rw [mapOffsets_timeZero f e he]

/-- Reversing a shifted time-zero expression leaves the common offset `R-d`. -/
theorem reverse_shift_timeZero {width : Nat} (R d : Nat) :
    ∀ e : WindowExpression width, Within 0 e →
      reverse R (shift d e) = shift (R-d) e
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have hoffset : offset = 0 := Nat.eq_zero_of_le_zero he
      subst offset
      simp only [reverse, shift, mapOffsets, Nat.zero_add]
  | .add e g, he => by
      change WindowExpression.add
          (reverse R (shift d e)) (reverse R (shift d g)) =
        WindowExpression.add (shift (R-d) e) (shift (R-d) g)
      rw [reverse_shift_timeZero R d e he.1, reverse_shift_timeZero R d g he.2]
  | .mul e g, he => by
      change WindowExpression.mul
          (reverse R (shift d e)) (reverse R (shift d g)) =
        WindowExpression.mul (shift (R-d) e) (shift (R-d) g)
      rw [reverse_shift_timeZero R d e he.1, reverse_shift_timeZero R d g he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (reverse R (shift d e)) =
        WindowExpression.smul c (shift (R-d) e)
      rw [reverse_shift_timeZero R d e he]

/-- Mirroring a shifted time-zero expression leaves the common offset `2*H-d`. -/
theorem mirror_shift_timeZero {width : Nat} (H d : Nat) :
    ∀ e : WindowExpression width, Within 0 e →
      mirror H (shift d e) = shift (2*H-d) e
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have hoffset : offset = 0 := Nat.eq_zero_of_le_zero he
      subst offset
      simp only [mirror, shift, mapOffsets, Nat.zero_add]
  | .add e g, he => by
      change WindowExpression.add
          (mirror H (shift d e)) (mirror H (shift d g)) =
        WindowExpression.add (shift (2*H-d) e) (shift (2*H-d) g)
      rw [mirror_shift_timeZero H d e he.1, mirror_shift_timeZero H d g he.2]
  | .mul e g, he => by
      change WindowExpression.mul
          (mirror H (shift d e)) (mirror H (shift d g)) =
        WindowExpression.mul (shift (2*H-d) e) (shift (2*H-d) g)
      rw [mirror_shift_timeZero H d e he.1, mirror_shift_timeZero H d g he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mirror H (shift d e)) =
        WindowExpression.smul c (shift (2*H-d) e)
      rw [mirror_shift_timeZero H d e he]

/-- A time-zero expression shifted by `n` lies in the time-`n` window. -/
theorem timeZero_shift_within {width : Nat} (n : Nat)
    (e : WindowExpression width) (he : Within 0 e) : Within n (shift n e) := by
  simpa using shift_within 0 n e he

end YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws

#print axioms YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws.mapOffsets_timeZero
#print axioms YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws.reverse_shift_timeZero
#print axioms YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws.mirror_shift_timeZero
#print axioms YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws.timeZero_shift_within
