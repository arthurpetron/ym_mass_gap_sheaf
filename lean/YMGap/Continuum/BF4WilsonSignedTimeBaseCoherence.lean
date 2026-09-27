/-
# Coherence of spatial-base inclusion for signed Wilson syntax

Every inclusion leaves signed time, spin and the original ordered loop word
unchanged. Zero spatial recentering is therefore reflexive and composes
exactly, before contextual or OS quotients are formed.
-/

import YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion

namespace YMGap.Continuum.BF4WilsonSignedTimeBaseCoherence

set_option autoImplicit false

open YMGap.Continuum.BF4WilsonSignedTimeExpression (Expression)
open YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion (inclusion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
  (includeLoop_start includeLoop_edges)

private theorem loop_ext {base : Nat} (x y : SourceLoop base)
    (hs : x.start = y.start) (he : x.edges = y.edges) : x = y := by
  cases x
  cases y
  cases hs
  cases he
  rfl

/-- Inclusion at the same spatial base is literal identity on signed syntax. -/
theorem inclusion_refl {base : Nat} :
    ∀ e : Expression base, inclusion (Nat.le_refl base) e = e
  | .one => rfl
  | .loop time value spin => by
      change Expression.loop time
          (recenterLoop (space := 0)
            (by simpa only [Nat.add_zero] using (Nat.le_refl base)) value) spin =
        .loop time value spin
      congr 1
      exact loop_ext _ _ (includeLoop_start (Nat.le_refl base) value)
        (includeLoop_edges (Nat.le_refl base) value)
  | .add e f => by
      change Expression.add (inclusion (Nat.le_refl base) e)
          (inclusion (Nat.le_refl base) f) = .add e f
      rw [inclusion_refl e, inclusion_refl f]
  | .mul e f => by
      change Expression.mul (inclusion (Nat.le_refl base) e)
          (inclusion (Nat.le_refl base) f) = .mul e f
      rw [inclusion_refl e, inclusion_refl f]
  | .smul c e => by
      change Expression.smul c (inclusion (Nat.le_refl base) e) = .smul c e
      rw [inclusion_refl e]

/-- Two witnessed spatial enlargements equal their direct enlargement. -/
theorem inclusion_trans {base middle larger : Nat}
    (hfirst : base ≤ middle) (hsecond : middle ≤ larger) :
    ∀ e : Expression base,
      inclusion hsecond (inclusion hfirst e) =
        inclusion (Nat.le_trans hfirst hsecond) e
  | .one => rfl
  | .loop time value spin => by
      change Expression.loop time
          (recenterLoop (space := 0)
            (by simpa only [Nat.add_zero] using hsecond)
            (recenterLoop (space := 0)
              (by simpa only [Nat.add_zero] using hfirst) value)) spin =
        .loop time (recenterLoop (space := 0)
          (by simpa only [Nat.add_zero] using (Nat.le_trans hfirst hsecond)) value) spin
      congr 1
      apply loop_ext
      · exact (includeLoop_start hsecond _).trans
          ((includeLoop_start hfirst value).trans
            (includeLoop_start (Nat.le_trans hfirst hsecond) value).symm)
      · exact (includeLoop_edges hsecond _).trans
          ((includeLoop_edges hfirst value).trans
            (includeLoop_edges (Nat.le_trans hfirst hsecond) value).symm)
  | .add e f => by
      change Expression.add (inclusion hsecond (inclusion hfirst e))
          (inclusion hsecond (inclusion hfirst f)) =
        .add (inclusion (Nat.le_trans hfirst hsecond) e)
          (inclusion (Nat.le_trans hfirst hsecond) f)
      rw [inclusion_trans hfirst hsecond e, inclusion_trans hfirst hsecond f]
  | .mul e f => by
      change Expression.mul (inclusion hsecond (inclusion hfirst e))
          (inclusion hsecond (inclusion hfirst f)) =
        .mul (inclusion (Nat.le_trans hfirst hsecond) e)
          (inclusion (Nat.le_trans hfirst hsecond) f)
      rw [inclusion_trans hfirst hsecond e, inclusion_trans hfirst hsecond f]
  | .smul c e => by
      change Expression.smul c (inclusion hsecond (inclusion hfirst e)) =
        .smul c (inclusion (Nat.le_trans hfirst hsecond) e)
      rw [inclusion_trans hfirst hsecond e]

end YMGap.Continuum.BF4WilsonSignedTimeBaseCoherence

#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseCoherence.inclusion_refl
#print axioms YMGap.Continuum.BF4WilsonSignedTimeBaseCoherence.inclusion_trans
