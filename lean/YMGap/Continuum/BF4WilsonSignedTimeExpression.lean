/-
# Signed-time syntax for original spatial Wilson expressions

Integer times give literal inverse translations and reflection before any
quotient is formed. A symmetric-window evaluation is used only with an
explicit support bound, so `Int.toNat` never truncates a generator time.
This is expression syntax, not an associative algebra or an OS quotient.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow

namespace YMGap.Continuum.BF4WilsonSignedTimeExpression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression mirror)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)

inductive Expression (base : Nat) : Type where
  | one : Expression base
  | loop (time : Int) (value : SourceLoop base) (spin : Nat) : Expression base
  | add : Expression base → Expression base → Expression base
  | mul : Expression base → Expression base → Expression base
  | smul : Q' → Expression base → Expression base

def Within {base : Nat} (H : Nat) : Expression base → Prop
  | .one => True
  | .loop time _ _ => -(H : Int) ≤ time ∧ time ≤ (H : Int)
  | .add e f => Within H e ∧ Within H f
  | .mul e f => Within H e ∧ Within H f
  | .smul _ e => Within H e

/-- A computable symmetric radius for every finite expression. -/
def radius {base : Nat} : Expression base → Nat
  | .one => 0
  | .loop time _ _ => time.natAbs
  | .add e f => max (radius e) (radius f)
  | .mul e f => max (radius e) (radius f)
  | .smul _ e => radius e

theorem within_mono {base H K : Nat} (hHK : H ≤ K) :
    ∀ e : Expression base, Within H e → Within K e
  | .one, _ => True.intro
  | .loop time _ _, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change -(K : Int) ≤ time ∧ time ≤ (K : Int)
      constructor <;> omega
  | .add e f, he => ⟨within_mono hHK e he.1, within_mono hHK f he.2⟩
  | .mul e f, he => ⟨within_mono hHK e he.1, within_mono hHK f he.2⟩
  | .smul _ e, he => within_mono hHK e he

theorem within_radius {base : Nat} :
    ∀ e : Expression base, Within (radius e) e
  | .one => True.intro
  | .loop time _ _ => by
      change -(time.natAbs : Int) ≤ time ∧ time ≤ (time.natAbs : Int)
      have hp : time ≤ (time.natAbs : Int) := Int.le_natAbs
      have hn : -time ≤ (time.natAbs : Int) := by
        simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -time))
      exact ⟨by omega, hp⟩
  | .add e f =>
      ⟨within_mono (Nat.le_max_left _ _) e (within_radius e),
        within_mono (Nat.le_max_right _ _) f (within_radius f)⟩
  | .mul e f =>
      ⟨within_mono (Nat.le_max_left _ _) e (within_radius e),
        within_mono (Nat.le_max_right _ _) f (within_radius f)⟩
  | .smul _ e => within_radius e

theorem radius_le_of_within {base : Nat} (H : Nat) :
    ∀ e : Expression base, Within H e → radius e ≤ H
  | .one, _ => Nat.zero_le _
  | .loop time _ _, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      cases time with
      | ofNat n =>
          change -(H : Int) ≤ (n : Int) ∧ (n : Int) ≤ (H : Int) at he
          change n ≤ H
          omega
      | negSucc n =>
          change n+1 ≤ H
          omega
  | .add e f, he => Nat.max_le.mpr
      ⟨radius_le_of_within H e he.1, radius_le_of_within H f he.2⟩
  | .mul e f, he => Nat.max_le.mpr
      ⟨radius_le_of_within H e he.1, radius_le_of_within H f he.2⟩
  | .smul _ e, he => radius_le_of_within H e he

/-- Literal natural-offset realization in a supplied symmetric window. -/
def window {base : Nat} (H : Nat) : Expression base → WindowExpression base
  | .one => .one
  | .loop time value spin => .loop (((H : Int)+time).toNat) value spin
  | .add e f => .add (window H e) (window H f)
  | .mul e f => .mul (window H e) (window H f)
  | .smul c e => .smul c (window H e)

theorem window_within {base : Nat} (H : Nat) :
    ∀ e : Expression base, Within H e →
      BF4ExactSlabFixedSpatialWilsonWindow.Within (2*H) (window H e)
  | .one, _ => True.intro
  | .loop time _ _, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change (((H : Int)+time).toNat) ≤ 2*H
      omega
  | .add e f, he => ⟨window_within H e he.1, window_within H f he.2⟩
  | .mul e f, he => ⟨window_within H e he.1, window_within H f he.2⟩
  | .smul _ e, he => window_within H e he

/-- Enlarging the center shifts every offset by the same natural amount. -/
theorem window_enlarge {base : Nat} (H d : Nat) :
    ∀ e : Expression base, Within H e → window (H+d) e = shift d (window H e)
  | .one, _ => rfl
  | .loop time value spin, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change WindowExpression.loop (((H+d : Nat) : Int)+time).toNat value spin =
        .loop ((((H : Int)+time).toNat)+d) value spin
      congr 1
      omega
  | .add e f, he => by
      change WindowExpression.add (window (H+d) e) (window (H+d) f) =
        .add (shift d (window H e)) (shift d (window H f))
      rw [window_enlarge H d e he.1, window_enlarge H d f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (window (H+d) e) (window (H+d) f) =
        .mul (shift d (window H e)) (shift d (window H f))
      rw [window_enlarge H d e he.1, window_enlarge H d f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (window (H+d) e) = .smul c (shift d (window H e))
      rw [window_enlarge H d e he]

def reflect {base : Nat} : Expression base → Expression base
  | .one => .one
  | .loop time value spin => .loop (-time) value spin
  | .add e f => .add (reflect e) (reflect f)
  | .mul e f => .mul (reflect e) (reflect f)
  | .smul c e => .smul c (reflect e)

/-- Positive transfer-time direction agrees with radius advance on stages. -/
def forward {base : Nat} (n : Nat) : Expression base → Expression base
  | .one => .one
  | .loop time value spin => .loop (time-(n : Int)) value spin
  | .add e f => .add (forward n e) (forward n f)
  | .mul e f => .mul (forward n e) (forward n f)
  | .smul c e => .smul c (forward n e)

def backward {base : Nat} (n : Nat) : Expression base → Expression base
  | .one => .one
  | .loop time value spin => .loop (time+(n : Int)) value spin
  | .add e f => .add (backward n e) (backward n f)
  | .mul e f => .mul (backward n e) (backward n f)
  | .smul c e => .smul c (backward n e)

theorem reflect_within {base : Nat} (H : Nat) :
    ∀ e : Expression base, Within H e → Within H (reflect e)
  | .one, _ => True.intro
  | .loop time _ _, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change -(H : Int) ≤ -time ∧ -time ≤ (H : Int)
      constructor <;> omega
  | .add e f, he => ⟨reflect_within H e he.1, reflect_within H f he.2⟩
  | .mul e f, he => ⟨reflect_within H e he.1, reflect_within H f he.2⟩
  | .smul _ e, he => reflect_within H e he

theorem forward_within {base : Nat} (H n : Nat) :
    ∀ e : Expression base, Within H e → Within (H+n) (forward n e)
  | .one, _ => True.intro
  | .loop time _ _, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change -((H+n : Nat) : Int) ≤ time-(n : Int) ∧ time-(n : Int) ≤ ((H+n : Nat) : Int)
      constructor <;> omega
  | .add e f, he => ⟨forward_within H n e he.1, forward_within H n f he.2⟩
  | .mul e f, he => ⟨forward_within H n e he.1, forward_within H n f he.2⟩
  | .smul _ e, he => forward_within H n e he

theorem backward_within {base : Nat} (H n : Nat) :
    ∀ e : Expression base, Within H e → Within (H+n) (backward n e)
  | .one, _ => True.intro
  | .loop time _ _, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change -((H+n : Nat) : Int) ≤ time+(n : Int) ∧ time+(n : Int) ≤ ((H+n : Nat) : Int)
      constructor <;> omega
  | .add e f, he => ⟨backward_within H n e he.1, backward_within H n f he.2⟩
  | .mul e f, he => ⟨backward_within H n e he.1, backward_within H n f he.2⟩
  | .smul _ e, he => backward_within H n e he

theorem window_reflect {base : Nat} (H : Nat) :
    ∀ e : Expression base, Within H e → window H (reflect e) = mirror H (window H e)
  | .one, _ => rfl
  | .loop time value spin, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change WindowExpression.loop (((H : Int)-time).toNat) value spin =
        .loop (2*H-(((H : Int)+time).toNat)) value spin
      congr 1
      omega
  | .add e f, he => by
      change WindowExpression.add (window H (reflect e)) (window H (reflect f)) =
        .add (mirror H (window H e)) (mirror H (window H f))
      rw [window_reflect H e he.1, window_reflect H f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (window H (reflect e)) (window H (reflect f)) =
        .mul (mirror H (window H e)) (mirror H (window H f))
      rw [window_reflect H e he.1, window_reflect H f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (window H (reflect e)) = .smul c (mirror H (window H e))
      rw [window_reflect H e he]

theorem window_forward {base : Nat} (H n : Nat) :
    ∀ e : Expression base, Within H e → window (H+n) (forward n e) = window H e
  | .one, _ => rfl
  | .loop time value spin, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change WindowExpression.loop ((((H+n : Nat) : Int)+(time-(n : Int))).toNat) value spin =
        .loop (((H : Int)+time).toNat) value spin
      congr 1
      omega
  | .add e f, he => by
      change WindowExpression.add (window (H+n) (forward n e)) (window (H+n) (forward n f)) =
        .add (window H e) (window H f)
      rw [window_forward H n e he.1, window_forward H n f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (window (H+n) (forward n e)) (window (H+n) (forward n f)) =
        .mul (window H e) (window H f)
      rw [window_forward H n e he.1, window_forward H n f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (window (H+n) (forward n e)) = .smul c (window H e)
      rw [window_forward H n e he]

theorem window_backward {base : Nat} (H n : Nat) :
    ∀ e : Expression base, Within H e →
      window (H+n) (backward n e) = shift (2*n) (window H e)
  | .one, _ => rfl
  | .loop time value spin, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change WindowExpression.loop ((((H+n : Nat) : Int)+(time+(n : Int))).toNat) value spin =
        .loop ((((H : Int)+time).toNat)+(2*n)) value spin
      congr 1
      omega
  | .add e f, he => by
      change WindowExpression.add (window (H+n) (backward n e)) (window (H+n) (backward n f)) =
        .add (shift (2*n) (window H e)) (shift (2*n) (window H f))
      rw [window_backward H n e he.1, window_backward H n f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (window (H+n) (backward n e)) (window (H+n) (backward n f)) =
        .mul (shift (2*n) (window H e)) (shift (2*n) (window H f))
      rw [window_backward H n e he.1, window_backward H n f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (window (H+n) (backward n e)) =
        .smul c (shift (2*n) (window H e))
      rw [window_backward H n e he]

theorem reflect_reflect {base : Nat} : ∀ e : Expression base, reflect (reflect e) = e
  | .one => rfl
  | .loop time value spin => by
      change Expression.loop (-(-time)) value spin = .loop time value spin
      congr 1
      omega
  | .add e f => by
      change Expression.add (reflect (reflect e)) (reflect (reflect f)) = _
      rw [reflect_reflect e, reflect_reflect f]
  | .mul e f => by
      change Expression.mul (reflect (reflect e)) (reflect (reflect f)) = _
      rw [reflect_reflect e, reflect_reflect f]
  | .smul c e => by
      change Expression.smul c (reflect (reflect e)) = _
      rw [reflect_reflect e]

theorem backward_forward {base : Nat} (n : Nat) :
    ∀ e : Expression base, backward n (forward n e) = e
  | .one => rfl
  | .loop time value spin => by
      change Expression.loop ((time-(n : Int))+(n : Int)) value spin = .loop time value spin
      congr 1
      omega
  | .add e f => by
      change Expression.add (backward n (forward n e)) (backward n (forward n f)) = _
      rw [backward_forward n e, backward_forward n f]
  | .mul e f => by
      change Expression.mul (backward n (forward n e)) (backward n (forward n f)) = _
      rw [backward_forward n e, backward_forward n f]
  | .smul c e => by
      change Expression.smul c (backward n (forward n e)) = _
      rw [backward_forward n e]

theorem forward_backward {base : Nat} (n : Nat) :
    ∀ e : Expression base, forward n (backward n e) = e
  | .one => rfl
  | .loop time value spin => by
      change Expression.loop ((time+(n : Int))-(n : Int)) value spin = .loop time value spin
      congr 1
      omega
  | .add e f => by
      change Expression.add (forward n (backward n e)) (forward n (backward n f)) = _
      rw [forward_backward n e, forward_backward n f]
  | .mul e f => by
      change Expression.mul (forward n (backward n e)) (forward n (backward n f)) = _
      rw [forward_backward n e, forward_backward n f]
  | .smul c e => by
      change Expression.smul c (forward n (backward n e)) = _
      rw [forward_backward n e]

theorem reflect_forward {base : Nat} (n : Nat) :
    ∀ e : Expression base, reflect (forward n e) = backward n (reflect e)
  | .one => rfl
  | .loop time value spin => by
      change Expression.loop (-(time-(n : Int))) value spin =
        .loop (-time+(n : Int)) value spin
      congr 1
      omega
  | .add e f => by
      change Expression.add (reflect (forward n e)) (reflect (forward n f)) =
        .add (backward n (reflect e)) (backward n (reflect f))
      rw [reflect_forward n e, reflect_forward n f]
  | .mul e f => by
      change Expression.mul (reflect (forward n e)) (reflect (forward n f)) =
        .mul (backward n (reflect e)) (backward n (reflect f))
      rw [reflect_forward n e, reflect_forward n f]
  | .smul c e => by
      change Expression.smul c (reflect (forward n e)) =
        .smul c (backward n (reflect e))
      rw [reflect_forward n e]

theorem reflect_backward {base : Nat} (n : Nat) :
    ∀ e : Expression base, reflect (backward n e) = forward n (reflect e)
  | .one => rfl
  | .loop time value spin => by
      change Expression.loop (-(time+(n : Int))) value spin =
        .loop (-time-(n : Int)) value spin
      congr 1
      omega
  | .add e f => by
      change Expression.add (reflect (backward n e)) (reflect (backward n f)) =
        .add (forward n (reflect e)) (forward n (reflect f))
      rw [reflect_backward n e, reflect_backward n f]
  | .mul e f => by
      change Expression.mul (reflect (backward n e)) (reflect (backward n f)) =
        .mul (forward n (reflect e)) (forward n (reflect f))
      rw [reflect_backward n e, reflect_backward n f]
  | .smul c e => by
      change Expression.smul c (reflect (backward n e)) =
        .smul c (forward n (reflect e))
      rw [reflect_backward n e]

/-- Every natural-offset expression can be recentered as signed syntax. -/
def ofWindow {base : Nat} (H : Nat) : WindowExpression base → Expression base
  | .one => .one
  | .loop offset value spin => .loop ((offset : Int)-(H : Int)) value spin
  | .add e f => .add (ofWindow H e) (ofWindow H f)
  | .mul e f => .mul (ofWindow H e) (ofWindow H f)
  | .smul c e => .smul c (ofWindow H e)

/-- Radius advance of a positive-time source is literal forward signed time. -/
theorem ofWindow_forward {base : Nat} (H n : Nat) :
    ∀ e : WindowExpression base, ofWindow (H+n) e = forward n (ofWindow H e)
  | .one => rfl
  | .loop offset value spin => by
      change Expression.loop ((offset : Int)-((H+n : Nat) : Int)) value spin =
        .loop (((offset : Int)-(H : Int))-(n : Int)) value spin
      congr 1
      omega
  | .add e f => by
      change Expression.add (ofWindow (H+n) e) (ofWindow (H+n) f) =
        .add (forward n (ofWindow H e)) (forward n (ofWindow H f))
      rw [ofWindow_forward H n e, ofWindow_forward H n f]
  | .mul e f => by
      change Expression.mul (ofWindow (H+n) e) (ofWindow (H+n) f) =
        .mul (forward n (ofWindow H e)) (forward n (ofWindow H f))
      rw [ofWindow_forward H n e, ofWindow_forward H n f]
  | .smul c e => by
      change Expression.smul c (ofWindow (H+n) e) = .smul c (forward n (ofWindow H e))
      rw [ofWindow_forward H n e]

theorem ofWindow_within {base : Nat} (H : Nat) :
    ∀ e : WindowExpression base, BF4ExactSlabFixedSpatialWilsonWindow.Within (2*H) e →
      Within H (ofWindow H e)
  | .one, _ => True.intro
  | .loop offset _ _, he => by
      change offset ≤ 2*H at he
      change -(H : Int) ≤ (offset : Int)-(H : Int) ∧
        (offset : Int)-(H : Int) ≤ (H : Int)
      constructor <;> omega
  | .add e f, he => ⟨ofWindow_within H e he.1, ofWindow_within H f he.2⟩
  | .mul e f, he => ⟨ofWindow_within H e he.1, ofWindow_within H f he.2⟩
  | .smul _ e, he => ofWindow_within H e he

theorem window_ofWindow {base : Nat} (r H : Nat) (e : WindowExpression base)
    (hr : r ≤ H) : window H (ofWindow r e) = shift (H-r) e := by
  induction e with
  | one => rfl
  | loop offset value spin =>
      change WindowExpression.loop (((H : Int)+((offset : Int)-(r : Int))).toNat) value spin =
        .loop (offset+(H-r)) value spin
      congr 1
      omega
  | add e f he hf =>
      change WindowExpression.add (window H (ofWindow r e)) (window H (ofWindow r f)) =
        .add (shift (H-r) e) (shift (H-r) f)
      rw [he, hf]
  | mul e f he hf =>
      change WindowExpression.mul (window H (ofWindow r e)) (window H (ofWindow r f)) =
        .mul (shift (H-r) e) (shift (H-r) f)
      rw [he, hf]
  | smul c e he =>
      change WindowExpression.smul c (window H (ofWindow r e)) =
        .smul c (shift (H-r) e)
      rw [he]

end YMGap.Continuum.BF4WilsonSignedTimeExpression

#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.Expression
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.Within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.radius
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.within_mono
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.within_radius
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.radius_le_of_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.window
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.window_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.window_enlarge
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.reflect
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.reflect_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.forward_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.backward_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.window_reflect
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.window_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.window_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.reflect_reflect
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.backward_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.forward_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.reflect_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.reflect_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.ofWindow
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.ofWindow_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.ofWindow_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpression.window_ofWindow
