/-
# Original discrete-time geometry on intrinsic Wilson expressions

Time advance increases the witnessed distance from the reflection plane;
it keeps the original source expression, loop order, spins and coefficients.
Common-chart identities prove the exact semigroup and signed linear laws.
The advanced unit need not be the same radius-tagged expression, but every
one of its charts is the literal unit polynomial.

The mixed reflected product for advances m and n is exactly a common offset
shift of the product with total advance m+n in its second argument. Explicit
support bounds keep both products in the original doubled window and avoid
truncated-subtraction aliasing. Equality of their limiting forms still needs
the separate original-action stationarity theorem. No form equality, norm
contraction, completed time operator, strict bound or continuum claim is made
in this purely finite geometric module.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra

/-- Preserve the literal source word and increase distance from the plane. -/
def advance {base : Nat} (n : Nat) (x : IntrinsicExpression base) : IntrinsicExpression base where
  radius := x.radius+n
  expression := x.expression
  within := within_mono (Nat.le_add_right _ _) x.expression x.within

private theorem intrinsic_ext {base : Nat} (x y : IntrinsicExpression base)
    (hr : x.radius=y.radius) (he : x.expression=y.expression) : x=y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem advance_zero {base : Nat} (x : IntrinsicExpression base) : advance 0 x = x := by
  apply intrinsic_ext
  · exact Nat.add_zero x.radius
  · rfl

theorem advance_add {base : Nat} (m n : Nat) (x : IntrinsicExpression base) :
    advance m (advance n x) = advance (m+n) x := by
  apply intrinsic_ext
  · change x.radius+n+m = x.radius+(m+n)
    omega
  · rfl

/-- Algebraic chart formula; semantic uses retain their displayed room guards. -/
theorem chart_advance {base : Nat} (H n : Nat) (x : IntrinsicExpression base) :
    chart H (advance n x) = chart (H-n) x := by
  change shift (H-(x.radius+n)) x.expression = shift ((H-n)-x.radius) x.expression
  rw [show H-(x.radius+n) = (H-n)-x.radius by omega]

/-- Moving the common chart with the time advance preserves every source offset. -/
theorem chart_advance_add_center {base : Nat} (H n : Nat) (x : IntrinsicExpression base) :
    chart (H+n) (advance n x) = chart H x := by
  change shift ((H+n)-(x.radius+n)) x.expression = shift (H-x.radius) x.expression
  rw [show (H+n)-(x.radius+n) = H-x.radius by omega]

theorem advance_sum {base : Nat} (n : Nat) (x y : IntrinsicExpression base) :
    advance n (sum x y) = sum (advance n x) (advance n y) := by
  apply intrinsic_ext
  · change max x.radius y.radius+n = max (x.radius+n) (y.radius+n)
    omega
  · change WindowExpression.add (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y) =
      WindowExpression.add (chart (max (x.radius+n) (y.radius+n)) (advance n x))
        (chart (max (x.radius+n) (y.radius+n)) (advance n y))
    rw [show max (x.radius+n) (y.radius+n) = max x.radius y.radius+n by omega,
      chart_advance_add_center, chart_advance_add_center]

theorem advance_difference {base : Nat} (n : Nat) (x y : IntrinsicExpression base) :
    advance n (difference x y) = difference (advance n x) (advance n y) := by
  apply intrinsic_ext
  · change max x.radius y.radius+n = max (x.radius+n) (y.radius+n)
    omega
  · change WindowExpression.add (chart (max x.radius y.radius) x)
      (.smul (-1) (chart (max x.radius y.radius) y)) =
      WindowExpression.add (chart (max (x.radius+n) (y.radius+n)) (advance n x))
        (.smul (-1) (chart (max (x.radius+n) (y.radius+n)) (advance n y)))
    rw [show max (x.radius+n) (y.radius+n) = max x.radius y.radius+n by omega,
      chart_advance_add_center, chart_advance_add_center]

theorem advance_smul {base : Nat} (n : Nat) (c : Q') (x : IntrinsicExpression base) :
    advance n (smul c x) = smul c (advance n x) := rfl

/-- Radius tags may differ, but the original unit observable does not. -/
theorem chart_advance_unit (base H n : Nat) : chart H (advance n (unit base)) = .one := rfl

theorem chart_advance_zero (base H n : Nat) :
    chart H (advance n (zero base)) = .smul 0 .one := rfl

private theorem mapOffsets_comp {base : Nat} (f g : Nat → Nat) (e : WindowExpression base) :
    mapOffsets f (mapOffsets g e) = mapOffsets (fun offset => f (g offset)) e := by
  induction e <;> simp_all only [mapOffsets]

private theorem mapOffsets_congr_within {base L : Nat} (f g : Nat → Nat)
    (hfg : ∀ offset, offset ≤ L → f offset = g offset) :
    ∀ e : WindowExpression base, Within L e → mapOffsets f e = mapOffsets g e
  | .one, _ => rfl
  | .loop offset value spin, he => congrArg (fun j => WindowExpression.loop j value spin) (hfg offset he)
  | .add e f', he => by
      change WindowExpression.add (mapOffsets f e) (mapOffsets f f') =
        WindowExpression.add (mapOffsets g e) (mapOffsets g f')
      rw [mapOffsets_congr_within f g hfg e he.1, mapOffsets_congr_within f g hfg f' he.2]
  | .mul e f', he => by
      change WindowExpression.mul (mapOffsets f e) (mapOffsets f f') =
        WindowExpression.mul (mapOffsets g e) (mapOffsets g f')
      rw [mapOffsets_congr_within f g hfg e he.1, mapOffsets_congr_within f g hfg f' he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mapOffsets f e) = WindowExpression.smul c (mapOffsets g e)
      rw [mapOffsets_congr_within f g hfg e he]

/-- Advancing the reflected operand moves its actual upper offsets forward. -/
theorem mirror_chart_advance {base : Nat} (H n : Nat) (x : IntrinsicExpression base)
    (hx : x.radius+n ≤ H) :
    mirror H (chart H (advance n x)) = shift n (mirror H (chart H x)) := by
  change mapOffsets (fun offset => 2*H-offset)
      (mapOffsets (fun offset => offset+(H-(x.radius+n))) x.expression) =
    mapOffsets (fun offset => offset+n) (mapOffsets (fun offset => 2*H-offset)
      (mapOffsets (fun offset => offset+(H-x.radius)) x.expression))
  simp only [mapOffsets_comp]
  exact mapOffsets_congr_within (L := x.radius) _ _ (fun offset ho => by omega) x.expression x.within

/-- Literal lower chart offsets give an upper bound sharper than 2H. -/
theorem mirror_chart_within {base : Nat} (H : Nat) (x : IntrinsicExpression base) :
    Within (H+x.radius) (mirror H (chart H x)) := by
  change Within (H+x.radius) (mapOffsets (fun offset => 2*H-offset)
    (mapOffsets (fun offset => offset+(H-x.radius)) x.expression))
  rw [mapOffsets_comp]
  exact within_mapOffsets (L := x.radius) _ (fun offset ho => by omega) x.expression x.within

/-- Transfer m units between the original source offset and the common shift. -/
theorem chart_advance_transfer {base : Nat} (H m n : Nat) (y : IntrinsicExpression base)
    (hy : y.radius+(m+n) ≤ H) :
    chart H (advance n y) = shift m (chart H (advance (m+n) y)) := by
  change shift (H-(y.radius+n)) y.expression =
    shift m (shift (H-(y.radius+(m+n))) y.expression)
  rw [shift_comp, show H-(y.radius+(m+n))+m = H-(y.radius+n) by omega]

/-- Exact signed mixed-product identity; stationarity is a SEPARATE consumer. -/
theorem mixed_advance {base : Nat} (H m n : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius+m ≤ H) (hy : y.radius+(m+n) ≤ H) :
    WindowExpression.mul (mirror H (chart H (advance m x))) (chart H (advance n y)) =
      shift m (.mul (mirror H (chart H x)) (chart H (advance (m+n) y))) := by
  change WindowExpression.mul (mirror H (chart H (advance m x))) (chart H (advance n y)) =
    WindowExpression.mul (shift m (mirror H (chart H x))) (shift m (chart H (advance (m+n) y)))
  rw [mirror_chart_advance H m x hx, chart_advance_transfer H m n y hy]

/-- The unshifted product fits BEFORE the global m-step shift; for m=1 this
is exactly the Within (2*H-1) guard of original same-window stationarity. -/
theorem mixed_advance_source_within {base : Nat} (H m n : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius+m ≤ H) (hy : y.radius+(m+n) ≤ H) :
    Within (2*H-m) (.mul (mirror H (chart H x)) (chart H (advance (m+n) y))) := by
  constructor
  · exact within_mono (by omega : H+x.radius ≤ 2*H-m) _ (mirror_chart_within H x)
  · exact within_mono (by omega : H ≤ 2*H-m) _ (chart_within H (advance (m+n) y) hy)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.chart_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.chart_advance_add_center
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.chart_advance_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.chart_advance_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.mirror_chart_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.mirror_chart_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.chart_advance_transfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.mixed_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime.mixed_advance_source_within
