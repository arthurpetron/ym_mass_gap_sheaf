/-
# Exact source-algebra syntax inside signed time

Recentering a natural window into integer time cancels a simultaneous shift
of the window and its center. Consequently the supported intrinsic product,
sum, scale, unit, and spatial inclusion map literally to the corresponding
signed-time syntax. These are source identities, not quotient multiplication
on OS-null states or an assertion about the completed carrier.
-/

import YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion
import YMGap.Continuum.BF4WilsonSpatialUnionProduct

namespace YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonSignedTimeExpression (Expression ofWindow)
open YMGap.Continuum.BF4WilsonSignedTimeExpectation (fromIntrinsic)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul)
open YMGap.Continuum.BF4WilsonSpatialUnionProduct (product)

/-- Shifting both the natural offset and the recentering origin leaves its
signed time exactly unchanged. -/
theorem ofWindow_shift {base : Nat} (H d : Nat) :
    ∀ e : WindowExpression base,
      ofWindow (H+d) (shift d e) = ofWindow H e
  | .one => rfl
  | .loop offset value spin => by
      change Expression.loop (((offset+d : Nat) : Int)-((H+d : Nat) : Int)) value spin =
        .loop ((offset : Int)-(H : Int)) value spin
      congr 1
      omega
  | .add e f => by
      change Expression.add (ofWindow (H+d) (shift d e))
          (ofWindow (H+d) (shift d f)) =
        .add (ofWindow H e) (ofWindow H f)
      rw [ofWindow_shift H d e, ofWindow_shift H d f]
  | .mul e f => by
      change Expression.mul (ofWindow (H+d) (shift d e))
          (ofWindow (H+d) (shift d f)) =
        .mul (ofWindow H e) (ofWindow H f)
      rw [ofWindow_shift H d e, ofWindow_shift H d f]
  | .smul c e => by
      change Expression.smul c (ofWindow (H+d) (shift d e)) =
        .smul c (ofWindow H e)
      rw [ofWindow_shift H d e]

/-- Any valid larger intrinsic chart recovers the same literal signed syntax. -/
theorem ofWindow_chart {base : Nat} (H : Nat) (x : IntrinsicExpression base)
    (hx : x.radius ≤ H) : ofWindow H (chart H x) = fromIntrinsic x := by
  have hr : x.radius+(H-x.radius)=H := by omega
  change ofWindow H (shift (H-x.radius) x.expression) =
    ofWindow x.radius x.expression
  simpa only [hr] using ofWindow_shift x.radius (H-x.radius) x.expression

theorem fromIntrinsic_product {base : Nat} (x y : IntrinsicExpression base) :
    fromIntrinsic (product x y) =
      Expression.mul (fromIntrinsic x) (fromIntrinsic y) := by
  let H := max x.radius y.radius
  change Expression.mul (ofWindow H (chart H x)) (ofWindow H (chart H y)) = _
  rw [ofWindow_chart H x (Nat.le_max_left _ _),
    ofWindow_chart H y (Nat.le_max_right _ _)]

theorem fromIntrinsic_sum {base : Nat} (x y : IntrinsicExpression base) :
    fromIntrinsic (sum x y) =
      Expression.add (fromIntrinsic x) (fromIntrinsic y) := by
  let H := max x.radius y.radius
  change Expression.add (ofWindow H (chart H x)) (ofWindow H (chart H y)) = _
  rw [ofWindow_chart H x (Nat.le_max_left _ _),
    ofWindow_chart H y (Nat.le_max_right _ _)]

theorem fromIntrinsic_difference {base : Nat} (x y : IntrinsicExpression base) :
    fromIntrinsic (difference x y) =
      Expression.add (fromIntrinsic x) (Expression.smul (-1) (fromIntrinsic y)) := by
  let H := max x.radius y.radius
  change Expression.add (ofWindow H (chart H x))
      (Expression.smul (-1) (ofWindow H (chart H y))) = _
  rw [ofWindow_chart H x (Nat.le_max_left _ _),
    ofWindow_chart H y (Nat.le_max_right _ _)]

theorem fromIntrinsic_smul {base : Nat} (c : Q') (x : IntrinsicExpression base) :
    fromIntrinsic (smul c x) = Expression.smul c (fromIntrinsic x) := rfl

theorem fromIntrinsic_unit (base : Nat) :
    fromIntrinsic (unit base) = (Expression.one : Expression base) := rfl

/-- Natural-window inclusion and signed inclusion use the same zero spatial
recentering of each generator's ordered loop. -/
theorem ofWindow_include {base larger : Nat} (h : base ≤ larger) (H : Nat) :
    ∀ e : WindowExpression base,
      ofWindow H (BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression h e) =
        BF4WilsonSignedTimeBaseInclusion.inclusion h (ofWindow H e)
  | .one => rfl
  | .loop _ _ _ => rfl
  | .add e f => by
      change Expression.add
          (ofWindow H (BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression h e))
          (ofWindow H (BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression h f)) =
        .add (BF4WilsonSignedTimeBaseInclusion.inclusion h (ofWindow H e))
          (BF4WilsonSignedTimeBaseInclusion.inclusion h (ofWindow H f))
      rw [ofWindow_include h H e, ofWindow_include h H f]
  | .mul e f => by
      change Expression.mul
          (ofWindow H (BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression h e))
          (ofWindow H (BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression h f)) =
        .mul (BF4WilsonSignedTimeBaseInclusion.inclusion h (ofWindow H e))
          (BF4WilsonSignedTimeBaseInclusion.inclusion h (ofWindow H f))
      rw [ofWindow_include h H e, ofWindow_include h H f]
  | .smul c e => by
      change Expression.smul c
          (ofWindow H (BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression h e)) =
        .smul c (BF4WilsonSignedTimeBaseInclusion.inclusion h (ofWindow H e))
      rw [ofWindow_include h H e]

theorem fromIntrinsic_inclusion {base larger : Nat} (h : base ≤ larger)
    (x : IntrinsicExpression base) :
    fromIntrinsic (BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion h x) =
      BF4WilsonSignedTimeBaseInclusion.inclusion h (fromIntrinsic x) :=
  ofWindow_include h x.radius x.expression

end YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra

#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.ofWindow_shift
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.ofWindow_chart
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.fromIntrinsic_product
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.fromIntrinsic_sum
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.fromIntrinsic_difference
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.fromIntrinsic_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.fromIntrinsic_unit
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.ofWindow_include
#print axioms YMGap.Continuum.BF4WilsonSignedTimeIntrinsicAlgebra.fromIntrinsic_inclusion
