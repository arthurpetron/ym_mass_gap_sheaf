/-
# Squared seminorm on arbitrary finite-horizon Wilson expressions

Sums and differences first place both original expressions at their maximum
recorded radius. Exact centered-chart identities retain every loop, offset,
spin and signed term. Distance is the existing intrinsic limiting reflected
form of that literal difference, with Cauchy data for its actual representative.

Every squared-seminorm law is transported from the proved fixed-window
instance at an explicit common horizon: two radii for symmetry, three for
triangle, four for null replacement. No new positivity, continuity or gap
hypothesis is introduced. This constructs the actual seminorm, not its
completion, a full observable-coverage identification or a continuum theory.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowSeminorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Both operands are centered at their computed common radius before adding. -/
def sum {base : Nat} (x y : IntrinsicExpression base) : IntrinsicExpression base where
  radius := max x.radius y.radius
  expression := .add (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
  within := ⟨chart_within _ x (Nat.le_max_left _ _), chart_within _ y (Nat.le_max_right _ _)⟩

/-- The actual signed difference at one common reflection center. -/
def difference {base : Nat} (x y : IntrinsicExpression base) : IntrinsicExpression base where
  radius := max x.radius y.radius
  expression := .add (chart (max x.radius y.radius) x) (.smul (-1) (chart (max x.radius y.radius) y))
  within := ⟨chart_within _ x (Nat.le_max_left _ _), chart_within _ y (Nat.le_max_right _ _)⟩

theorem chart_sum {base : Nat} (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    chart H (sum x y) = .add (chart H x) (chart H y) := by
  let M := max x.radius y.radius
  have hM : M ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hsum : M+(H-M)=H := by omega
  change WindowExpression.add (shift (H-M) (chart M x)) (shift (H-M) (chart M y)) = _
  rw [← chart_step M (H-M) x (Nat.le_max_left _ _),
    ← chart_step M (H-M) y (Nat.le_max_right _ _), hsum]

theorem chart_difference {base : Nat} (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    chart H (difference x y) = .add (chart H x) (.smul (-1) (chart H y)) := by
  let M := max x.radius y.radius
  have hM : M ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hsum : M+(H-M)=H := by omega
  change WindowExpression.add (shift (H-M) (chart M x))
    (.smul (-1) (shift (H-M) (chart M y))) = _
  rw [← chart_step M (H-M) x (Nat.le_max_left _ _),
    ← chart_step M (H-M) y (Nat.le_max_right _ _), hsum]

/-- Actual inclusion into the existing guarded fixed-window carrier. -/
def toWindow {base : Nat} (H : Nat) (x : IntrinsicExpression base) (hx : x.radius ≤ H) :
    BF4ExactSlabFixedSpatialWilsonWindowSeminorm.Carrier base H :=
  ⟨chart H x, chart_within H x hx⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

/-- No new scalar: this is the intrinsic form on the literal difference. -/
def distSq (x y : IntrinsicExpression base) : CReal :=
  intrinsicForm hw0 hw1 hsmall hd hs hb (difference x y) (difference x y)

def distSqCauchy (x y : IntrinsicExpression base) :
    QCauchy (distSq hw0 hw1 hsmall hd hs hb x y).approx :=
  intrinsicFormCauchy hw0 hw1 hsmall hd hs hb (difference x y) (difference x y)

local notation "D" => distSq hw0 hw1 hsmall hd hs hb
local notation "Wdist" => BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq hw0 hw1 hsmall hd hs hb

/-- A valid common window realizes exactly the existing intrinsic distance. -/
theorem distSq_chart (x y : IntrinsicExpression base) (H : Nat)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    Equiv (D x y) (Wdist H (toWindow H x hx) (toWindow H y hy)) := by
  have hxy : (difference x y).radius ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have h := intrinsicForm_chart hw0 hw1 hsmall hd hs hb (difference x y) (difference x y)
    H hxy hxy
  simpa only [chart_difference H x y hx hy] using h

attribute [local irreducible] distSq BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq

theorem distSq_refl (x : IntrinsicExpression base) : Equiv (D x x) czero :=
  (distSq_chart hw0 hw1 hsmall hd hs hb x x x.radius (Nat.le_refl _) (Nat.le_refl _)).trans
    (BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_refl hw0 hw1 hsmall hd hs hb x.radius
      (toWindow x.radius x (Nat.le_refl _)))

theorem distSq_symm (x y : IntrinsicExpression base) : Equiv (D x y) (D y x) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  exact (distSq_chart hw0 hw1 hsmall hd hs hb x y H hx hy).trans
    ((BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_symm hw0 hw1 hsmall hd hs hb H
      (toWindow H x hx) (toWindow H y hy)).trans
      (distSq_chart hw0 hw1 hsmall hd hs hb y x H hy hx).symm)

theorem distSq_nonnegative (x y : IntrinsicExpression base) : leEv czero (D x y) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  exact leEv_trans
    (BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_nonnegative hw0 hw1 hsmall hd hs hb H
      (toWindow H x hx) (toWindow H y hy))
    (leEv_of_equiv (distSq_chart hw0 hw1 hsmall hd hs hb x y H hx hy).symm)

/-- Three independent horizons are compared in one explicitly computed chart. -/
theorem distSq_triangle (x y z : IntrinsicExpression base) :
    leEv (D x z) (add (add (D x y) (D x y)) (add (D y z) (D y z))) := by
  let H := max (max x.radius y.radius) z.radius
  have hx : x.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hy : y.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hz : z.radius ≤ H := Nat.le_max_right _ _
  have hxy := distSq_chart hw0 hw1 hsmall hd hs hb x y H hx hy
  have hyz := distSq_chart hw0 hw1 hsmall hd hs hb y z H hy hz
  exact leEv_trans (leEv_of_equiv (distSq_chart hw0 hw1 hsmall hd hs hb x z H hx hz))
    (leEv_trans
      (BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_triangle hw0 hw1 hsmall hd hs hb H
        (toWindow H x hx) (toWindow H y hy) (toWindow H z hz))
      (leEv_of_equiv (Equiv_add (Equiv_add hxy.symm hxy.symm) (Equiv_add hyz.symm hyz.symm))))

/-- Nullity is transferred only between the same limiting distances. It is
never inferred for a finite-cutoff representative. -/
theorem distSq_null_congr {x x' y y' : IntrinsicExpression base}
    (hx : Equiv (D x x') czero) (hy : Equiv (D y y') czero) :
    Equiv (D x y) (D x' y') := by
  let H := max (max x.radius x'.radius) (max y.radius y'.radius)
  have hxr : x.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hxr' : x'.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hyr : y.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hyr' : y'.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hxW : Equiv (Wdist H (toWindow H x hxr) (toWindow H x' hxr')) czero :=
    (distSq_chart hw0 hw1 hsmall hd hs hb x x' H hxr hxr').symm.trans hx
  have hyW : Equiv (Wdist H (toWindow H y hyr) (toWindow H y' hyr')) czero :=
    (distSq_chart hw0 hw1 hsmall hd hs hb y y' H hyr hyr').symm.trans hy
  exact (distSq_chart hw0 hw1 hsmall hd hs hb x y H hxr hyr).trans
    ((BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq_null_congr
      hw0 hw1 hsmall hd hs hb H hxW hyW).trans
      (distSq_chart hw0 hw1 hsmall hd hs hb x' y' H hxr' hyr').symm)

/-- Every field is transported from the actual fixed-window Wilson instance. -/
def seminorm : SquaredSeminorm where
  Carrier := IntrinsicExpression base
  distSq := D
  distSq_refl := distSq_refl hw0 hw1 hsmall hd hs hb
  distSq_symm := distSq_symm hw0 hw1 hsmall hd hs hb
  distSq_nonneg := distSq_nonnegative hw0 hw1 hsmall hd hs hb
  distSq_triangle := distSq_triangle hw0 hw1 hsmall hd hs hb
  null_congr := distSq_null_congr hw0 hw1 hsmall hd hs hb

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.chart_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.chart_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.toWindow
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSqCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_chart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_triangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.seminorm
