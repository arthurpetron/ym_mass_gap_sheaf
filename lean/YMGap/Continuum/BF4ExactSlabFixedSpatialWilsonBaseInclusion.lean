/-
# Literal spatial-base inclusion of original Wilson expressions

Zero spatial translation retains every original oriented link, loop order,
time offset, spin and signed coefficient. Only the witnessed source-box room
increases. Recentring at zero therefore gives coherent inclusions of signed
windows and their radius-tagged intrinsic expressions. The literal polynomial
in a common ambient slab is unchanged, and time advance and dense algebra
commute exactly with this inclusion.

Width-dependent source coordinate polynomials are NOT identified. Nor does
this finite syntax module identify the original interacting actions or their
limits at different bases. Compatibility of the actual limiting pairings is
a separate analytic consumer, required before any spatial union completion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftVertex shiftLink)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (OrientedBF4Link)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (character)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop shiftEntry)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl (windowCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison (windowCap_recenter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap (intrinsicCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyAdd polyMul polySmul)

private theorem translateEntry_zero (e : OrientedBF4Link) : translateEntry 0 e = e := by
  rcases e with ⟨⟨⟨a,b,c,t⟩,dir⟩,rev⟩
  rfl

private theorem map_translateEntry_zero (edges : List OrientedBF4Link) :
    edges.map (translateEntry 0) = edges := by
  induction edges with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, translateEntry_zero, ih]

/-- The original ordered oriented word is literally retained across bases. -/
theorem includeLoop_edges {base larger : Nat} (h : base ≤ larger) (loop : SourceLoop base) :
    (recenterLoop (space := 0) (by simpa only [Nat.add_zero] using h) loop).edges = loop.edges :=
  map_translateEntry_zero loop.edges

theorem includeLoop_start {base larger : Nat} (h : base ≤ larger) (loop : SourceLoop base) :
    (recenterLoop (space := 0) (by simpa only [Nat.add_zero] using h) loop).start = loop.start := by
  change shiftVertex 0 0 loop.start = loop.start
  rcases loop.start with ⟨a,b,c,t⟩
  rfl

private theorem loop_ext {base : Nat} (x y : SourceLoop base)
    (hs : x.start = y.start) (he : x.edges = y.edges) : x=y := by
  cases x
  cases y
  cases hs
  cases he
  rfl

private theorem includeLoop_refl {base : Nat} (loop : SourceLoop base) :
    recenterLoop (space := 0) (by omega : base+0 ≤ base) loop = loop :=
  loop_ext _ _ (includeLoop_start (Nat.le_refl base) loop) (includeLoop_edges (Nat.le_refl base) loop)

/-- Only the source-box witness changes; spatial translation is exactly zero. -/
def includeExpression {base larger : Nat} (h : base ≤ larger) :
    WindowExpression base → WindowExpression larger :=
  recenterExpression (space := 0) (by simpa only [Nat.add_zero] using h)

theorem includeExpression_refl {base : Nat} (e : WindowExpression base) :
    includeExpression (Nat.le_refl base) e = e := by
  induction e <;> simp_all only [includeExpression, recenterExpression, includeLoop_refl]

theorem includeExpression_trans {base middle larger : Nat}
    (hfirst : base ≤ middle) (hsecond : middle ≤ larger) (e : WindowExpression base) :
    includeExpression hsecond (includeExpression hfirst e) =
      includeExpression (Nat.le_trans hfirst hsecond) e := by
  simpa only [includeExpression, Nat.add_zero] using
    recenterExpression_comp (width := base) (middle := middle) (targetWidth := larger)
      (first := 0) (second := 0)
      (by simpa only [Nat.add_zero] using hfirst)
      (by simpa only [Nat.add_zero] using hsecond) e

theorem includeExpression_within {base larger : Nat} (h : base ≤ larger)
    (L : Nat) (e : WindowExpression base) :
    Within L (includeExpression h e) ↔ Within L e := recenter_within _ L e

theorem includeExpression_cap {base larger : Nat} (h : base ≤ larger)
    (e : WindowExpression base) : windowCap (includeExpression h e) = windowCap e :=
  windowCap_recenter _ e

theorem includeExpression_mapOffsets {base larger : Nat} (h : base ≤ larger)
    (f : Nat → Nat) (e : WindowExpression base) :
    includeExpression h (mapOffsets f e) = mapOffsets f (includeExpression h e) :=
  recenter_mapOffsets _ f e

theorem includeExpression_mirror {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (e : WindowExpression base) :
    includeExpression h (mirror H e) = mirror H (includeExpression h e) :=
  includeExpression_mapOffsets h (fun offset => 2*H-offset) e

theorem includeExpression_one {base larger : Nat} (h : base ≤ larger) :
    includeExpression h .one = .one := rfl

theorem includeExpression_add {base larger : Nat} (h : base ≤ larger)
    (e f : WindowExpression base) :
    includeExpression h (.add e f) = .add (includeExpression h e) (includeExpression h f) := rfl

theorem includeExpression_mul {base larger : Nat} (h : base ≤ larger)
    (e f : WindowExpression base) :
    includeExpression h (.mul e f) = .mul (includeExpression h e) (includeExpression h f) := rfl

theorem includeExpression_smul {base larger : Nat} (h : base ≤ larger)
    (c : Q') (e : WindowExpression base) :
    includeExpression h (.smul c e) = .smul c (includeExpression h e) := rfl

/-- SAME ambient polynomial; this does not identify source coordinate carriers
or the different original action families used by their limits. -/
theorem includeExpression_placed {base larger : Nat} (h : base ≤ larger) (extent start : Nat) :
    ∀ e : WindowExpression base,
    placedPolynomial extent start (includeExpression h e) = placedPolynomial extent start e
  | .one => rfl
  | .loop offset value spin => by
      change character extent
        ((recenterLoop (space := 0) (by simpa only [Nat.add_zero] using h) value).edges.map
          (shiftEntry (start+offset))) spin = _
      rw [includeLoop_edges h value]
      rfl
  | .add e f => by
      change polyAdd (placedPolynomial extent start (includeExpression h e))
        (placedPolynomial extent start (includeExpression h f)) =
        polyAdd (placedPolynomial extent start e) (placedPolynomial extent start f)
      rw [includeExpression_placed h extent start e, includeExpression_placed h extent start f]
  | .mul e f => by
      change polyMul (placedPolynomial extent start (includeExpression h e))
        (placedPolynomial extent start (includeExpression h f)) =
        polyMul (placedPolynomial extent start e) (placedPolynomial extent start f)
      rw [includeExpression_placed h extent start e, includeExpression_placed h extent start f]
  | .smul c e => by
      change polySmul c (placedPolynomial extent start (includeExpression h e)) =
        polySmul c (placedPolynomial extent start e)
      rw [includeExpression_placed h extent start e]

/-- The intrinsic time radius remains the same witnessed natural number. -/
def inclusion {base larger : Nat} (h : base ≤ larger) (x : IntrinsicExpression base) :
    IntrinsicExpression larger where
  radius := x.radius
  expression := includeExpression h x.expression
  within := (includeExpression_within h x.radius x.expression).mpr x.within

private theorem intrinsic_ext {base : Nat} (x y : IntrinsicExpression base)
    (hr : x.radius = y.radius) (he : x.expression = y.expression) : x=y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem inclusion_refl {base : Nat} (x : IntrinsicExpression base) :
    inclusion (Nat.le_refl base) x = x :=
  intrinsic_ext _ _ rfl (includeExpression_refl x.expression)

theorem inclusion_trans {base middle larger : Nat} (hfirst : base ≤ middle)
    (hsecond : middle ≤ larger) (x : IntrinsicExpression base) :
    inclusion hsecond (inclusion hfirst x) = inclusion (Nat.le_trans hfirst hsecond) x :=
  intrinsic_ext _ _ rfl (includeExpression_trans hfirst hsecond x.expression)

theorem inclusion_radius {base larger : Nat} (h : base ≤ larger) (x : IntrinsicExpression base) :
    (inclusion h x).radius = x.radius := rfl

theorem inclusion_cap {base larger : Nat} (h : base ≤ larger) (x : IntrinsicExpression base) :
    intrinsicCap (inclusion h x) = intrinsicCap x := includeExpression_cap h x.expression

theorem inclusion_chart {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (x : IntrinsicExpression base) :
    chart H (inclusion h x) = includeExpression h (chart H x) :=
  (includeExpression_mapOffsets h (fun offset => offset+(H-x.radius)) x.expression).symm

theorem inclusion_unit {base larger : Nat} (h : base ≤ larger) :
    inclusion h (unit base) = unit larger := rfl

theorem inclusion_zero {base larger : Nat} (h : base ≤ larger) :
    inclusion h (zero base) = zero larger := rfl

theorem inclusion_sum {base larger : Nat} (h : base ≤ larger) (x y : IntrinsicExpression base) :
    inclusion h (sum x y) = sum (inclusion h x) (inclusion h y) := by
  apply intrinsic_ext
  · rfl
  · change WindowExpression.add (includeExpression h (chart (max x.radius y.radius) x))
        (includeExpression h (chart (max x.radius y.radius) y)) =
      WindowExpression.add (chart (max x.radius y.radius) (inclusion h x))
        (chart (max x.radius y.radius) (inclusion h y))
    rw [inclusion_chart, inclusion_chart]

theorem inclusion_difference {base larger : Nat} (h : base ≤ larger)
    (x y : IntrinsicExpression base) :
    inclusion h (difference x y) = difference (inclusion h x) (inclusion h y) := by
  apply intrinsic_ext
  · rfl
  · change WindowExpression.add (includeExpression h (chart (max x.radius y.radius) x))
        (.smul (-1) (includeExpression h (chart (max x.radius y.radius) y))) =
      WindowExpression.add (chart (max x.radius y.radius) (inclusion h x))
        (.smul (-1) (chart (max x.radius y.radius) (inclusion h y)))
    rw [inclusion_chart, inclusion_chart]

theorem inclusion_smul {base larger : Nat} (h : base ≤ larger)
    (c : Q') (x : IntrinsicExpression base) :
    inclusion h (smul c x) = smul c (inclusion h x) := rfl

/-- Physical time changes the same radius on both sides and no spatial link. -/
theorem inclusion_advance {base larger : Nat} (h : base ≤ larger)
    (n : Nat) (x : IntrinsicExpression base) :
    inclusion h (advance n x) = advance n (inclusion h x) := rfl

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeLoop_edges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeLoop_start
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_trans
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_mapOffsets
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_mirror
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_mul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.includeExpression_placed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_trans
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_radius
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_chart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_advance
