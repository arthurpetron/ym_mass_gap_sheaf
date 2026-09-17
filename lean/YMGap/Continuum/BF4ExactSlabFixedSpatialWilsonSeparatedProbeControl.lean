/-
# Two fixed-support original Wilson probes in a reflected chart

At common horizon H=R+n, the reflected left word expression is its literal
radius-reversed offset schedule placed at A+H. The right expression advanced
by n is its fixed R chart placed at A. Loop words, their orientation and order,
spins, signed coefficients and all algebraic operations remain unchanged.

Each probe has its own interval and fixed-box locality certificate. Box size
depends only on the original spatial base and observation radius R, not on the
physical time gap, spatial margin, cutoff or external time buffer. The inclusive
source-link fringe requires max(base+1,R+1), not the old plaquette-box size.
The SAME original selected action is left untouched. This is finite geometry
for the separate connected-covariance consumer, not yet its decay estimate or
a strict bound on the enlarged Wilson completion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (centeredExpression centered_within chartInsertion windowCap_recenter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality (placed_recenter_local)
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl (windowCap windowCap_mapOffsets placed_interval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftLink)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (RatPoly polyMul polyAdd polySmul)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.Z4FiniteBoxExhaustion (boxLinks)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks centralExtent)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

/-- Reverse only the finite time schedule about its witnessed radius. -/
def reverse {base : Nat} (x : IntrinsicExpression base) : WindowExpression base :=
  mapOffsets (fun offset => x.radius-offset) x.expression

theorem reverse_within {base : Nat} (x : IntrinsicExpression base) :
    Within x.radius (reverse x) :=
  within_mapOffsets (fun offset => x.radius-offset)
    (fun _ _ => Nat.sub_le _ _) x.expression x.within

theorem reverse_cap {base : Nat} (x : IntrinsicExpression base) :
    windowCap (reverse x) = intrinsicCap x :=
  windowCap_mapOffsets (fun offset => x.radius-offset) x.expression

private theorem mirror_shift_reverse {base : Nat} (H radius : Nat) (hr : radius ≤ H) :
    ∀ e : WindowExpression base, Within radius e →
    mirror H (shift (H-radius) e) = shift H (mapOffsets (fun offset => radius-offset) e)
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have ho : offset ≤ radius := he
      change WindowExpression.loop (2*H-(offset+(H-radius))) value spin =
        WindowExpression.loop ((radius-offset)+H) value spin
      rw [show 2*H-(offset+(H-radius)) = (radius-offset)+H by omega]
  | .add e f, he => by
      change WindowExpression.add (mirror H (shift (H-radius) e)) (mirror H (shift (H-radius) f)) =
        WindowExpression.add (shift H (mapOffsets (fun offset => radius-offset) e))
          (shift H (mapOffsets (fun offset => radius-offset) f))
      rw [mirror_shift_reverse H radius hr e he.1, mirror_shift_reverse H radius hr f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (mirror H (shift (H-radius) e)) (mirror H (shift (H-radius) f)) =
        WindowExpression.mul (shift H (mapOffsets (fun offset => radius-offset) e))
          (shift H (mapOffsets (fun offset => radius-offset) f))
      rw [mirror_shift_reverse H radius hr e he.1, mirror_shift_reverse H radius hr f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mirror H (shift (H-radius) e)) =
        WindowExpression.smul c (shift H (mapOffsets (fun offset => radius-offset) e))
      rw [mirror_shift_reverse H radius hr e he]

/-- Literal reflected schedule, with the guard excluding truncated aliases. -/
theorem mirror_chart_reverse {base : Nat} (H : Nat) (x : IntrinsicExpression base)
    (hx : x.radius ≤ H) : mirror H (chart H x) = shift H (reverse x) :=
  mirror_shift_reverse H x.radius hx x.expression x.within

/-- Shift the placement start, not any loop word or polynomial factor order. -/
theorem placedPolynomial_shift {base : Nat} (extent start d : Nat) :
    ∀ e : WindowExpression base,
    placedPolynomial extent start (shift d e) = placedPolynomial extent (start+d) e
  | .one => rfl
  | .loop offset value spin => by
      simp only [shift, mapOffsets, placedPolynomial,
        show start+(offset+d) = start+d+offset by omega]
  | .add e f => by
      change polyAdd (placedPolynomial extent start (shift d e))
        (placedPolynomial extent start (shift d f)) =
        polyAdd (placedPolynomial extent (start+d) e) (placedPolynomial extent (start+d) f)
      rw [placedPolynomial_shift extent start d e, placedPolynomial_shift extent start d f]
  | .mul e f => by
      change polyMul (placedPolynomial extent start (shift d e))
        (placedPolynomial extent start (shift d f)) =
        polyMul (placedPolynomial extent (start+d) e) (placedPolynomial extent (start+d) f)
      rw [placedPolynomial_shift extent start d e, placedPolynomial_shift extent start d f]
  | .smul c e => by
      change polySmul c (placedPolynomial extent start (shift d e)) =
        polySmul c (placedPolynomial extent (start+d) e)
      rw [placedPolynomial_shift extent start d e]

/-- Spatial recentering retains the complete original temporal schedule. -/
theorem centered_shift {base : Nat} (r d : Nat) (e : WindowExpression base) :
    centeredExpression r (shift d e) = shift d (centeredExpression r e) :=
  recenter_mapOffsets _ (fun offset => offset+d) e

def probeBoxSize (base R : Nat) : Nat := max (base+1) (R+1)

theorem probeBoxSize_pos (base R : Nat) : 0 < probeBoxSize base R := by
  unfold probeBoxSize
  omega

def upperProbe (base r R n t : Nat) (x : IntrinsicExpression base) : RatPoly :=
  placedPolynomial (chartExtent base r (R+n) t) (paddedWidth base r+1+t+(R+n))
    (centeredExpression r (reverse x))

def lowerProbe (base r R n t : Nat) (y : IntrinsicExpression base) : RatPoly :=
  placedPolynomial (chartExtent base r (R+n) t) (paddedWidth base r+1+t)
    (centeredExpression r (chart R y))

/-- One common original chart contains exactly the product of the two probes. -/
theorem chartInsertion_separated (base r R n t : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ R) (_hy : y.radius ≤ R) :
    chartInsertion r (R+n) t
      (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y))) =
      polyMul (upperProbe base r R n t x) (lowerProbe base r R n t y) := by
  rw [mirror_chart_reverse (R+n) x (Nat.le_trans hx (Nat.le_add_right R n)),
    chart_advance_add_center]
  change polyMul
      (placedPolynomial _ _ (centeredExpression r (shift (R+n) (reverse x))))
      (placedPolynomial _ _ (centeredExpression r (chart R y))) = _
  rw [centered_shift, placedPolynomial_shift]
  rfl

/-- Actual upper original Wilson polynomial, with its lag-independent cap. -/
def upperProbe_interval (base r R n t : Nat) (x : IntrinsicExpression base)
    (hx : x.radius ≤ R) :
    Interval (boundaryCompleteSlabLinks (chartExtent base r (R+n) t)).length
      (upperProbe base r R n t x) (intrinsicCap x) := by
  have hw : paddedWidth base r ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+(R+n)+R ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hrev : Within R (reverse x) := within_mono hx _ (reverse_within x)
  have P := placed_interval hw ht (centeredExpression r (reverse x))
    ((centered_within r R (reverse x)).mpr hrev)
  simpa only [upperProbe, centeredExpression, windowCap_recenter, reverse_cap] using P

/-- Actual lower original Wilson polynomial in its fixed R window. -/
def lowerProbe_interval (base r R n t : Nat) (y : IntrinsicExpression base)
    (hy : y.radius ≤ R) :
    Interval (boundaryCompleteSlabLinks (chartExtent base r (R+n) t)).length
      (lowerProbe base r R n t y) (intrinsicCap y) := by
  have hw : paddedWidth base r ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+R ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have P := placed_interval hw ht (centeredExpression r (chart R y))
    ((centered_within r R (chart R y)).mpr (chart_within R y hy))
  simpa only [lowerProbe, centeredExpression, windowCap_recenter, chart_cap] using P

/-- Separate fixed upper box; no box enclosing the physical gap appears. -/
theorem upperProbe_local (base r R n t : Nat) (x : IntrinsicExpression base)
    (hx : x.radius ≤ R) :
    LinkLocal (chartExtent base r (R+n) t)
      ((boxLinks (probeBoxSize base R)).map
        (shiftLink (r+1) (paddedWidth base r+1+t+(R+n))))
      (upperProbe base r R n t x) :=
  placed_recenter_local (space := r+1)
    (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth base r) R (reverse x)
    (within_mono hx _ (reverse_within x))

theorem lowerProbe_local (base r R n t : Nat) (y : IntrinsicExpression base)
    (hy : y.radius ≤ R) :
    LinkLocal (chartExtent base r (R+n) t)
      ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t)))
      (lowerProbe base r R n t y) :=
  placed_recenter_local (space := r+1)
    (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth base r) R (chart R y)
    (chart_within R y hy)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.reverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.reverse_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.reverse_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.mirror_chart_reverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.placedPolynomial_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.centered_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.probeBoxSize
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.probeBoxSize_pos
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.upperProbe
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.lowerProbe
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.chartInsertion_separated
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.upperProbe_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.lowerProbe_interval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.upperProbe_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.lowerProbe_local
