/-
# Two fixed-support original probes in a reflected chart

At chart H=R+n, the reflected left probe starts at A+H and the advanced
right probe is encoded in the fixed R chart at A. Their literal polynomials
have separately computed interval and link-locality certificates. Each
support box depends on base and R, never on physical lag n, spatial margin,
heat cutoff or external time buffer. No growing box enclosing the gap is
used. The original action is unchanged.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedProbeControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor sweptProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (Span Within Physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe (encodeChart_translate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe (mirrorSpan_encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (placeProbes)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftLink)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.Z4FiniteBoxExhaustion (boxLinks)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks centralExtent)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

theorem placeWindowProbes_advance (start n : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    placeWindowProbes start (advanceSchedule n fs) = placeWindowProbes (start+n) fs
  | [] => rfl
  | e::es => by
      change placeProbes (start+(e.1+n)) e.2 ++ placeWindowProbes start (advanceSchedule n es) =
        placeProbes (start+n+e.1) e.2 ++ placeWindowProbes (start+n) es
      rw [show start+(e.1+n) = start+n+e.1 by omega, placeWindowProbes_advance start n es]

/-- Literal polynomial equality, including empty schedules and spans. -/
theorem placedSpan_advance (extent start n : Nat) : (xs : Span) →
    placedSpan extent start (advanceSpan n xs) = placedSpan extent (start+n) xs
  | [] => rfl
  | x::xs => by
      change polyAdd (polySmul x.1 (sweptProduct extent 0 (placeWindowProbes start (advanceSchedule n x.2))))
        (placedSpan extent start (advanceSpan n xs)) =
        polyAdd (polySmul x.1 (sweptProduct extent 0 (placeWindowProbes (start+n) x.2)))
          (placedSpan extent (start+n) xs)
      rw [placeWindowProbes_advance, placedSpan_advance]

def probeBoxSize (base R : Nat) : Nat := max base (R+1)

theorem probeBoxSize_pos (base R : Nat) : 0 < probeBoxSize base R := by
  unfold probeBoxSize
  omega

def upperProbe (base r R n t : Nat) (x : PhysicalSpan base) : RatPoly :=
  placedSpan (chartExtent base r (R+n) t) (paddedWidth base r+1+t+(R+n)) (recenter r x).val

def lowerProbe (base r R n t : Nat) (y : PhysicalSpan base) : RatPoly :=
  placedSpan (chartExtent base r (R+n) t) (paddedWidth base r+1+t) (encodeChart R (recenter r y).val)

theorem chartProbe_separated (base r R n t : Nat) (x y : PhysicalSpan base)
    (hx : radius x.val ≤ R) :
    chartProbe base r (R+n) t x (physicalTime n y) =
      polyMul (upperProbe base r R n t x) (lowerProbe base r R n t y) := by
  have hxr : radius (recenter r x).val ≤ R+n := by
    rw [recenter_radius]
    omega
  dsimp only [chartProbe]
  rw [mirrorSpan_encodeChart _ _ hxr, placedSpan_advance, recenter_time]
  change polyMul _ (placedSpan _ _ (encodeChart (R+n) (advanceSpan n (recenter r y).val))) = _
  rw [encodeChart_advance]
  rfl

private theorem recenter_within {base R : Nat} (r : Nat) (x : PhysicalSpan base)
    (hx : radius x.val ≤ R) : Within R (recenter r x).val := by
  intro a ha e he
  have h := radius_within (recenter r x).val a ha e he
  rw [recenter_radius] at h
  exact Nat.le_trans h hx

def upperProbe_interval (base r R n t : Nat) (x : PhysicalSpan base)
    (hx : radius x.val ≤ R) :
    Interval (boundaryCompleteSlabLinks (chartExtent base r (R+n) t)).length
      (upperProbe base r R n t x) (spanCap x.val) := by
  have hw : paddedWidth base r ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+(R+n)+R ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have P := placedSpan_interval (chartExtent base r (R+n) t) (paddedWidth base r+1+t+(R+n))
    (recenter r x).val (fun a ha => placeWindowProbes_physical hw ht a.2
      (recenter_within r x hx a ha) ((recenter r x).property a ha))
  simpa only [upperProbe, recenter, spanCap_translate] using P

def lowerProbe_interval (base r R n t : Nat) (y : PhysicalSpan base)
    (hy : radius y.val ≤ R) :
    Interval (boundaryCompleteSlabLinks (chartExtent base r (R+n) t)).length
      (lowerProbe base r R n t y) (spanCap y.val) := by
  have hw : paddedWidth base r ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+R ≤ chartExtent base r (R+n) t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hyr : radius (recenter r y).val ≤ R := by rw [recenter_radius]; exact hy
  have P := placedSpan_interval (chartExtent base r (R+n) t) (paddedWidth base r+1+t)
    (encodeChart R (recenter r y).val) (fun a ha => placeWindowProbes_physical hw ht a.2
      (encodeChart_within R _ hyr a ha) (encodeChart_physical R _ (recenter r y).property a ha))
  simpa only [lowerProbe, spanCap_encode, recenter, spanCap_translate] using P

theorem upperProbe_local (base r R n t : Nat) (x : PhysicalSpan base)
    (hx : radius x.val ≤ R) :
    LinkLocal (chartExtent base r (R+n) t)
      ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t+(R+n))))
      (upperProbe base r R n t x) :=
  placedSpan_translated_local base R (r+1) _ _ x.val x.property
    (fun a ha e he => Nat.le_trans (radius_within x.val a ha e he) hx)

theorem lowerProbe_local (base r R n t : Nat) (y : PhysicalSpan base)
    (hy : radius y.val ≤ R) :
    LinkLocal (chartExtent base r (R+n) t)
      ((boxLinks (probeBoxSize base R)).map (shiftLink (r+1) (paddedWidth base r+1+t)))
      (lowerProbe base r R n t y) := by
  have P := placedSpan_translated_local base R (r+1) (chartExtent base r (R+n) t)
    (paddedWidth base r+1+t) (encodeChart R y.val)
    (encodeChart_physical R _ y.property) (encodeChart_within R _ hy)
  simpa only [lowerProbe, probeBoxSize, recenter, encodeChart_translate] using P

#print axioms placeWindowProbes_advance
#print axioms placedSpan_advance
#print axioms probeBoxSize
#print axioms probeBoxSize_pos
#print axioms upperProbe
#print axioms lowerProbe
#print axioms chartProbe_separated
#print axioms upperProbe_interval
#print axioms lowerProbe_interval
#print axioms upperProbe_local
#print axioms lowerProbe_local

end YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedProbeControl
