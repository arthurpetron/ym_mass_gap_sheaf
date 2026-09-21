/-
# Reversal of an arbitrary fixed-spatial source span

Reverse the chronological quaternion blocks of an arbitrary finite signed
source span.  The result is the same span written in natural distances from
the reflection plane.  Combining this algebraic pin with the existing
one-step chart geometry identifies the common-chart insertion with the odd
kinetic quadratic used by the finite positivity theorem.

No positivity, nome, cutoff, partition, or limiting statement is used here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe
import YMGap.Continuum.SU2QuaternionHeadWindowReversal

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (windowProbe windowProbe_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan sourceSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (mixedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
  (DistanceSpan radius radius_within encodeSchedule encodeChart encodeChart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
  (advanceSpan encodeChart_advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe
  (mixedProduct_reflected_separated)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (sourceProbe sourceProbe_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHeadWindowReversal (lift_padded prefix_lift)
open YMGap.Continuum.SU2QuaternionSliceReversal

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 h)

private theorem reindex_one {blocks : Nat} (s : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolynomialEqv blocks (reindexQuaternionPolynomial s polyOne) polyOne := by
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro i hi
      exact exponentAt_reindexQuaternionExponents s [] hi
  · exact .nil

private theorem reverse_single_slice (blocks R offset : Nat) (hoffset : offset ≤ R)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    PaddedPolynomialCoeffEqv ((R+1)*blocks)
      (reversePolynomial blocks R (liftBoundary (offset*blocks) p))
      (liftBoundary ((R-offset)*blocks) p) := by
  have hplace := reversePolynomial_lift blocks R offset 0 (by omega) p
    (by simpa only [Nat.zero_add, Nat.one_mul] using hp)
  have hzero := reversePolynomial_zero blocks p hp
  have hsupport : SupportedQuaternionBlocks blocks (reversePolynomial blocks 0 p) := by
    simpa only [Nat.zero_add, Nat.one_mul] using reversePolynomial_supported blocks 0 p
  have hlift : PaddedPolynomialCoeffEqv ((R+1)*blocks)
      (liftBoundary ((R-offset)*blocks) (reversePolynomial blocks 0 p))
      (liftBoundary ((R-offset)*blocks) p) :=
    prefix_lift ((R-offset)*blocks) hsupport hp hzero
  exact (PaddedPolynomialCoeffEqv.of_prefix
    (by simpa only [Nat.sub_zero] using hplace)).trans hlift

/-- Reversing a chart-encoded ordered schedule recovers its natural-distance
schedule, without changing any face word or its order. -/
theorem windowProbe_reverse (width R : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    (∀ e, e ∈ fs → e.1 ≤ R) →
    PaddedPolynomialCoeffEqv ((R+1)*(N width))
      (reversePolynomial (N width) R (windowProbe width (encodeSchedule R fs)))
      (windowProbe width fs)
  | [], _ => PaddedPolynomialCoeffEqv.of_prefix (reindex_one (sliceReverse (N width) R))
  | e::es, hwithin => by
      have he : e.1 ≤ R := hwithin e List.mem_cons_self
      change PaddedPolynomialCoeffEqv ((R+1)*(N width))
        (reversePolynomial (N width) R
          (polyMul (liftBoundary ((R-e.1)*(N width)) (sourceProbe width e.2))
            (windowProbe width (encodeSchedule R es))))
        (polyMul (liftBoundary (e.1*(N width)) (sourceProbe width e.2))
          (windowProbe width es))
      unfold reversePolynomial
      rw [reindexQuaternionPolynomial_mul]
      have hh := reverse_single_slice (N width) R (R-e.1) (Nat.sub_le _ _)
        (sourceProbe width e.2) (sourceProbe_supported width e.2)
      have ht : R-(R-e.1)=e.1 := by omega
      simpa only [ht] using hh.mul
        (windowProbe_reverse width R es
          (fun a ha => hwithin a (List.mem_cons_of_mem e ha)))

/-- Exact reversal of an arbitrary signed source span. Coefficients, repeated
schedules, ordered face products, and empty schedules are all retained. -/
theorem sourceSpan_reverse (width R : Nat) (xs : DistanceSpan)
    (hx : radius xs ≤ R) :
    PaddedPolynomialCoeffEqv ((R+1)*(N width))
      (reversePolynomial (N width) R (sourceSpan width (encodeChart R xs)))
      (sourceSpan width xs) := by
  induction xs with
  | nil => exact PaddedPolynomialCoeffEqv.refl _ _
  | cons x xs ih =>
      have hhead : ∀ e, e ∈ x.2 → e.1 ≤ R := fun e he =>
        Nat.le_trans
          (BF4ExactSlabFixedSpatialIntrinsicReflectedForm.scheduleRadius_within x.2 e he)
          (Nat.le_trans (Nat.le_max_left _ _) hx)
      have htail : radius xs ≤ R := Nat.le_trans (Nat.le_max_right _ _) hx
      change PaddedPolynomialCoeffEqv ((R+1)*(N width))
        (reversePolynomial (N width) R
          (polyAdd (polySmul x.1 (windowProbe width (encodeSchedule R x.2)))
            (sourceSpan width (encodeChart R xs))))
        (polyAdd (polySmul x.1 (windowProbe width x.2)) (sourceSpan width xs))
      unfold reversePolynomial
      rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_smul]
      exact ((windowProbe_reverse width R x.2 hhead).smul x.1).add (ih htail)

/-- The literal odd product whose finite window is the one-step kinetic
quadratic. -/
def oddProduct (width h : Nat) (xs : DistanceSpan) : RatPoly :=
  let p := sourceSpan width (encodeChart h xs)
  polyMul p (liftBoundary ((h+1)*(N width)) (reversePolynomial (N width) h p))

theorem oddProduct_supported (width h : Nat) (xs : DistanceSpan) (hx : radius xs ≤ h) :
    SupportedQuaternionBlocks ((2*h+1+1)*(N width)) (oddProduct width h xs) := by
  let p := sourceSpan width (encodeChart h xs)
  have hp : SupportedQuaternionBlocks ((h+1)*(N width)) p :=
    sourceSpan_supported width h (encodeChart h xs) (encodeChart_within h xs hx)
  have hr := reversePolynomial_supported (N width) h p
  have hp' : SupportedQuaternionBlocks ((2*h+1+1)*(N width)) p :=
    support_mono hp (Nat.mul_le_mul_right (N width) (by omega))
  have hrl : SupportedQuaternionBlocks ((2*h+1+1)*(N width))
      (liftBoundary ((h+1)*(N width)) (reversePolynomial (N width) h p)) := by
    have hcount : (2*h+1+1)*(N width) =
        (h+1)*(N width)+(h+1)*(N width) := by
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [hcount]
    exact lift_supported hr ((h+1)*(N width))
  exact supported_polyMul hp' hrl

/-- The common chart for `x` and its one-step physical advance is the same
odd product, with one harmless extra padding slice in the displayed chart. -/
theorem mixedProduct_oneStep (width h : Nat) (xs : DistanceSpan)
    (hx : radius xs ≤ h) :
    PaddedPolynomialCoeffEqv ((2*(h+1)+1)*(N width))
      (mixedProduct width (h+1) (encodeChart (h+1) xs)
        (encodeChart (h+1) (advanceSpan 1 xs)))
      (oddProduct width h xs) := by
  let p := sourceSpan width (encodeChart h xs)
  let q := sourceSpan width xs
  have hp : SupportedQuaternionBlocks ((h+1)*(N width)) p :=
    sourceSpan_supported width h (encodeChart h xs) (encodeChart_within h xs hx)
  have hq : SupportedQuaternionBlocks ((h+1)*(N width)) q :=
    sourceSpan_supported width h xs (fun a ha e he =>
      Nat.le_trans (radius_within xs a ha e he) hx)
  have hr : SupportedQuaternionBlocks ((h+1)*(N width))
      (reversePolynomial (N width) h p) := reversePolynomial_supported _ _ _
  have hreverse : PaddedPolynomialCoeffEqv ((h+1)*(N width))
      (reversePolynomial (N width) h p) q := by
    simpa only [p, q] using sourceSpan_reverse width h xs hx
  have hlift : PaddedPolynomialCoeffEqv ((2*(h+1)+1)*(N width))
      (liftBoundary ((h+1)*(N width)) q)
      (liftBoundary ((h+1)*(N width)) (reversePolynomial (N width) h p)) :=
    lift_padded ((h+1)*(N width)) hq hr hreverse.symm
  have hsep := mixedProduct_reflected_separated ((2*(h+1)+1)*(N width))
    width h 1 xs xs hx
  exact hsep.trans (by
    simpa only [oddProduct, p, q] using
      (PaddedPolynomialCoeffEqv.refl ((2*(h+1)+1)*(N width)) p).mul hlift)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal.windowProbe_reverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal.sourceSpan_reverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal.oddProduct
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal.oddProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal.mixedProduct_oneStep
