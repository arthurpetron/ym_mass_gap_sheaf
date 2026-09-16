/-
# Literal reflected probes as two physically separated source windows

Reflecting the encoding of a distance d in a valid chart H gives offset
H+d. Thus the reflected source is the literal physical advance by H of
the original signed span. Arbitrary advances of a source span are one
common coordinate lift, with padded coefficient equality retaining empty
schedules and their lifted units.

In chart H=R+n, encoding the physically advanced right input cancels its
advance exactly. The mixed reflected product is therefore the R-chart
right source times the original left source lifted by (R+n) slices. This
is the concrete insertion pin for the separation bound, not a comparison
with another observable algebra. Physical-face membership, finite action
normalization and limits remain in the existing consumers. No decay,
reflected-norm spectral bound, or continuum assertion is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (sourceProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (windowProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection (mirrorSchedule)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (mixedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
  (lift_one lift_product lift_add lift_smul)
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem mirrorSchedule_encodeSchedule (H : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    (hf : ∀ e, e ∈ fs → e.1 ≤ H) →
    mirrorSchedule H (encodeSchedule H fs) = advanceSchedule H fs
  | [], _ => rfl
  | e::es, hf => by
      have he := hf e List.mem_cons_self
      have htime : 2*H-(H-e.1) = e.1+H := by omega
      change (2*H-(H-e.1), e.2)::mirrorSchedule H (encodeSchedule H es) =
        (e.1+H, e.2)::advanceSchedule H es
      rw [htime, mirrorSchedule_encodeSchedule H es
        (fun f hmem => hf f (List.mem_cons_of_mem e hmem))]

/-- A valid chart reflection sends each intrinsic distance d to offset H+d,
preserving coefficients, face words, list order and repeated insertions. -/
theorem mirrorSpan_encodeChart (H : Nat) : (xs : DistanceSpan) →
    (hx : radius xs ≤ H) →
    mirrorSpan H (encodeChart H xs) = advanceSpan H xs
  | [], _ => rfl
  | x::xs, hx => by
      have hhead : ∀ e, e ∈ x.2 → e.1 ≤ H := fun e he =>
        Nat.le_trans (scheduleRadius_within x.2 e he)
          (Nat.le_trans (Nat.le_max_left _ _) hx)
      have htail : radius xs ≤ H := Nat.le_trans (Nat.le_max_right _ _) hx
      change (x.1, mirrorSchedule H (encodeSchedule H x.2))::
          mirrorSpan H (encodeChart H xs) =
        (x.1, advanceSchedule H x.2)::advanceSpan H xs
      rw [mirrorSchedule_encodeSchedule H x.2 hhead, mirrorSpan_encodeChart H xs htail]

private theorem lift_zero : ∀ a, liftBoundary a polyZero = polyZero
  | 0 => rfl
  | a+1 => by
      rw [liftBoundary, lift_zero a]
      rfl

private theorem scheduled_advance (width a j : Nat) (p : RatPoly) :
    liftBoundary ((j+a)*(N width)) p =
      liftBoundary (a*(N width)) (liftBoundary (j*(N width)) p) := by
  have hindex : (j+a)*(N width) = a*(N width)+j*(N width) := by
    rw [Nat.add_mul, Nat.add_comm]
  rw [hindex]
  exact liftBoundary_add _ _ _

/-- The whole advanced ordered schedule is one common coordinate lift.
Padded equality is essential for the empty schedule's unit polynomial. -/
theorem windowProbe_advance (blocks width a : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    PaddedPolynomialCoeffEqv blocks (windowProbe width (advanceSchedule a fs))
      (liftBoundary (a*(N width)) (windowProbe width fs))
  | [] => (lift_one blocks (a*(N width))).symm
  | e::es => by
      change PaddedPolynomialCoeffEqv blocks
        (polyMul (liftBoundary ((e.1+a)*(N width)) (sourceProbe width e.2))
          (windowProbe width (advanceSchedule a es)))
        (liftBoundary (a*(N width))
          (polyMul (liftBoundary (e.1*(N width)) (sourceProbe width e.2)) (windowProbe width es)))
      rw [scheduled_advance width a e.1 (sourceProbe width e.2), lift_product]
      exact (PaddedPolynomialCoeffEqv.refl _ _).mul (windowProbe_advance blocks width a es)

/-- Arbitrary physical advance of every signed schedule is a single lift,
including empty spans/schedules, zero advance, and zero-width carriers. -/
theorem sourceSpan_advance (blocks width a : Nat) : (xs : DistanceSpan) →
    PaddedPolynomialCoeffEqv blocks (sourceSpan width (advanceSpan a xs))
      (liftBoundary (a*(N width)) (sourceSpan width xs))
  | [] => by
      change PaddedPolynomialCoeffEqv blocks polyZero (liftBoundary (a*(N width)) polyZero)
      rw [lift_zero]
      exact .refl _ _
  | x::xs => by
      change PaddedPolynomialCoeffEqv blocks
        (polyAdd (polySmul x.1 (windowProbe width (advanceSchedule a x.2)))
          (sourceSpan width (advanceSpan a xs)))
        (liftBoundary (a*(N width))
          (polyAdd (polySmul x.1 (windowProbe width x.2)) (sourceSpan width xs)))
      rw [lift_add, lift_smul]
      exact ((windowProbe_advance blocks width a x.2).smul x.1).add
        (sourceSpan_advance blocks width a xs)

/-- The actual mixed reflected insertion at physical lag n is a separated
product. No right radius bound is needed for this algebraic identity;
the genuine physical common-chart support is proved separately. -/
theorem mixedProduct_reflected_separated (blocks width R n : Nat)
    (xs ys : DistanceSpan) (hx : radius xs ≤ R) :
    PaddedPolynomialCoeffEqv blocks
      (mixedProduct width (R+n) (encodeChart (R+n) xs)
        (encodeChart (R+n) (advanceSpan n ys)))
      (polyMul (sourceSpan width (encodeChart R ys))
        (liftBoundary ((R+n)*(N width)) (sourceSpan width xs))) := by
  have hxH : radius xs ≤ R+n := Nat.le_trans hx (Nat.le_add_right _ _)
  unfold mixedProduct
  rw [mirrorSpan_encodeChart (R+n) xs hxH, encodeChart_advance R n ys]
  exact ((sourceSpan_advance blocks width (R+n) xs).mul
    (PaddedPolynomialCoeffEqv.refl blocks (sourceSpan width (encodeChart R ys)))).trans
    (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_comm _ _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe.mirrorSpan_encodeChart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe.windowProbe_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe.sourceSpan_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe.mixedProduct_reflected_separated
