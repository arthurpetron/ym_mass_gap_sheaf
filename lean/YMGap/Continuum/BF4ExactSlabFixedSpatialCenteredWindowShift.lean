/-
# Centered inclusion of actual signed spatial-probe windows

Enlarging a half-window from h to h+1 while increasing every scheduled
offset by one preserves each observable's position relative to the
reflection plane. Coefficients, ordered face words, repetitions, and the
inclusive spatial fringe are unchanged. The corresponding source
polynomial is the existing one-slice lift, up to padded coefficients.

The mixed reflected product has one common lift, not two independently
integrated factors. This supplies the polynomial pin for the existing
left/right window-limit padding laws. No stationarity, quotient,
completion, or physical transfer assertion is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive
import YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (sourceProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Move each actual schedule entry by one slice, retaining its face list. -/
def shiftSchedule (fs : List (Nat × List FaceFactor)) :
    List (Nat × List FaceFactor) :=
  fs.map (fun e => (e.1+1, e.2))

/-- Shift every schedule, leaving all signed rational coefficients unchanged. -/
def shiftSpan (xs : List (Q' × List (Nat × List FaceFactor))) :
    List (Q' × List (Nat × List FaceFactor)) :=
  xs.map (fun x => (x.1, shiftSchedule x.2))

theorem shiftSchedule_within (L : Nat) (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L) :
    ∀ e, e ∈ shiftSchedule fs → e.1 ≤ L+1 := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  exact Nat.add_le_add_right (hwithin f hf) 1

theorem shiftSpan_within (L : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ L) :
    ∀ x, x ∈ shiftSpan xs → ∀ e, e ∈ x.2 → e.1 ≤ L+1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact shiftSchedule_within L y.2 (hwithin y hy)

theorem shiftSchedule_faces {width : Nat}
    (fs : List (Nat × List FaceFactor))
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ e, e ∈ shiftSchedule fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  exact hfaces g hg

theorem shiftSpan_faces {width : Nat}
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 →
      f.1 ∈ spatialFaces width) :
    ∀ x, x ∈ shiftSpan xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 →
      f.1 ∈ spatialFaces width := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact shiftSchedule_faces y.2 (hfaces y hy)

/-- The shifted source uses exactly the existing chronological blocks. -/
theorem windowProbe_shift_supported (width L : Nat)
    (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L) :
    SupportedQuaternionBlocks ((L+1+1)*(N width))
      (windowProbe width (shiftSchedule fs)) :=
  windowProbe_supported width (L+1) _ (shiftSchedule_within L fs hwithin)

theorem sourceSpan_shift_supported (width L : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ L) :
    SupportedQuaternionBlocks ((L+1+1)*(N width))
      (sourceSpan width (shiftSpan xs)) :=
  sourceSpan_supported width (L+1) _ (shiftSpan_within L xs hwithin)

private theorem lift_zero : ∀ n, liftBoundary n polyZero = polyZero
  | 0 => rfl
  | n+1 => by
      rw [liftBoundary, lift_zero n]
      rfl

private theorem scheduled_shift (width j : Nat) (p : RatPoly) :
    liftBoundary ((j+1)*(N width)) p =
      liftBoundary (N width) (liftBoundary (j*(N width)) p) := by
  have hindex : (j+1)*(N width) = N width+j*(N width) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [hindex]
  exact liftBoundary_add _ _ _

/-- One common lift of the complete ordered product. Padded coefficients
also retain the empty schedule, whose unit has extra zero exponents after
lifting. No geometric or nonempty-carrier hypothesis is needed. -/
theorem windowProbe_shift (blocks width : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    PaddedPolynomialCoeffEqv blocks (windowProbe width (shiftSchedule fs))
      (liftBoundary (N width) (windowProbe width fs))
  | [] => (lift_one blocks (N width)).symm
  | e::es => by
      change PaddedPolynomialCoeffEqv blocks
        (polyMul (liftBoundary ((e.1+1)*(N width)) (sourceProbe width e.2))
          (windowProbe width (shiftSchedule es)))
        (liftBoundary (N width)
          (polyMul (liftBoundary (e.1*(N width)) (sourceProbe width e.2))
            (windowProbe width es)))
      rw [scheduled_shift width e.1 (sourceProbe width e.2), lift_product]
      exact (PaddedPolynomialCoeffEqv.refl _ _).mul
        (windowProbe_shift blocks width es)

/-- The same common lift preserves every coefficient and cross term of
the finite signed span. -/
theorem sourceSpan_shift (blocks width : Nat) :
    (xs : List (Q' × List (Nat × List FaceFactor))) →
    PaddedPolynomialCoeffEqv blocks (sourceSpan width (shiftSpan xs))
      (liftBoundary (N width) (sourceSpan width xs))
  | [] => by
      change PaddedPolynomialCoeffEqv blocks polyZero (liftBoundary (N width) polyZero)
      rw [lift_zero]
      exact .refl _ _
  | x::xs => by
      change PaddedPolynomialCoeffEqv blocks
        (polyAdd (polySmul x.1 (windowProbe width (shiftSchedule x.2)))
          (sourceSpan width (shiftSpan xs)))
        (liftBoundary (N width)
          (polyAdd (polySmul x.1 (windowProbe width x.2)) (sourceSpan width xs)))
      rw [lift_add, lift_smul]
      exact ((windowProbe_shift blocks width x.2).smul x.1).add
        (sourceSpan_shift blocks width xs)

/-- Centered inclusion commutes literally with reflection. The original
half-window guard rules out truncated-subtraction artifacts. -/
theorem mirrorSchedule_shift (h : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ h) →
    mirrorSchedule (h+1) (shiftSchedule fs) = shiftSchedule (mirrorSchedule h fs)
  | [], _ => rfl
  | e::es, hwithin => by
      have he := hwithin e List.mem_cons_self
      have htime : 2*(h+1)-(e.1+1) = (2*h-e.1)+1 := by omega
      change (2*(h+1)-(e.1+1), e.2)::mirrorSchedule (h+1) (shiftSchedule es) =
        ((2*h-e.1)+1, e.2)::shiftSchedule (mirrorSchedule h es)
      rw [htime, mirrorSchedule_shift h es
        (fun a ha => hwithin a (List.mem_cons_of_mem e ha))]

theorem mirrorSpan_shift (h : Nat) :
    (xs : List (Q' × List (Nat × List FaceFactor))) →
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h) →
    mirrorSpan (h+1) (shiftSpan xs) = shiftSpan (mirrorSpan h xs)
  | [], _ => rfl
  | x::xs, hwithin => by
      change (x.1, mirrorSchedule (h+1) (shiftSchedule x.2))::
          mirrorSpan (h+1) (shiftSpan xs) =
        (x.1, shiftSchedule (mirrorSchedule h x.2))::shiftSpan (mirrorSpan h xs)
      rw [mirrorSchedule_shift h x.2 (hwithin x List.mem_cons_self),
        mirrorSpan_shift h xs (fun y hy => hwithin y (List.mem_cons_of_mem x hy))]

/-- Both factors of the actual mixed reflected product undergo the same
coordinate lift. Only the reflected schedule needs the half-window guard
for this coefficient pin; support of the second span is a separate fact. -/
theorem mixedReflectedProduct_shift (blocks width h : Nat)
    (xs ys : List (Q' × List (Nat × List FaceFactor)))
    (hx : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h) :
    PaddedPolynomialCoeffEqv blocks
      (polyMul (sourceSpan width (mirrorSpan (h+1) (shiftSpan xs)))
        (sourceSpan width (shiftSpan ys)))
      (liftBoundary (N width)
        (polyMul (sourceSpan width (mirrorSpan h xs)) (sourceSpan width ys))) := by
  rw [mirrorSpan_shift h xs hx, lift_product]
  exact (sourceSpan_shift blocks width (mirrorSpan h xs)).mul
    (sourceSpan_shift blocks width ys)

/-- Diagonal specialization for the already-defined reflected insertion. -/
theorem reflectedWindowProduct_shift (blocks width h : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hx : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h) :
    PaddedPolynomialCoeffEqv blocks (reflectedWindowProduct width (h+1) (shiftSpan xs))
      (liftBoundary (N width) (reflectedWindowProduct width h xs)) :=
  mixedReflectedProduct_shift blocks width h xs xs hx

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.shiftSchedule
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.shiftSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.shiftSchedule_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.shiftSpan_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.shiftSchedule_faces
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.shiftSpan_faces
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.windowProbe_shift_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.sourceSpan_shift_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.windowProbe_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.sourceSpan_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.mirrorSchedule_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.mirrorSpan_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.mixedReflectedProduct_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift.reflectedWindowProduct_shift
