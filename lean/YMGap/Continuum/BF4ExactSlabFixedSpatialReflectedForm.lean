/-
# The actual mixed reflected window form

This is the existing explicit-modulus window limit applied to the mixed
product of two finite signed spans of scheduled spatial face characters.
It is not a separately supplied state. Signed rational bilinearity retains
all cross terms and permits different polynomial caps in the three limits.
The diagonal is the already proved original-action reflected positive form.

Nome, spatial width and heat cutoff remain fixed. An intrinsic carrier,
radical quotient, physical transfer and continuum/physical-gap estimates
are not supplied by this module.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add)

local notation:max "N" width:arg => List.length (baseLinks width)

abbrev Span := List (Q' × List (Nat × List FaceFactor))

/-- Every schedule lies on the original half of the centered window. -/
def Within (h : Nat) (xs : Span) : Prop :=
  ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h

/-- The literal spatial-face domain; no arbitrary coordinate polynomial is
silently declared to be an original gauge observable. -/
def Physical (width : Nat) (xs : Span) : Prop :=
  ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width

def scaleSpan (c : Q') (xs : Span) : Span :=
  xs.map (fun x => (c*x.1, x.2))

theorem within_append {h : Nat} {xs ys : Span} (hx : Within h xs) (hy : Within h ys) :
    Within h (xs++ys) := by
  intro x hm
  cases List.mem_append.mp hm with
  | inl hx' => exact hx x hx'
  | inr hy' => exact hy x hy'

theorem physical_append {width : Nat} {xs ys : Span}
    (hx : Physical width xs) (hy : Physical width ys) : Physical width (xs++ys) := by
  intro x hm
  cases List.mem_append.mp hm with
  | inl hx' => exact hx x hx'
  | inr hy' => exact hy x hy'

theorem within_scale {h : Nat} (c : Q') {xs : Span} (hx : Within h xs) :
    Within h (scaleSpan c xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact hx y hy

theorem physical_scale {width : Nat} (c : Q') {xs : Span} (hx : Physical width xs) :
    Physical width (scaleSpan c xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact hx y hy

theorem sourceSpan_append (width : Nat) (xs ys : Span) :
    sourceSpan width (xs++ys) = polyAdd (sourceSpan width xs) (sourceSpan width ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change polyAdd (polySmul x.1 (windowProbe width x.2)) (sourceSpan width (xs++ys)) = _
      rw [ih]
      exact (List.append_assoc _ _ _).symm

theorem sourceSpan_scale (width : Nat) (c : Q') : (xs : Span) →
    RatPolyCoeffEqv (sourceSpan width (scaleSpan c xs)) (polySmul c (sourceSpan width xs))
  | [] => RatPolyCoeffEqv.refl _
  | x::xs =>
      ((RatPolyCoeffEqv.smul_assoc c x.1 (windowProbe width x.2)).symm.add
        (sourceSpan_scale width c xs)).trans
        (RatPolyCoeffEqv.smul_add c (polySmul x.1 (windowProbe width x.2))
          (sourceSpan width xs)).symm

theorem mirrorSpan_append (h : Nat) (xs ys : Span) :
    mirrorSpan h (xs++ys) = mirrorSpan h xs ++ mirrorSpan h ys :=
  List.map_append

theorem mirrorSpan_scale (h : Nat) (c : Q') (xs : Span) :
    mirrorSpan h (scaleSpan c xs) = scaleSpan c (mirrorSpan h xs) := by
  simp only [mirrorSpan, scaleSpan, List.map_map, Function.comp_def]

def mixedProduct (width h : Nat) (xs ys : Span) : RatPoly :=
  polyMul (sourceSpan width (mirrorSpan h xs)) (sourceSpan width ys)

theorem mixedProduct_supported (width h : Nat) (xs ys : Span) (hy : Within h ys) :
    SupportedQuaternionBlocks ((2*h+1)*(N width)) (mixedProduct width h xs ys) := by
  apply supported_polyMul
  · apply sourceSpan_supported
    intro x hm
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
    exact mirrorSchedule_within h y.2
  · apply sourceSpan_supported
    intro y hm e he
    have := hy y hm e he
    omega

theorem mixedProduct_add_left (width h : Nat) (xs ys zs : Span) :
    mixedProduct width h (xs++ys) zs =
      polyAdd (mixedProduct width h xs zs) (mixedProduct width h ys zs) := by
  simp only [mixedProduct, mirrorSpan_append, sourceSpan_append, polyMul_add_left_exact]

theorem mixedProduct_add_right (width h : Nat) (xs ys zs : Span) :
    RatPolyCoeffEqv (mixedProduct width h xs (ys++zs))
      (polyAdd (mixedProduct width h xs ys) (mixedProduct width h xs zs)) := by
  rw [mixedProduct, sourceSpan_append]
  exact RatPolyCoeffEqv.mul_add_right _ _ _

theorem mixedProduct_smul_left (width h : Nat) (c : Q') (xs ys : Span) :
    RatPolyCoeffEqv (mixedProduct width h (scaleSpan c xs) ys)
      (polySmul c (mixedProduct width h xs ys)) := by
  rw [mixedProduct, mirrorSpan_scale]
  exact ((sourceSpan_scale width c (mirrorSpan h xs)).mul (.refl _)).trans
    (RatPolyCoeffEqv.polyMul_smul_left _ _ _)

theorem mixedProduct_smul_right (width h : Nat) (c : Q') (xs ys : Span) :
    RatPolyCoeffEqv (mixedProduct width h xs (scaleSpan c ys))
      (polySmul c (mixedProduct width h xs ys)) :=
  ((RatPolyCoeffEqv.refl _).mul (sourceSpan_scale width c ys)).trans
    (RatPolyCoeffEqv.polyMul_smul_right _ _ _)

/-- The SAME existing limit, with its computed cap and constructive modulus.
The first guard records the intended half-window domain even though support
of the truncated mirror alone does not require it. -/
def form {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (_hx : Within h xs) (hy : Within h ys)
    (stage : Nat) : CReal :=
  polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
    (2*h) (mixedProduct width h xs ys) (mixedProduct_supported width h xs ys hy)

theorem form_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (hx : Within h xs) (hy : Within h ys) (stage : Nat) :
    ConvergesTo (fun t => ofQ' (windowRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) t (2*h) t (mixedProduct width h xs ys)))
      (form hw0 hw1 width h xs ys hx hy stage) :=
  polynomialWindow_converges hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
    (2*h) (mixedProduct width h xs ys) (mixedProduct_supported width h xs ys hy)

theorem form_self_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs : Span) (hx : Within h xs) (hf : Physical width xs) (stage : Nat) :
    leEv (ofQ' 0) (form hw0 hw1 width h xs xs hx hx stage) :=
  reflectedWindowLimit_nonnegative hw0 hw1 width h xs hx hf stage

theorem form_add_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys zs : Span)
    (hx : Within h xs) (hy : Within h ys) (hz : Within h zs) (stage : Nat) :
    Equiv (form hw0 hw1 width h (xs++ys) zs (within_append hx hy) hz stage)
      (add (form hw0 hw1 width h xs zs hx hz stage)
        (form hw0 hw1 width h ys zs hy hz stage)) := by
  unfold form
  have hp := mixedProduct_supported width h xs zs hz
  have hq := mixedProduct_supported width h ys zs hz
  exact Equiv.trans (windowLimit_congr hw0 hw1 _ width _ (2*h) _ (supported_add hp hq)
    (by rw [mixedProduct_add_left]; exact .refl _))
    (windowLimit_add hw0 hw1 _ width _ (2*h) hp hq)

theorem form_add_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys zs : Span)
    (hx : Within h xs) (hy : Within h ys) (hz : Within h zs) (stage : Nat) :
    Equiv (form hw0 hw1 width h xs (ys++zs) hx (within_append hy hz) stage)
      (add (form hw0 hw1 width h xs ys hx hy stage)
        (form hw0 hw1 width h xs zs hx hz stage)) := by
  unfold form
  have hp := mixedProduct_supported width h xs ys hy
  have hq := mixedProduct_supported width h xs zs hz
  exact Equiv.trans (windowLimit_congr hw0 hw1 _ width _ (2*h) _ (supported_add hp hq)
    (mixedProduct_add_right width h xs ys zs))
    (windowLimit_add hw0 hw1 _ width _ (2*h) hp hq)

theorem form_smul_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (c : Q') (xs ys : Span)
    (hx : Within h xs) (hy : Within h ys) (stage : Nat) :
    Equiv (form hw0 hw1 width h (scaleSpan c xs) ys (within_scale c hx) hy stage)
      (mul (ofQ' c) (form hw0 hw1 width h xs ys hx hy stage)) := by
  unfold form
  have hp := mixedProduct_supported width h xs ys hy
  exact Equiv.trans (windowLimit_congr hw0 hw1 _ width _ (2*h) _ (supported_smul hp c)
    (mixedProduct_smul_left width h c xs ys))
    (windowLimit_smul hw0 hw1 _ width _ (2*h) c hp)

theorem form_smul_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (c : Q') (xs ys : Span)
    (hx : Within h xs) (hy : Within h ys) (stage : Nat) :
    Equiv (form hw0 hw1 width h xs (scaleSpan c ys) hx (within_scale c hy) stage)
      (mul (ofQ' c) (form hw0 hw1 width h xs ys hx hy stage)) := by
  unfold form
  have hp := mixedProduct_supported width h xs ys hy
  exact Equiv.trans (windowLimit_congr hw0 hw1 _ width _ (2*h) _ (supported_smul hp c)
    (mixedProduct_smul_right width h c xs ys))
    (windowLimit_smul hw0 hw1 _ width _ (2*h) c hp)

/-- Symmetry is inherited from reflection of the original selected action,
not assumed as a property of an abstract limiting state. -/
theorem form_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (hx : Within h xs) (hy : Within h ys)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage : Nat) :
    Equiv (form hw0 hw1 width h xs ys hx hy stage)
      (form hw0 hw1 width h ys xs hy hx stage) := by
  apply Equiv_of_limit_of_equal
    (hA := form_converges hw0 hw1 width h xs ys hx hy stage)
    (hB := form_converges hw0 hw1 width h ys xs hy hx stage)
  intro t
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    reflectedWindowRatio_symm hw0 hw1 width h xs ys hx hxf hy hyf stage t)

/-- Enlarge both ends while preserving every position relative to the
reflection plane. The two factors share ONE lift. Two proved padding laws
then identify the already-constructed limits; no finite stationarity or
identical representative modulus is presumed. -/
theorem form_centered_inclusion {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (hx : Within h xs) (hy : Within h ys) (stage : Nat) :
    Equiv (form hw0 hw1 width (h+1) (shiftSpan xs) (shiftSpan ys)
      (shiftSpan_within h xs hx) (shiftSpan_within h ys hy) stage)
      (form hw0 hw1 width h xs ys hx hy stage) := by
  have hp := mixedProduct_supported width h xs ys hy
  have hleft := windowSupport_left hp
  have hright := windowSupport_right hleft
  have he : 2*(h+1) = (2*h+1)+1 := by omega
  have hq : SupportedQuaternionBlocks ((2*(h+1)+1)*(N width))
      (liftBoundary (N width) (mixedProduct width h xs ys)) := by
    simpa only [he] using hright
  have hpin := mixedReflectedProduct_shift ((2*(h+1)+1)*(N width)) width h xs ys hx
  have hpad := Equiv.trans
    (windowLimit_pad_right hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (2*h+1) (liftBoundary (N width) (mixedProduct width h xs ys)) hleft)
    (windowLimit_pad_left hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (2*h) (mixedProduct width h xs ys) hp)
  unfold form
  exact Equiv.trans (windowLimit_padded_congr hw0 hw1 _ width _ (2*(h+1)) _ hq hpin)
    (by simpa only [he] using hpad)

end YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.scaleSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.within_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.physical_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.within_scale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.physical_scale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.sourceSpan_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.sourceSpan_scale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mirrorSpan_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mirrorSpan_scale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mixedProduct
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mixedProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mixedProduct_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mixedProduct_add_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mixedProduct_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.mixedProduct_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_self_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_add_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm.form_centered_inclusion
