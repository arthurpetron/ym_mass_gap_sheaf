/-
# Reflected positivity of the constructed fixed-width window limit

A finite rational linear combination of scheduled spatial probes is placed
on the lower half of a symmetric selected chain. Its reflected schedule
has offsets 2*h-j and the SAME signed coefficients. The exact original
bilinear pin and finite selected-action reflection positivity make every
diagonal window value nonnegative. The existing explicit-modulus CReal
window limit inherits this property through its actual representatives.

The compact insertion is fixed as the two time boundaries recede; only its
ambient placement varies. All finite terms retain the SAME selected action,
heat cutoff and partition. This is real rational reflected positivity on
the scheduled spatial-probe span, not merely positivity of one product.

Nome, spatial width and retained heat cutoff are fixed. No new limit is
chosen and no time/cutoff interchange is asserted. Gauge-observable
completeness, an intrinsic reflected carrier and its quotient/transfer/
vacuum, uniform spatial/spacing estimates and continuum Clay closure remain
open. In particular this is not a Hamiltonian mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Reflection changes only scheduled time offsets, not rational coefficients. -/
def mirrorSpan (h : Nat) (xs : List (Q' × List (Nat × List FaceFactor))) :=
  xs.map (fun x => (x.1, mirrorSchedule h x.2))

/-- The fixed compact insertion; independent of the receding boundaries. -/
def reflectedWindowProduct (width h : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor))) : RatPoly :=
  polyMul (sourceSpan width (mirrorSpan h xs)) (sourceSpan width xs)

private theorem mirror_within (h : Nat) (xs : List (Q' × List (Nat × List FaceFactor))) :
    ∀ x, x ∈ mirrorSpan h xs → ∀ e, e ∈ x.2 → e.1 ≤ 2*h := by
  intro x hm
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_within h y.2

private theorem mirror_faces {width : Nat} (h : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hx : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ x, x ∈ mirrorSpan h xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 →
      f.1 ∈ spatialFaces width := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces h y.2 (hx y hy)

theorem reflectedWindowProduct_supported (width h : Nat)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hx : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h) :
    SupportedQuaternionBlocks ((2*h+1)*(baseLinks width).length)
      (reflectedWindowProduct width h xs) :=
  supported_polyMul (sourceSpan_supported width (2*h) (mirrorSpan h xs) (mirror_within h xs))
    (sourceSpan_supported width (2*h) xs (fun x hx' e he => by have := hx x hx' e he; omega))

/-- Linearity preserves the original signed reflected schedule pin. -/
theorem placedSpan_reflection {width radius A h : Nat}
    (hw : width ≤ adjacentEvenExtent radius) (hcenter : A+h=radius+1) :
    (xs : List (Q' × List (Nat × List FaceFactor))) →
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h) →
    (hfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) →
    ReflectionImage (adjacentEvenExtent radius)
      (placedSpan (adjacentEvenExtent radius) A xs)
      (placedSpan (adjacentEvenExtent radius) A (mirrorSpan h xs))
  | [], _, _ => ReflectionImage.zero _
  | x::xs, ht, hf =>
      ((placed_reflection hw hcenter x.2 (ht x List.mem_cons_self)
        (hf x List.mem_cons_self)).smul x.1).add
        (placedSpan_reflection hw hcenter xs
          (fun y hy => ht y (List.mem_cons_of_mem x hy))
          (fun y hy => hf y (List.mem_cons_of_mem x hy)))

theorem placedSpan_oneSided {width radius A h : Nat}
    (hw : width ≤ adjacentEvenExtent radius) (hcenter : A+h=radius+1)
    (xs : List (Q' × List (Nat × List FaceFactor)))
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h)
    (hfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    OneSided radius (placedSpan (adjacentEvenExtent radius) A xs) :=
  BlockLocal.finiteSum _ xs (fun x hx =>
    (placed_oneSided hw hcenter x.2 (hwithin x hx) (hfaces x hx)).smul x.1)

/-- Exact same-action normalization respects the original reflected image. -/
private theorem finite_reflected_image {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blockCount radius) p)
    (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hr : ReflectionImage (adjacentEvenExtent radius) p q) (stage : Nat) :
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
        (fun _ hi => chainIds_physical hi)
        (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) stage ≈
      finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
        (fun _ hi => chainIds_physical hi) (polyMul q p) stage := by
  have ha := selectedHeat_supported w (headCutoff w+stage) radius (selectedIds radius width start depth)
  apply Q'.mul_eqv_congr_right
  exact ((PaddedPolynomialCoeffEqv.mul hr (.refl _ p)).mul (.refl _
    (selectedHeat w (headCutoff w+stage) radius (selectedIds radius width start depth)))).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hp) ha)
      (supported_polyMul (supported_polyMul hq hp) ha)

/-- Every diagonal uses a reflection-centered placement of the SAME compact
insertion. Both boundaries recede without changing its coefficients/cutoff. -/
theorem reflectedWindowRatio_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs : List (Q' × List (Nat × List FaceFactor)))
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h)
    (hfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (stage t : Nat) :
    (0 : Q') ≤ windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      t (2*h) t (reflectedWindowProduct width h xs) := by
  let radius := width+t+h
  let start := width+1
  let E := adjacentEvenExtent radius
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent radius; omega
  have hcenter : start+t+h=radius+1 := by unfold start radius; omega
  have ht : start+(t+(2*h+t)) ≤ E := by unfold E adjacentEvenExtent centralExtent radius start; omega
  have hcount : t+(2*h+t)=2*(t+h) := by omega
  let p := placedSpan E (start+t) xs
  let q := placedSpan E (start+t) (mirrorSpan h xs)
  have hp := placedSpan_supported E (start+t) xs
  have hq := placedSpan_supported E (start+t) (mirrorSpan h xs)
  have hr := placedSpan_reflection hw hcenter xs hwithin hfaces
  have hn := originalChain_finiteValue_nonnegative hw0 hw1 radius width start (t+h)
    (by omega) p (placedSpan_oneSided hw hcenter xs hwithin hfaces) hp stage
  have he := finite_reflected_image hw0 hw1 radius width start (t+h) p q hp hq hr stage
  have hpin := windowRatio_span_mul_originalFiniteValue hw0 hw1 (m := t) (L := 2*h) (n := t)
    hw ht (mirrorSpan h xs) xs (mirror_within h xs) (mirror_faces h xs hfaces)
    (fun x hx e he => by have := hwithin x hx e he; omega) hfaces stage
  have hn' := Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he)
  apply Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hpin)
  simpa only [selectedIds, hcount] using hn'

/-- Real rational reflected positivity on the finite scheduled-observable
span, for the EXISTING time limit with its unchanged explicit modulus. -/
theorem reflectedWindowLimit_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs : List (Q' × List (Nat × List FaceFactor)))
    (hwithin : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → e.1 ≤ h)
    (hfaces : ∀ x, x ∈ xs → ∀ e, e ∈ x.2 → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width)
    (stage : Nat) :
    leEv (ofQ' 0) (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (2*h) (reflectedWindowProduct width h xs) (reflectedWindowProduct_supported width h xs hwithin)) :=
  leEv_ofQ'_of_approx_ge (fun k => reflectedWindowRatio_nonnegative hw0 hw1 width h xs
    hwithin hfaces stage (QMhat _ (polynomialWindowCauchy hw0 hw1 (headCutoff w+stage)
      width (Nat.le_add_right _ _) (2*h) (reflectedWindowProduct width h xs)
      (reflectedWindowProduct_supported width h xs hwithin)) k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive.mirrorSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive.reflectedWindowProduct
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive.reflectedWindowProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive.placedSpan_reflection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive.placedSpan_oneSided
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive.reflectedWindowRatio_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive.reflectedWindowLimit_nonnegative
