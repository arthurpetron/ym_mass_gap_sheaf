/-
# Reflected positivity for original multi-time Wilson expressions

The complete signed expression is placed below the reflection plane. Its
literal reflected word expression supplies the other factor; neither a
product-state law nor positivity of separate factors is substituted. The
existing symmetric selected-action theorem and the exact original window
normalization give positivity at every receding-time diagonal. The SAME
constructed CReal window limit inherits that positivity.

Nome, width, window and retained heat cutoff remain fixed. This enlarges
the verified reflected observable domain beyond face-character syntax; it
does not supply full gauge-observable coverage, its quotient/completion,
an extension of the old completed-carrier strict bound, spatial/spacing
control or continuum Yang--Mills existence.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflectionPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

/-- A fixed compact expression; only its physical placement will recede. -/
def reflectedWindowProduct {width : Nat} (h : Nat) (e : WindowExpression width) : RatPoly :=
  sourcePolynomial (.mul (mirror h e) e)

theorem reflectedWindowProduct_supported {width : Nat} (h : Nat)
    (e : WindowExpression width) (he : Within h e) :
    SupportedQuaternionBlocks ((2*h+1)*(baseLinks width).length)
      (reflectedWindowProduct h e) :=
  source_supported (2*h) (.mul (mirror h e) e)
    ⟨mirror_within h e, within_mono (by omega : h ≤ 2*h) e he⟩

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

/-- Finite reflected positivity retains every signed term, the original full
selected action, the cutoff and the SAME partition on both sides of the pin. -/
theorem reflectedWindowRatio_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (h : Nat) (e : WindowExpression width) (he : Within h e)
    (stage t : Nat) :
    (0 : Q') ≤ windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      t (2*h) t (reflectedWindowProduct h e) := by
  let radius := width+t+h
  let start := width+1
  let E := adjacentEvenExtent radius
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent radius; omega
  have hcenter : start+t+h=radius+1 := by unfold start radius; omega
  have ht : start+(t+(2*h+t)) ≤ E := by
    unfold E adjacentEvenExtent centralExtent radius start
    omega
  have hcount : t+(2*h+t)=2*(t+h) := by omega
  let p := placedPolynomial E (start+t) e
  let q := placedPolynomial E (start+t) (mirror h e)
  have hp := placed_supported E (start+t) e
  have hq := placed_supported E (start+t) (mirror h e)
  have hr := placed_reflection hw hcenter e he
  have hn := originalChain_finiteValue_nonnegative hw0 hw1 radius width start (t+h)
    (by omega) p (placed_oneSided hw hcenter e he) hp stage
  have himage := finite_reflected_image hw0 hw1 radius width start (t+h) p q hp hq hr stage
  have hpin := windowRatio_originalFiniteValue hw0 hw1 (m := t) (L := 2*h) (n := t)
    hw ht (.mul (mirror h e) e)
    ⟨mirror_within h e, within_mono (by omega : h ≤ 2*h) e he⟩ stage
  have hn' := Q'.le_trans' _ _ _ hn (Q'.le_of_eqv himage)
  apply Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hpin)
  simpa only [selectedIds, hcount, placedPolynomial] using hn'

/-- Reflected positivity of the EXISTING fixed-width, fixed-cutoff time
limit for arbitrary finite signed multi-time spatial Wilson expressions. -/
theorem reflectedWindowLimit_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (h : Nat) (e : WindowExpression width) (he : Within h e)
    (stage : Nat) :
    leEv (ofQ' 0) (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (2*h) (reflectedWindowProduct h e) (reflectedWindowProduct_supported h e he)) :=
  leEv_ofQ'_of_approx_ge (fun k => reflectedWindowRatio_nonnegative hw0 hw1 h e he stage
    (QMhat _ (polynomialWindowCauchy hw0 hw1 (headCutoff w+stage)
      width (Nat.le_add_right _ _) (2*h) (reflectedWindowProduct h e)
      (reflectedWindowProduct_supported h e he)) k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive.reflectedWindowProduct
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive.reflectedWindowProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive.reflectedWindowRatio_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive.reflectedWindowLimit_nonnegative
