/-
# Symmetry of the original spatial Wilson-window reflected form

Both signed Wilson expressions are placed on the SAME centered original
selected chain. Literal ordered-word reflection identifies their mirrors;
the existing original-action reflection theorem swaps the two factors
without changing the heat stage or reciprocal partition. Equality on the
unmodified spatial/time/cutoff diagonal then gives equality of its existing
constructive limits.

The finite identity needs only the original nome bounds. The limit retains
the spatial construction's small-nome guards. This supplies symmetry for
the enlarged reflected form, not its completed strict bound, full gauge
observable coverage, physical spacing limit or continuum QFT.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization (blockCount)
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction (selectedHeat selectedHeat_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection (selectedIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent chartIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem finite_reflected_image {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (p p' q : RatPoly)
    (hp' : SupportedQuaternionBlocks (blockCount radius) p')
    (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hr : ReflectionImage (adjacentEvenExtent radius) p p') (stage : Nat) :
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q) stage ≈
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi) (polyMul p' q) stage := by
  have ha := selectedHeat_supported w (headCutoff w+stage) radius (selectedIds radius width start depth)
  apply Q'.mul_eqv_congr_right
  exact ((PaddedPolynomialCoeffEqv.mul hr (.refl _ q)).mul (.refl _
    (selectedHeat w (headCutoff w+stage) radius (selectedIds radius width start depth)))).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq) ha)
      (supported_polyMul (supported_polyMul hp' hq) ha)

/-- Mixed symmetry on the actual centered chart, with identical selected
action, heat stage and reciprocal partition. -/
theorem chartScalar_reflected_symm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) (r stage t : Nat) :
    chartScalar hw0 hw1 H (.mul (mirror H e) f) r stage t ≈
      chartScalar hw0 hw1 H (.mul (mirror H f) e) r stage t := by
  let width := paddedWidth base r
  let radius := width+t+H
  let start := width+1
  let E := adjacentEvenExtent radius
  have hw : width ≤ E := by
    unfold E adjacentEvenExtent centralExtent radius
    omega
  have hcenter : start+t+H=radius+1 := by unfold start radius; omega
  have hcount : t+(2*H+t)=2*(t+H) := by omega
  let p := placedPolynomial E (start+t) (centeredExpression r e)
  let q := placedPolynomial E (start+t) (centeredExpression r f)
  let rp := placedPolynomial E (start+t) (mirror H (centeredExpression r e))
  let rq := placedPolynomial E (start+t) (mirror H (centeredExpression r f))
  have hp := placed_supported E (start+t) (centeredExpression r e)
  have hq := placed_supported E (start+t) (centeredExpression r f)
  have hrp := placed_supported E (start+t) (mirror H (centeredExpression r e))
  have hrq := placed_supported E (start+t) (mirror H (centeredExpression r f))
  have hleft := finite_reflected_image hw0 hw1 radius width start (t+H) p rp q hrp hq
    (placed_reflection hw hcenter (centeredExpression r e) ((centered_within r H e).mpr he)) stage
  have hright := finite_reflected_image hw0 hw1 radius width start (t+H) q rq p hrq hp
    (placed_reflection hw hcenter (centeredExpression r f) ((centered_within r H f).mpr hf)) stage
  have hsymm := originalChain_finiteValue_reflected_symm hw0 hw1 radius width start (t+H)
    (by omega) p q hp hq stage
  have hmixed := Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft) (Q'.eqv_trans _ _ _ hsymm hright)
  simpa only [p, q, rp, rq, E, radius, start, width, chartScalar, chartInsertion,
    chartExtent, chartIds, selectedIds, hcount, centeredExpression, recenterExpression,
    mirror, recenter_mapOffsets, placedPolynomial] using hmixed

attribute [local irreducible] chartScalar spatialLimit

/-- Equality on the original three-regulator diagonal identifies the two
already constructed spatial limits; no new state or limit is selected. -/
theorem spatialLimit_reflected_symm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base) :
    Equiv (spatialLimit hw0 hw1 H (.mul (mirror H e) f)
      ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb)
      (spatialLimit hw0 hw1 H (.mul (mirror H f) e)
        ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) e he⟩ hsmall hd hs hb) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => chartScalar_reflected_symm hw0 hw1 H e f he hf n n n))
    (spatial_diagonal_converges hw0 hw1 H (.mul (mirror H e) f)
      ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb)
    (spatial_diagonal_converges hw0 hw1 H (.mul (mirror H f) e)
      ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) e he⟩ hsmall hd hs hb)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry.chartScalar_reflected_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry.spatialLimit_reflected_symm
