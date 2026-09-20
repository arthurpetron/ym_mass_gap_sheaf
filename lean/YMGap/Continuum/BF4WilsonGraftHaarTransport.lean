/-
# A source Haar identity survives every original graft context

The source certificate is transported to a finite slab and then to the actual
shifted chart at an arbitrary larger spatial base. Its supplied input window
is retained as a supported insertion. This proves equality against the FULL
interacting insertion; no link independence or factorization is invoked.

All extents, shifts and room inequalities are constructed from the source
duration and the input's support. The consequence is used by the existing
reflected-form descent and duration-preserving kernel, not by the old
vacuum-only compiler.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionHaarSourceIdentity
import YMGap.Continuum.BF4WilsonShiftedInclusionPlacement
import YMGap.Continuum.BF4WilsonChronologicalKernel

namespace YMGap.Continuum.BF4WilsonGraftHaarTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison (chartInsertion centeredExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent)
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding (Placement)
open YMGap.Continuum.BF4WilsonSpatialUnionHaarSourceIdentity (placed_source_haar_congr)
open YMGap.Continuum.BF4WilsonShiftedInclusionPlacement
open YMGap.Continuum.BF4WilsonChronologicalKernel (graft)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

local notation:max "N" base:arg => List.length (baseLinks base)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The auxiliary source slab is an observable coordinate carrier, not a
replacement for the original target action. -/
def graftPlacement {base larger : Nat} (hb : base ≤ larger) (H K r t : Nat) : Placement where
  source := base+H
  target := chartExtent larger r (H+K) t
  space := r+1
  time := paddedWidth larger r+1+t+K
  space_room := by unfold chartExtent adjacentEvenExtent centralExtent paddedWidth; omega
  time_room := by unfold chartExtent adjacentEvenExtent centralExtent paddedWidth; omega

/-- Source identity at ONE finite carrier, placed at the later interval of
ANY larger original input chart. -/
theorem chart_shifted_include_haar_congr {base larger : Nat} (hb : base ≤ larger)
    (H K r t : Nat) (e f : WindowExpression base) (he : Within H e) (hf : Within H f)
    (hp : SupportedHaarEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    SupportedHaarEqv (B (chartExtent larger r (H+K) t))
      (chartInsertion r (H+K) t (shift K (includeExpression hb e)))
      (chartInsertion r (H+K) t (shift K (includeExpression hb f))) := by
  let P := graftPlacement hb H K r t
  have hw : base ≤ P.source := Nat.le_add_right _ _
  have ht : 0+H ≤ P.source := by dsimp [P, graftPlacement]; omega
  have hroom : base+P.space ≤ paddedWidth larger r := by
    dsimp [P, graftPlacement, paddedWidth]; omega
  have hsource := placed_source_haar_congr hw ht e f he hf hp
  have htransport := P.embedding.polynomial_supportedHaar_congr
    (placed_supported P.source 0 e) (placed_supported P.source 0 f) hsource
  have hepin := SupportedHaarEqv.of_padded
    (PaddedPolynomialCoeffEqv.of_prefix (placed_pin P hroom hw ht e he))
    (P.embedding.polynomial_supported _) (placed_supported _ _ _)
  have hfpin := SupportedHaarEqv.of_padded
    (PaddedPolynomialCoeffEqv.of_prefix (placed_pin P hroom hw ht f hf))
    (P.embedding.polynomial_supported _) (placed_supported _ _ _)
  rw [chartInsertion_shifted_include, chartInsertion_shifted_include]
  simpa only [P, graftPlacement, Nat.zero_add] using
    hepin.symm.trans (htransport.trans hfpin)

/-- Multiplication retains the entire supplied input expression as a test;
the transported identity is not merely equality of bare expectations. -/
theorem chart_graft_haar_congr {base larger : Nat} (hb : base ≤ larger)
    (H K r t : Nat) (e f : WindowExpression base) (he : Within H e) (hf : Within H f)
    (hp : SupportedHaarEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f))
    (z : WindowExpression larger) :
    SupportedHaarEqv (B (chartExtent larger r (H+K) t))
      (chartInsertion r (H+K) t (graft K (includeExpression hb e) z))
      (chartInsertion r (H+K) t (graft K (includeExpression hb f) z)) :=
  (chart_shifted_include_haar_congr hb H K r t e f he hf hp).mul
    (.refl _ (chartInsertion r (H+K) t z))
    (placed_supported _ _ _) (placed_supported _ _ _)

end YMGap.Continuum.BF4WilsonGraftHaarTransport

#print axioms YMGap.Continuum.BF4WilsonGraftHaarTransport.graftPlacement
#print axioms YMGap.Continuum.BF4WilsonGraftHaarTransport.chart_shifted_include_haar_congr
#print axioms YMGap.Continuum.BF4WilsonGraftHaarTransport.chart_graft_haar_congr
