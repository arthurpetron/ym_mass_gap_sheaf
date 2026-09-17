/-
# Source Haar identities reach the SAME original Wilson states

One supported Haar identity on the finite chronological source transports
through both original block embeddings: source to a time-zero slab, then
that slab to the actual centered chart. The old polynomial expression pins
identify the endpoints. Haar identity transport allows the full interacting
target insertion, so the original reflected-form descent applies unchanged.

The conclusion is equality in the existing Wilson union completion, now
including supplied sphere identities rather than only free-polynomial
coefficient equality. All source support and room guards are proved, and
all original small-nome guards are retained. This does not define products
of arbitrary OS-null states or supply full canonical OS/QFT realization.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity
import YMGap.Continuum.BF4WilsonSpatialUnionHaarObservableDescent
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality
import YMGap.Continuum.BF4WilsonBacktrackSourceIdentity

namespace YMGap.Continuum.BF4WilsonSpatialUnionHaarSourceIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (placed_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (chartInsertion centeredExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent)
open YMGap.Continuum.BF4WilsonSpatialUnion (ofExpression)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm (embedStage)
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity (sourcePlacement)
open YMGap.Continuum.BF4WilsonSpatialUnionHaarObservableDescent
  (embedStage_eq_of_haar_diagonal)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local notation:max "N" base:arg => List.length (baseLinks base)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Chronological placement transports the genuine Haar identity, with both
source supports supplied by the actual window bounds. -/
theorem placed_source_haar_congr {base start H extent : Nat}
    (hw : base ≤ extent) (ht : start+H ≤ extent)
    (e f : WindowExpression base) (he : Within H e) (hf : Within H f)
    (hp : SupportedHaarEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    SupportedHaarEqv (B extent)
      (placedPolynomial extent start e) (placedPolynomial extent start f) := by
  let E := BF4ExactSlabFixedSpatialChainCarrier.embedding H hw ht
  have hepin := SupportedHaarEqv.of_padded (expression_pin hw ht e he)
    (E.polynomial_supported _) (placed_supported extent start e)
  have hfpin := SupportedHaarEqv.of_padded (expression_pin hw ht f hf)
    (E.polynomial_supported _) (placed_supported extent start f)
  exact hepin.symm.trans
    ((E.polynomial_supportedHaar_congr (source_supported H e he)
      (source_supported H f hf) hp).trans hfpin)

/-- Literal recentering/translation retains equality against every supported
target test, including the entire original action. -/
theorem chartInsertion_source_haar_congr {base : Nat} (r H t : Nat)
    (e f : WindowExpression base) (he : Within H e) (hf : Within H f)
    (hp : SupportedHaarEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    SupportedHaarEqv (B (chartExtent base r H t))
      (chartInsertion r H t e) (chartInsertion r H t f) := by
  let P := sourcePlacement base r H t
  have hw : base ≤ P.source := Nat.le_add_right _ _
  have ht : 0+H ≤ P.source := by dsimp [P, sourcePlacement]; omega
  have hroom : base+P.space ≤ paddedWidth base r := by
    dsimp [P, sourcePlacement, paddedWidth]; omega
  have hsource := placed_source_haar_congr hw ht e f he hf hp
  have htransport := P.embedding.polynomial_supportedHaar_congr
    (placed_supported P.source 0 e) (placed_supported P.source 0 f) hsource
  have hepin := SupportedHaarEqv.of_padded
    (PaddedPolynomialCoeffEqv.of_prefix (placed_pin P hroom hw ht e he))
    (P.embedding.polynomial_supported _) (placed_supported _ _ _)
  have hfpin := SupportedHaarEqv.of_padded
    (PaddedPolynomialCoeffEqv.of_prefix (placed_pin P hroom hw ht f hf))
    (P.embedding.polynomial_supported _) (placed_supported _ _ _)
  simpa only [P, sourcePlacement, Nat.zero_add, chartInsertion, centeredExpression] using
    hepin.symm.trans (htransport.trans hfpin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

/-- One source Haar certificate, not a family of regulator assumptions,
identifies the actual states in the existing completion. -/
theorem embedStage_eq_of_haar_source_identity (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H)
    (hp : SupportedHaarEqv ((H+1)*(N base))
      (sourcePolynomial (chart H x)) (sourcePolynomial (chart H y))) :
    embedStage hw0 hw1 hsmall hd hs (ofExpression base hb x) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb y) :=
  embedStage_eq_of_haar_diagonal hw0 hw1 hsmall hd hs hb H x y hx hy
    (fun n => chartInsertion_source_haar_congr n H n (chart H x) (chart H y)
      (chart_within H x hx) (chart_within H y hy) hp)

/-- Direct signed-window consumer of genuine source Haar identities. -/
theorem embedWindow_eq_of_haar_source_identity (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hp : SupportedHaarEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    embedStage hw0 hw1 hsmall hd hs (ofExpression base hb ⟨H, e, he⟩) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb ⟨H, f, hf⟩) := by
  apply embedStage_eq_of_haar_source_identity hw0 hw1 hsmall hd hs hb H
    ⟨H, e, he⟩ ⟨H, f, hf⟩ (Nat.le_refl _) (Nat.le_refl _)
  simpa only [chart, Nat.sub_self, shift_zero] using hp

open BF4WilsonBacktrackSourceIdentity in
/-- A concrete sphere-dependent Wilson identity reaches the EXISTING states:
forward and reverse traversal of the same physical link has character two. -/
theorem embed_backtrack_eq_constant :
    embedStage hw0 hw1 hsmall hd hs
      (ofExpression 1 (by decide) ⟨0, backtrack, backtrack_within⟩) =
    embedStage hw0 hw1 hsmall hd hs
      (ofExpression 1 (by decide) ⟨0, constant, constant_within⟩) := by
  apply embedWindow_eq_of_haar_source_identity hw0 hw1 hsmall hd hs (by decide)
    0 backtrack constant backtrack_within constant_within
  simpa only [Nat.zero_add, Nat.one_mul] using source_supported_haar

#print axioms placed_source_haar_congr
#print axioms chartInsertion_source_haar_congr
#print axioms embedStage_eq_of_haar_source_identity
#print axioms embedWindow_eq_of_haar_source_identity
#print axioms embed_backtrack_eq_constant

end YMGap.Continuum.BF4WilsonSpatialUnionHaarSourceIdentity
