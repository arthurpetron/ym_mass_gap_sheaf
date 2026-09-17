/-
# Source identities reach the SAME Wilson states through actual placements

A single padded coefficient identity on the chronological source carrier
is transported to every original centered chart. First place the source at
time zero in extent base+H; then apply the literal spatial/time translation
to the actual chart. The original expression pins identify both endpoints.
All source support, spatial fringe and time-room guards are proved.

The existing observable-descent theorem then gives literal equality in the
existing Wilson union completion. No regulator-indexed equality is assumed
at this final interface, and no source-recentering algebra is postulated.
This concerns free-polynomial coefficient identities, not every relation
valid only on the quaternion sphere, arbitrary OS-null multiplication,
full observable coverage, canonical OS/QFT or a continuum mass gap.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingCongruence

namespace YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity

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
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding (Placement)
open YMGap.Continuum.BF4WilsonSpatialUnion (ofExpression)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm (embedStage)
open YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent (embedStage_eq_of_padded_diagonal)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local notation:max "N" base:arg => List.length (baseLinks base)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- One source identity, with its actual inclusive chronological support,
survives the existing placement at any allowed ambient extent and start. -/
theorem placed_source_congr {base start H extent : Nat}
    (hw : base ≤ extent) (ht : start+H ≤ extent)
    (e f : WindowExpression base) (he : Within H e) (hf : Within H f)
    (hp : PaddedPolynomialCoeffEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    PaddedPolynomialCoeffEqv (B extent)
      (placedPolynomial extent start e) (placedPolynomial extent start f) :=
  (expression_pin hw ht e he).symm.trans
    (((BF4ExactSlabFixedSpatialChainCarrier.embedding H hw ht).polynomial_padded_congr
      (source_supported H e he) (source_supported H f hf) hp).trans
      (expression_pin hw ht f hf))

/-- The complete auxiliary slab is only an observable coordinate carrier;
no equality of its action with the target action is asserted or needed. -/
def sourcePlacement (base r H t : Nat) : Placement where
  source := base+H
  target := chartExtent base r H t
  space := r+1
  time := paddedWidth base r+1+t
  space_room := by unfold chartExtent adjacentEvenExtent centralExtent paddedWidth; omega
  time_room := by unfold chartExtent adjacentEvenExtent centralExtent paddedWidth; omega

/-- No new source-recentering theorem: chronological placement followed by
literal slab translation gives the actual centered lower observable. -/
theorem chartInsertion_source_congr {base : Nat} (r H t : Nat)
    (e f : WindowExpression base) (he : Within H e) (hf : Within H f)
    (hp : PaddedPolynomialCoeffEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    PaddedPolynomialCoeffEqv (B (chartExtent base r H t))
      (chartInsertion r H t e) (chartInsertion r H t f) := by
  let P := sourcePlacement base r H t
  have hw : base ≤ P.source := Nat.le_add_right _ _
  have ht : 0+H ≤ P.source := by dsimp [P, sourcePlacement]; omega
  have hroom : base+P.space ≤ paddedWidth base r := by
    dsimp [P, sourcePlacement, paddedWidth]; omega
  have hsource := placed_source_congr hw ht e f he hf hp
  have htransport := P.embedding.polynomial_padded_congr
    (placed_supported P.source 0 e) (placed_supported P.source 0 f) hsource
  have hepin := PaddedPolynomialCoeffEqv.of_prefix (placed_pin P hroom hw ht e he)
  have hfpin := PaddedPolynomialCoeffEqv.of_prefix (placed_pin P hroom hw ht f hf)
  simpa only [P, sourcePlacement, Nat.zero_add, chartInsertion, centeredExpression] using
    hepin.symm.trans (htransport.trans hfpin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

/-- One finite source identity supplies ALL diagonal premises of the already
proved same-state theorem. No new completion or equivalence is introduced. -/
theorem embedStage_eq_of_source_identity (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H)
    (hp : PaddedPolynomialCoeffEqv ((H+1)*(N base))
      (sourcePolynomial (chart H x)) (sourcePolynomial (chart H y))) :
    embedStage hw0 hw1 hsmall hd hs (ofExpression base hb x) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb y) :=
  embedStage_eq_of_padded_diagonal hw0 hw1 hsmall hd hs hb H x y hx hy
    (fun n => chartInsertion_source_congr n H n (chart H x) (chart H y)
      (chart_within H x hx) (chart_within H y hy) hp)

/-- Direct signed-window interface for existing source-polynomial certificates. -/
theorem embedWindow_eq_of_source_identity (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hp : PaddedPolynomialCoeffEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    embedStage hw0 hw1 hsmall hd hs (ofExpression base hb ⟨H, e, he⟩) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb ⟨H, f, hf⟩) := by
  apply embedStage_eq_of_source_identity hw0 hw1 hsmall hd hs hb H
    ⟨H, e, he⟩ ⟨H, f, hf⟩ (Nat.le_refl _) (Nat.le_refl _)
  simpa only [chart, Nat.sub_self, shift_zero] using hp

#print axioms placed_source_congr
#print axioms sourcePlacement
#print axioms chartInsertion_source_congr
#print axioms embedStage_eq_of_source_identity
#print axioms embedWindow_eq_of_source_identity

end YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity
