/-
# Local Ward scores in the SAME original coordinates and action

Pull the constructed score back from its selected-link frame. It pairs to
zero with every supported polynomial independent of that link, even under
the complete interacting action. Its source links are just the selected
link, its incident faces, and the test's links. Consequently two actual
scores have zero cross moment when the second source excludes the first
selected link. This is exact conditional cancellation, not independence of
the full measure or spatial clustering of arbitrary observables.
-/

import YMGap.Continuum.BF4ExactSlabLocalWardScoreBound
import YMGap.Continuum.SU2QuaternionAngularLocality
import YMGap.Continuum.QuaternionHaarOrthogonalPairCost

namespace YMGap.Continuum.BF4ExactSlabOriginalWardLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalHaarWard
open YMGap.Continuum.BF4ExactSlabLocalWardVariance
open YMGap.Continuum.BF4ExactSlabLocalWardScoreBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionAngularLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularProductBounds
open YMGap.Continuum.QuaternionHaarAngularProductList
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarOrthogonalPairCost
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

variable (w : Q') (K extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "swap" => linkHeadSwap extent link hl
local notation "A" => reindexQuaternionPolynomial swap (incidentHeat w K extent link)
local notation "R" => reindexQuaternionPolynomial swap (complementHeat w K extent link)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- Test g is in the original coordinates; the resulting score is too. -/
def originalScore (i j : Nat) (g : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial swap
    (localScore w K extent link hl i j (reindexQuaternionPolynomial swap g))

theorem originalScore_supported (i j : Nat) (g : RatPoly) :
    SupportedQuaternionBlocks (blocks extent) (originalScore w K extent link hl i j g) :=
  reindex_supported swap _

/-- Exact pairing pin from the common original action to its selected-link frame. -/
theorem originalScore_pair_pin {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    quaternionHaar (blocks extent) (polyMul (polyMul f (originalScore w K extent link hl i j g)) W) ≈
    quaternionHaar (blocks extent) (polyMul R (polyMul A
      (polyMul (reindexQuaternionPolynomial swap f)
        (localScore w K extent link hl i j (reindexQuaternionPolynomial swap g))))) := by
  let S := localScore w K extent link hl i j (reindexQuaternionPolynomial swap g)
  have hS := localScore_supported w K extent link hl hi hj (reindex_supported swap g)
  have ht := carrierOfPrefix (reindex_supported swap (reindexQuaternionPolynomial swap S)) hS
    (reindex_twice_prefix swap S)
  have hp := fullAction_pair_pin w K extent link hl
    (polyMul f (originalScore w K extent link hl i j g))
    (supported_polyMul hf (originalScore_supported w K extent link hl i j g))
  rw [reindexQuaternionPolynomial_mul] at hp
  exact Q'.eqv_trans _ _ _ hp (haar_of_carrier
    (HaarCarrierEqv.mul_left R (HaarCarrierEqv.mul_left A
      (HaarCarrierEqv.mul_left (reindexQuaternionPolynomial swap f) ht))))

/-- No independent-law assumption: the full action cancels the score exactly
against a polynomial whose selected-link derivative is zero. -/
theorem originalScore_pair_zero {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f)
    (hd : HeadQuaternionIndependent (reindexQuaternionPolynomial swap f)) :
    quaternionHaar (blocks extent) (polyMul (polyMul f (originalScore w K extent link hl i j g)) W) ≈ 0 := by
  have hz := angularDerivative_independent_zero hi hj _ hd
  have he : RatPolyCoeffEqv
      (polyAdd
        (polyMul (reindexQuaternionPolynomial swap f)
          (localScore w K extent link hl i j (reindexQuaternionPolynomial swap g)))
        (polyMul (polyMul A (reindexQuaternionPolynomial swap g))
          (SU2QuaternionAngularDerivative.angularDerivative i j (reindexQuaternionPolynomial swap f))))
      (polyMul (reindexQuaternionPolynomial swap f)
        (localScore w K extent link hl i j (reindexQuaternionPolynomial swap g))) :=
    ((RatPolyCoeffEqv.refl _).add
      ((hz.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _))).trans (RatPolyCoeffEqv.add_zero _)
  exact Q'.eqv_trans _ _ _ (originalScore_pair_pin w K extent link hl hi hj g f hf)
    (Q'.eqv_trans _ _ _ (haar_of_coeff ((he.mul_left A).mul_left R).symm)
      (fullAction_score_identity w K extent link hl hi hj (reindexQuaternionPolynomial swap g)
        (reindexQuaternionPolynomial swap f)))

/-- A literal source-link exclusion supplies the derivative-zero premise. -/
theorem originalScore_pair_zero_of_local {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f)
    {links : List Z4Link} (hfLocal : LinkLocal extent links f) (hn : link ∉ links) :
    quaternionHaar (blocks extent) (polyMul (polyMul f (originalScore w K extent link hl i j g)) W) ≈ 0 := by
  have hb := List.idxOf_lt_length_of_mem hl
  exact originalScore_pair_zero w K extent link hl hi hj g f hf
    (blockDegree_reindex swap (Nat.lt_of_le_of_lt (Nat.zero_le _) hb)
      (headSwapBlockInvolution_map_zero _ _ hb) (linkLocal_degree_zero hfLocal link hl hn))

/-- Zero mean in the original coordinates under the complete action. -/
theorem originalScore_mean_zero {i j : Nat} (hi : i < 4) (hj : j < 4) (g : RatPoly) :
    quaternionHaar (blocks extent) (polyMul (originalScore w K extent link hl i j g) W) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff ((RatPolyCoeffEqv.one_mul _).mul_right W)))
    (originalScore_pair_zero_of_local w K extent link hl hi hj g polyOne (supported_one _)
      (BlockLocal.one _ (fun b => correctedSlabLinkAt extent b ∈ ([] : List Z4Link)))
      (fun h => List.not_mem_nil h))

/-- The original score's finite source, including its test; no exterior action. -/
def sourceLinks (extent : Nat) (link : Z4Link) (testLinks : List Z4Link) : List Z4Link :=
  link :: (faceLinks extent (incidentIds extent link) ++ testLinks)

/-- Differentiation adds no source beyond the selected link. Pulling back
uses the SAME involution, so the original finite link support is recovered. -/
theorem originalScore_local {i j : Nat} (hi : i < 4) (hj : j < 4)
    {g : RatPoly} {testLinks : List Z4Link} (hg : LinkLocal extent testLinks g) :
    LinkLocal extent (sourceLinks extent link testLinks) (originalScore w K extent link hl i j g) := by
  let allowed := fun b => correctedSlabLinkAt extent b ∈ sourceLinks extent link testLinks
  have hA : BlockLocal (blocks extent) allowed (incidentHeat w K extent link) :=
    (heatProduct_local w K extent (incidentIds extent link)).mono
      (fun _ h => List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have hg' : BlockLocal (blocks extent) allowed g := hg.mono
    (fun _ h => List.mem_cons_of_mem _ (List.mem_append_right _ h))
  let pulled := fun b => allowed ((swap).map b)
  have hAr : BlockLocal (blocks extent) pulled A := hA.reindex swap (fun _ _ h => h)
  have hgr : BlockLocal (blocks extent) pulled (reindexQuaternionPolynomial swap g) :=
    hg'.reindex swap (fun _ _ h => h)
  have hhead : pulled 0 := by
    change correctedSlabLinkAt extent ((swap).map 0) ∈ sourceLinks extent link testLinks
    rw [show (swap).map 0 = (boundaryCompleteSlabLinks extent).idxOf link from
      headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl), correctedSlabLinkAt_idxOf hl]
    exact List.mem_cons_self
  have hscore := (hAr.mul (angularDerivative_local hgr hhead hi hj)).add
    (((angularDerivative_local hAr hhead hi hj).mul hgr).smul 2)
  apply hscore.reindex swap
  intro b hb ha
  change allowed b
  change allowed ((swap).map ((swap).map b)) at ha
  rw [(swap).involutive b hb] at ha
  exact ha

/-- Two literal original scores have zero cross moment when the second
score's local source excludes the first selected link. This is a statement
under the full interacting action, not the star-deleted reference. -/
theorem separated_scores_pair_zero {i j k l : Nat} (hi : i < 4) (hj : j < 4)
    (hk : k < 4) (hll : l < 4) (g : RatPoly)
    (other : Z4Link) (ho : other ∈ boundaryCompleteSlabLinks extent)
    {h : RatPoly} {testLinks : List Z4Link} (hh : LinkLocal extent testLinks h)
    (hsep : link ∉ sourceLinks extent other testLinks) :
    quaternionHaar (blocks extent)
      (polyMul (polyMul (originalScore w K extent other ho k l h)
        (originalScore w K extent link hl i j g)) W) ≈ 0 :=
  originalScore_pair_zero_of_local w K extent link hl hi hj g _
    (originalScore_supported w K extent other ho k l h)
    (originalScore_local w K extent other ho hk hll hh) hsep

/-- The original score inherits the proved interval without changing the action.
Uniformity requires the supplied original-frame test caps G,DG to be uniform. -/
def originalScoreInterval (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {i j : Nat} (hi : i < 4) (hj : j < 4) {g : RatPoly} {G DG : Q'}
    (P : AngularBound (blocks extent) i j (reindexQuaternionPolynomial swap g) G DG) :
    Interval (blocks extent) (originalScore w K extent link hl i j g) (wardScoreCap w G DG) :=
  intervalReindex swap (localScoreInterval w K extent link hl hw0 hw1 hi hj P)

include link hl in
/-- The partition for all original-coordinate scores is the same original one. -/
theorem originalPartition_positive (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) : (0 : Q') < quaternionHaar (blocks extent) W :=
  Q'.pos_of_lt_of_le (framePartition_positive w K extent link hl hw0 hw1 hK)
    (Q'.ge_of_eqv (framePartition_pin w K extent link hl))

/-- Exact noninteracting-score cancellation removes the generic factor two.
Both diagonal costs and the sum use the SAME complete original action and
normalizer. This is a two-score input for spatial aggregation, not a bound
for a general interacting score family or its response. -/
theorem separated_scores_cost_le (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j k l : Nat} (hi : i < 4) (hj : j < 4)
    (hk : k < 4) (hll : l < 4) {g h : RatPoly}
    (other : Z4Link) (ho : other ∈ boundaryCompleteSlabLinks extent)
    {testLinks : List Z4Link} (hh : LinkLocal extent testLinks h)
    (hsep : link ∉ sourceLinks extent other testLinks) {G DG H DH : Q'}
    (P : AngularBound (blocks extent) i j (reindexQuaternionPolynomial swap g) G DG)
    (Q : AngularBound (blocks extent) k l
      (reindexQuaternionPolynomial (linkHeadSwap extent other ho) h) H DH) :
    let total := polyAdd (originalScore w K extent other ho k l h) (originalScore w K extent link hl i j g)
    normalizedMoment (blocks extent) W (polyMul total total)
      (originalPartition_positive w K extent link hl hw0 hw1 hK) ≤
      wardScoreCap w H DH * wardScoreCap w H DH + wardScoreCap w G DG * wardScoreCap w G DG :=
  normalized_square_add_le
    (originalScoreInterval w K extent other ho hw0 hw1 hk hll Q)
    (originalScoreInterval w K extent link hl hw0 hw1 hi hj P)
    (headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ hid => hid))
    (originalPartition_positive w K extent link hl hw0 hw1 hK)
    (separated_scores_pair_zero w K extent link hl hi hj hk hll g other ho hh hsep)

end YMGap.Continuum.BF4ExactSlabOriginalWardLocality

#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalScore_supported
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalScore_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalScore_pair_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalScore_pair_zero_of_local
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalScore_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalScore_local
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.separated_scores_pair_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalScoreInterval
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.originalPartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabOriginalWardLocality.separated_scores_cost_le
