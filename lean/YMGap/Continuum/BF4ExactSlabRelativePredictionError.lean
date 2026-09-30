/-
# Original-action plaquette prediction floor from relative Ward control

The full supplied physical action is retained. A predictor may depend on
every link except the first edge of the actual plaquette. The floor uses
only the six-face relative derivative budget, not a global density minimum.
Nome dependence and the required late cutoff are explicit.
-/

import YMGap.Continuum.BF4ExactSlabSelectedActionRelativeBound
import YMGap.Continuum.BF4ExactSlabSelectedPlaquetteDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
import YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError
import YMGap.Continuum.QuaternionHaarRelativePredictionFloor

namespace YMGap.Continuum.BF4ExactSlabRelativePredictionError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError
open YMGap.Continuum.BF4ExactSlabSelectedActionRelativeBound
open YMGap.Continuum.BF4ExactSlabSelectedPlaquetteDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativePredictionFloor
open YMGap.Continuum.RationalRelativeWardPrediction
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

def selectedScoreCap (w : Q') : Q' := 6 * relativeCap w 2048
def relativePredictionFloor (w : Q') : Q' := predictionFloor (selectedScoreCap w)

theorem relativePredictionFloor_positive (w : Q') :
    (0 : Q') < relativePredictionFloor w := predictionFloor_positive _

private theorem smul_neg (q : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) q) (polyNeg q) :=
  (cap_mul_left (-1) q).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => q))

attribute [local irreducible] correctedSlabPlaquettePolynomial

/-- A division-free estimate on the original joint action. The predictor
is only excluded from the first edge of this literal physical plaquette. -/
theorem raw_prediction_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : relativeCutoff w 2048 ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (B extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : faceLinkA face ∉ links) :
    quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) ≤
      predictionFactor (selectedScoreCap w) * quaternionHaar (B extent)
        (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
          (polyMul (polynomialError extent face q) (polynomialError extent face q))) := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let link := faceLinkA face
  have hedge : link ∈ edgesOf face := List.mem_cons_self
  have hl : link ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hedge⟩
  let s := linkHeadSwap extent link hl
  let W := reindexQuaternionPolynomial s A
  let f := reindexQuaternionPolynomial s (faceCharacter extent face)
  let q' := reindexQuaternionPolynomial s q
  have hB : (B extent - 1)+1 = B extent := by
    have := List.idxOf_lt_length_of_mem hl
    omega
  have hC : (0 : Q') < selectedScoreCap w :=
    Q'.mul_pos (by decide) (relativeCap_positive hw0 (by decide))
  have R : ∀ i j, i < 4 → j < 4 → RelativeBound (B extent) i j W (selectedScoreCap w) :=
    fun _ _ hi hj => selectedActionRelativeBound hw0 hw1 K extent hK ids hids hnodup link hl hi hj
  have hlinear := faceCharacter_head_degree_one hf hedge
  have hkin := fullSlabFaceCharacter_head_angularSquare hf
  have hzero := linkLocal_head_degree_zero hlocal link hl hfree
  have hb := raw_prediction_floor (tail := B extent - 1) (W := W) (f := f) hC
    (by rw [hB]; exact R)
    (by rw [hB]; exact reindex_supported s (faceCharacter extent face))
    hlinear (by rw [hB]; exact hkin) q'
    (by rw [hB]; exact reindex_supported s q) hzero
  have hz : quaternionHaar (B extent) W ≈ quaternionHaar (B extent) A :=
    quaternionHaar_reindex s A (heatProduct_supported w K extent ids)
  let err := polynomialError extent face q
  have herr : RatPolyCoeffEqv (polyAdd f (polySmul (-1) q'))
      (reindexQuaternionPolynomial s err) := by
    change RatPolyCoeffEqv _ (reindexQuaternionPolynomial s
      (polyAdd (faceCharacter extent face) (polyNeg q)))
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
    exact (RatPolyCoeffEqv.refl f).add (smul_neg q')
  have he : quaternionHaar (B extent)
      (polyMul W (polyMul (polyAdd f (polySmul (-1) q')) (polyAdd f (polySmul (-1) q')))) ≈
      quaternionHaar (B extent) (polyMul A (polyMul err err)) := by
    have hp := haar_of_coeff (blocks := B extent) ((herr.mul herr).mul_left W)
    change quaternionHaar (B extent) _ ≈ quaternionHaar (B extent)
      (polyMul (reindexQuaternionPolynomial s A)
        (polyMul (reindexQuaternionPolynomial s err) (reindexQuaternionPolynomial s err))) at hp
    rw [← reindexQuaternionPolynomial_mul, ← reindexQuaternionPolynomial_mul] at hp
    exact Q'.eqv_trans _ _ _ hp (quaternionHaar_reindex s _
      (supported_polyMul (heatProduct_supported w K extent ids)
        (supported_polyMul (polynomialError_supported extent face hq)
          (polynomialError_supported extent face hq))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hz)
    (Q'.le_trans' _ _ _ (by simpa only [hB] using hb)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he)))

/-- The positive explicit floor in the existing SAME-partition finiteValue.
It is independent of extent and selected-face count at each fixed nome,
for every cutoff meeting the displayed relative-cutoff condition. -/
theorem finite_prediction_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (stage : Nat) (hK : relativeCutoff w 2048 ≤ headCutoff w+stage)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (B extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : faceLinkA face ∉ links) :
    relativePredictionFloor w ≤ finiteValue w hw0 hw1 extent ids hids
      (polyMul (polynomialError extent face q) (polynomialError extent face q)) stage := by
  let A := polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids
  let err := polynomialError extent face q
  have hz : (0 : Q') < quaternionHaar (B extent) A :=
    Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partitionSample_floor w hw0 hw1 extent ids hids stage)
  have h := normalized_prediction_bound (selectedScoreCap w) _ _ hz
    (raw_prediction_bound hw0 hw1 (headCutoff w+stage) extent hK ids hids hnodup
      hf q hq links hlocal hfree)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm A (polyMul err err)))))

#print axioms relativePredictionFloor_positive
#print axioms raw_prediction_bound
#print axioms finite_prediction_floor

end YMGap.Continuum.BF4ExactSlabRelativePredictionError
