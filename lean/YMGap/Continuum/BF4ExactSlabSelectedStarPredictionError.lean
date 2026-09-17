/-
# Polynomial prediction error for an original plaquette character

The predictor may be any supported polynomial localized away from one
selected link of the actual plaquette. Erasing only the incident selected
heat factors makes its cross moment vanish and leaves the character's
second moment equal to one, against the entire retained action product.
Restoring the at-most-six original factors gives the existing starRatio
floor for the prediction error, with the SAME selected partition.

The predictor is not assumed constant or independent of other links. No
mixing, completed-operator, uniform-in-nome or continuum conclusion follows.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarVariance
import YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure

namespace YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure (jump_eq_diagonal)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] correctedSlabPlaquettePolynomial

def polynomialError (extent : Nat) (face : Z4Plaq) (q : RatPoly) : RatPoly :=
  polyAdd (faceCharacter extent face) (polyNeg q)

theorem polynomialError_supported (extent : Nat) (face : Z4Plaq) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (B extent) q) :
    SupportedQuaternionBlocks (B extent) (polynomialError extent face q) := by
  apply supported_add (faceCharacter_supported extent face)
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hq s hs

private theorem rest_mem {extent : Nat} {ids : List Nat} {link : Z4Link} {id : Nat}
    (hi : id ∈ selectedRest extent ids link) :
    id ∈ ids ∧ link ∉ edgesOf (slabPlaquetteAt extent id) := by
  simpa only [selectedRest, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] using hi

private theorem rest_misses (extent : Nat) (ids : List Nat) (link : Z4Link) :
    link ∉ faceLinks extent (selectedRest extent ids link) := by
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  exact (rest_mem hi).2 he

private theorem rest_character_zero (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (spin : Nat) (hs : 0 < spin) :
    quaternionHaar (B extent)
      (polyMul (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
        (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link))) ≈ 0 :=
  original_character_local_zero hf link hl spin hs _
    (faceLinks extent (selectedRest extent ids link))
    (heatProduct_supported w K extent _) (heatProduct_local w K extent _)
    (rest_misses extent ids link)

/-- Every factor of the retained action remains beside the arbitrary predictor. -/
theorem retained_cross_zero (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (B extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) :
    quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link))
        (polyMul (faceCharacter extent face) q)) ≈ 0 := by
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  let allowed := faceLinks extent (selectedRest extent ids link) ++ links
  have hr : LinkLocal extent allowed R := (heatProduct_local w K extent _).mono
    (fun _ hi => List.mem_append.mpr (Or.inl hi))
  have hq' : LinkLocal extent allowed q := hlocal.mono
    (fun _ hi => List.mem_append.mpr (Or.inr hi))
  have hnone : link ∉ allowed := fun hi =>
    (List.mem_append.mp hi).elim (rest_misses extent ids link) hfree
  have hz := original_character_local_zero hf link hl 1 (by decide) (polyMul R q) allowed
    (supported_polyMul (heatProduct_supported w K extent _) hq) (BlockLocal.mul hr hq') hnone
  exact Q'.eqv_trans _ _ _ (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => R | 1 => faceCharacter extent face | _ => q))) hz

private theorem first_character_square (p : RatPoly) :
    RatPolyCoeffEqv (polyMul (characterPolynomial p 1) (characterPolynomial p 1))
      (polyAdd (characterPolynomial p 2) polyOne) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p 1)
  let b := characterPolynomial p 0
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (RatPolyCoeffEqv.refl b))

private theorem retained_square_moment (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) :
    quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link))
        (polyMul (faceCharacter extent face) (faceCharacter extent face))) ≈
      quaternionHaar (B extent)
        (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)) := by
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  let chi2 := characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar 2
  have hsplit : RatPolyCoeffEqv
      (polyMul R (polyMul (faceCharacter extent face) (faceCharacter extent face)))
      (polyAdd (polyMul chi2 R) (polyMul polyOne R)) :=
    ((first_character_square (correctedSlabPlaquettePolynomial extent face).scalar).mul_left R).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 2) (.add (.var 0) (.var 1)))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => chi2 | 1 => polyOne | _ => R))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hsplit)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (rest_character_zero w K extent ids hf link hl 2 (by decide))
          (haar_of_coeff (RatPolyCoeffEqv.one_mul R)))
        (Q'.eqv_of_eq (Q'.zero_add' _))))

/-- Exact erased-background error, including the predictor's full squared cost. -/
theorem retained_error_identity (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (B extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) :
    let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
    quaternionHaar (B extent)
        (polyMul R (polyMul (polynomialError extent face q) (polynomialError extent face q))) ≈
      quaternionHaar (B extent) R + quaternionHaar (B extent) (polyMul R (polyMul q q)) := by
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  have hz := retained_cross_zero w K extent ids hf link hl q hq links hlocal hfree
  have he := jump_eq_diagonal R (faceCharacter extent face) q hz
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right R _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (retained_square_moment w K extent ids hf link hl) (Q'.eqv_refl _))))

/-- No polynomial independent of the selected plaquette link predicts its
fundamental character with squared error below the original starRatio floor. -/
theorem polynomial_square_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (B extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) :
    starRatio w * quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) ≤
      quaternionHaar (B extent)
        (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
          (polyMul (polynomialError extent face q) (polynomialError extent face q))) := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  let s := polyMul (polynomialError extent face q) (polynomialError extent face q)
  let PR := headProduct_certificate hw0 hw1 K extent hK (selectedRest extent ids link)
    (fun id hi => hids id (rest_mem hi).1)
  have htest := retained_error_identity w K extent ids hf link hl q hq links hlocal hfree
  have hrest : quaternionHaar (B extent) R ≤ quaternionHaar (B extent) (polyMul s R) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (PR.mul (Certificate.square q hq)).haar_nonnegative)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv htest)
        (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm R s))))
  have hlo : lowerFactor w * quaternionHaar (B extent) R ≤
      quaternionHaar (B extent) (polyMul A s) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hrest (Q'.le_of_lt (lowerFactor_positive hw0 hw1)))
      (Q'.le_trans' _ _ _
        (selected_star_bounds hw0 hw1 K extent hK ids hids hnodup link
          (Certificate.square (polynomialError extent face q) (polynomialError_supported extent face hq))).1
        (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))
  have hhi : quaternionHaar (B extent) A ≤ upperFactor w * quaternionHaar (B extent) R :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.one_mul A)))
      (Q'.le_trans' _ _ _
        (selected_star_bounds hw0 hw1 K extent hK ids hids hnodup link (Certificate.one (B extent))).2
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul R)))))
  have hcancel : starRatio w * (upperFactor w * quaternionHaar (B extent) R) ≈
      lowerFactor w * quaternionHaar (B extent) R :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _
        (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (upperFactor_positive hw0))))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hhi (Q'.le_of_lt (starRatio_positive hw0 hw1)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcancel) hlo)

end YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError

#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError.polynomialError
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError.polynomialError_supported
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError.retained_cross_zero
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError.retained_error_identity
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError.polynomial_square_floor
