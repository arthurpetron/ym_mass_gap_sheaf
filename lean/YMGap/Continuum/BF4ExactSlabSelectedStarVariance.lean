/-
# A local variance floor for the original selected-face action

Only the heat factors incident to one actual plaquette link are compared.
A physical list without repetitions has at most six such factors. Every
other factor remains in the Haar integral, including all interactions
through the other links. Positive-spin cancellation against this actual
link-independent background gives the fundamental character's first and
second moments exactly. Testing at the original interacting mean yields
a positive variance floor depending only on the nome.

The floor is the existing starRatio, uniformly in extent, selected-face
count and every cutoff above headCutoff. The final statement uses the
existing finiteValue and its SAME partition. This is a local variance
bound, not a spatial mixing estimate, an OS gap, or a spacing-uniform floor.
-/

import YMGap.Continuum.BF4ExactSlabLocalStarComparison
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.BF4ExactSlabSelectedStarVariance

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
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (original_character_support)
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit (heatProductHaar)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment normalizedVariance)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The selected incident factors, each retained with its original multiplicity. -/
def selectedStar (extent : Nat) (ids : List Nat) (link : Z4Link) : List Nat :=
  ids.filter (fun id => decide (link ∈ edgesOf (slabPlaquetteAt extent id)))

/-- Every selected factor not containing the integrated link. -/
def selectedRest (extent : Nat) (ids : List Nat) (link : Z4Link) : List Nat :=
  ids.filter (fun id => !(decide (link ∈ edgesOf (slabPlaquetteAt extent id))))

private theorem star_mem {extent : Nat} {ids : List Nat} {link : Z4Link} {id : Nat}
    (hi : id ∈ selectedStar extent ids link) :
    id ∈ ids ∧ link ∈ edgesOf (slabPlaquetteAt extent id) := by
  simpa only [selectedStar, List.mem_filter, decide_eq_true_eq] using hi

private theorem rest_mem {extent : Nat} {ids : List Nat} {link : Z4Link} {id : Nat}
    (hi : id ∈ selectedRest extent ids link) :
    id ∈ ids ∧ link ∉ edgesOf (slabPlaquetteAt extent id) := by
  simpa only [selectedRest, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] using hi

/-- The six-face bound uses the actual no-repetition hypothesis. -/
theorem selectedStar_length_le_six (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (link : Z4Link) :
    (selectedStar extent ids link).length ≤ 6 := by
  have hn : (selectedStar extent ids link).Nodup := List.filter_sublist.nodup hnodup
  have h := CayleyPruferInjection.nodup_subset_length_le
    (selectedStar extent ids link) (incidentIds extent link) hn (by
      intro id hi
      exact (mem_incidentIds_iff extent link id).mpr
        ⟨hids id (star_mem hi).1, (star_mem hi).2⟩)
  exact Nat.le_trans h (incidentIds_length_le_six extent link)

/-- A literal action partition: no spectator is dropped and no face is repeated. -/
theorem selected_heat_partition (w : Q') (K extent : Nat) (ids : List Nat) (link : Z4Link) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polyMul
        (polynomialProduct (faceHeatPolynomial w K extent) (selectedStar extent ids link))
        (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link))) :=
  (polynomialProduct_perm _ (List.filter_append_perm _ _).symm).trans
    (polynomialProduct_append _ _ _)

/-- The original fundamental character of an arbitrary physical ambient face. -/
def faceCharacter (extent : Nat) (face : Z4Plaq) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar 1

theorem faceCharacter_supported (extent : Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (B extent) (faceCharacter extent face) :=
  original_character_support extent face 1

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem first_character_square (p : RatPoly) :
    RatPolyCoeffEqv (polyMul (characterPolynomial p 1) (characterPolynomial p 1))
      (polyAdd (characterPolynomial p 2) polyOne) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p 1)
  let b := characterPolynomial p 0
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (RatPolyCoeffEqv.refl b))

private theorem rest_character_zero (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (spin : Nat) (hs : 0 < spin) :
    quaternionHaar (B extent)
      (polyMul (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
        (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link))) ≈ 0 := by
  apply original_character_local_zero hf link hl spin hs _
    (faceLinks extent (selectedRest extent ids link))
    (heatProduct_supported w K extent _) (heatProduct_local w K extent _)
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  exact (rest_mem hi).2 he

private theorem rest_square_moment (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) :
    quaternionHaar (B extent)
      (polyMul (polyMul (faceCharacter extent face) (faceCharacter extent face))
        (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link))) ≈
      quaternionHaar (B extent)
        (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)) := by
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  let chi2 := characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar 2
  have hsplit : RatPolyCoeffEqv
      (polyMul (polyMul (faceCharacter extent face) (faceCharacter extent face)) R)
      (polyAdd (polyMul chi2 R) (polyMul polyOne R)) :=
    ((first_character_square (correctedSlabPlaquettePolynomial extent face).scalar).mul_right R).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => chi2 | 1 => polyOne | _ => R))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hsplit)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (rest_character_zero w K extent ids hf link hl 2 (by decide))
          (haar_of_coeff (RatPolyCoeffEqv.one_mul R)))
        (Q'.eqv_of_eq (Q'.zero_add' _))))

/-- A rational shift of the actual character, still an original supported polynomial. -/
def shiftedCharacter (extent : Nat) (face : Z4Plaq) (c : Q') : RatPoly :=
  polyAdd (polySmul 1 (faceCharacter extent face)) (polySmul (-c) polyOne)

private theorem supported_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem shifted_supported (extent : Nat) (face : Z4Plaq) (c : Q') :
    SupportedQuaternionBlocks (B extent) (shiftedCharacter extent face c) :=
  supported_add (supported_smul (faceCharacter_supported extent face) 1)
    (supported_smul (supported_one (B extent)) (-c))

-- Subsequent scalar algebra uses the character as a supported polynomial;
-- it must not unfold the ambient plaquette-word implementation during unification.
attribute [local irreducible] correctedSlabPlaquettePolynomial

set_option maxHeartbeats 2000000 in
private theorem shifted_square_pin {extent : Nat} {W : RatPoly}
    (P : Certificate (B extent) W) (face : Z4Plaq) (c : Q') :
    quaternionHaar (B extent)
        (polyMul W (polyMul (shiftedCharacter extent face c) (shiftedCharacter extent face c))) ≈
      quaternionHaar (B extent) (polyMul W (polyMul (faceCharacter extent face) (faceCharacter extent face))) +
        -(2*c*quaternionHaar (B extent) (polyMul W (faceCharacter extent face))) +
        c*c*quaternionHaar (B extent) W := by
  let p := faceCharacter extent face
  let G := weightedGNSData (B extent) W P
  have h := G.diag_expand 1 (-c) ⟨p,faceCharacter_supported extent face⟩
    ⟨polyOne,supported_one (B extent)⟩
  have hb : weightedPair (B extent) W p p ≈ quaternionHaar (B extent) (polyMul W (polyMul p p)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have ha : weightedPair (B extent) W p polyOne ≈ quaternionHaar (B extent) (polyMul W p) :=
    haar_of_coeff (((RatPolyCoeffEqv.mul_one p).mul_right W).trans (RatPolyCoeffEqv.mul_comm _ _))
  have hz : weightedPair (B extent) W polyOne polyOne ≈ quaternionHaar (B extent) W :=
    haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right W).trans (RatPolyCoeffEqv.one_mul W))
  have ht := Q'.eqv_trans _ _ _ h (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl 1) hb))
      (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl (-c)) ha)))
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl 1) ha))
      (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl (-c)) hz))))
  have hs : quaternionHaar (B extent)
      (polyMul W (polyMul (shiftedCharacter extent face c) (shiftedCharacter extent face c))) ≈
      weightedPair (B extent) W (shiftedCharacter extent face c) (shiftedCharacter extent face c) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  exact Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _ ht
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
        (.mul (.const 1) (.mul (.neg (.var 3)) (.var 1))))
        (.add (.mul (.neg (.var 3)) (.mul (.const 1) (.var 1)))
          (.mul (.neg (.var 3)) (.mul (.neg (.var 3)) (.var 2)))))
      (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 3)) (.var 1))))
        (.mul (.mul (.var 3) (.var 3)) (.var 2))) (by decide)
      (fun | 0 => quaternionHaar (B extent) (polyMul W (polyMul p p))
           | 1 => quaternionHaar (B extent) (polyMul W p)
           | 2 => quaternionHaar (B extent) W
           | _ => c)))

/-- The local comparison keeps the entire selected spectator product. -/
theorem selected_star_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (link : Z4Link) {p : RatPoly} (P : Certificate (B extent) p) :
    let A := polynomialProduct (faceHeatPolynomial w K extent) ids
    let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
    lowerFactor w * quaternionHaar (B extent) (polyMul p R) ≤
        quaternionHaar (B extent) (polyMul p A) ∧
      quaternionHaar (B extent) (polyMul p A) ≤
        upperFactor w * quaternionHaar (B extent) (polyMul p R) := by
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  let S := polynomialProduct (faceHeatPolynomial w K extent) (selectedStar extent ids link)
  have h := atMostSix_bounds hw0 hw1 K extent hK
    (P.mul (headProduct_certificate hw0 hw1 K extent hK (selectedRest extent ids link)
      (fun id hi => hids id (rest_mem hi).1)))
    (selectedStar extent ids link) (fun id hi => hids id (star_mem hi).1)
    (selectedStar_length_le_six extent ids hids hnodup link)
  have he : quaternionHaar (B extent)
      (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids)) ≈
      quaternionHaar (B extent) (polyMul (polyMul p R) S) :=
    haar_of_coeff (((RatPolyCoeffEqv.refl p).mul (selected_heat_partition w K extent ids link)).trans
      (((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm _ _)).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _).symm))
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) h.2⟩

/-- The actual selected partition is positive at the same late cutoff. -/
theorem selectedMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    (0 : Q') < quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) :=
  Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partition_floor hw0 hw1 extent ids hids K hK)

/-- Every rational center has original squared cost at least starRatio
times the SAME partition. No spectator mass or signed numerator is inverted. -/
theorem shifted_square_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (c : Q') :
    starRatio w * quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) ≤
      quaternionHaar (B extent)
        (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
          (polyMul (shiftedCharacter extent face c) (shiftedCharacter extent face c))) := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  let p := faceCharacter extent face
  let s := polyMul (shiftedCharacter extent face c) (shiftedCharacter extent face c)
  let PR := headProduct_certificate hw0 hw1 K extent hK (selectedRest extent ids link)
    (fun id hi => hids id (rest_mem hi).1)
  have hmean : quaternionHaar (B extent) (polyMul R p) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (rest_character_zero w K extent ids hf link hl 1 (by decide))
  have hsquare : quaternionHaar (B extent) (polyMul R (polyMul p p)) ≈ quaternionHaar (B extent) R :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (rest_square_moment w K extent ids hf link hl)
  have htest : quaternionHaar (B extent) (polyMul s R) ≈
      quaternionHaar (B extent) R + c*c*quaternionHaar (B extent) R :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (shifted_square_pin PR face c)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr' hsquare
              (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (2*c) _ _ hmean)))
            (Q'.eqv_refl _))
          (poly_identity_of_normal_eq
            (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 1)) (.const 0))))
              (.mul (.mul (.var 1) (.var 1)) (.var 0)))
            (.add (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 0)))
            (by decide) (fun | 0 => quaternionHaar (B extent) R | _ => c))))
  have hrest : quaternionHaar (B extent) R ≤ quaternionHaar (B extent) (polyMul s R) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg c) PR.haar_nonnegative))
      (Q'.ge_of_eqv htest)
  have hlo : lowerFactor w * quaternionHaar (B extent) R ≤
      quaternionHaar (B extent) (polyMul A s) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hrest (Q'.le_of_lt (lowerFactor_positive hw0 hw1)))
      (Q'.le_trans' _ _ _
        (selected_star_bounds hw0 hw1 K extent hK ids hids hnodup link
          (Certificate.square (shiftedCharacter extent face c) (shifted_supported extent face c))).1
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

/-- Normalization uses the actual selected-action mean and actual partition.
The explicit positive lower bound is independent of volume and cutoff. -/
theorem normalizedVariance_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) :
    starRatio w ≤ normalizedVariance (B extent)
      (polynomialProduct (faceHeatPolynomial w K extent) ids) (faceCharacter extent face)
      (selectedMass_positive hw0 hw1 K extent hK ids hids) := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let p := faceCharacter extent face
  let z := quaternionHaar (B extent) A
  let a := quaternionHaar (B extent) (polyMul A p)
  let b := quaternionHaar (B extent) (polyMul A (polyMul p p))
  let hz := selectedMass_positive hw0 hw1 K extent hK ids hids
  let r := Q'.recipPos z hz
  have he : (starRatio w*z)*r ≈ starRatio w :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z hz))
        (Q'.mul_one_eqv _))
  have hraw := shifted_square_floor hw0 hw1 K extent hK ids hids hnodup hf link hl (a*r)
  have hpin : quaternionHaar (B extent)
      (polyMul A (polyMul (shiftedCharacter extent face (a*r)) (shiftedCharacter extent face (a*r)))) * r ≈
      normalizedVariance (B extent) A p hz :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ r
        (shifted_square_pin (headProduct_certificate hw0 hw1 K extent hK ids hids) face (a*r)))
      (RationalVarianceComparison.quadratic_minimizer z a b r (Q'.mul_recipPos_eqv z hz))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ r hraw (Q'.le_of_lt (Q'.recipPos_pos z hz)))
      (Q'.le_of_eqv hpin))

private theorem normalizedMoment_finiteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (p : RatPoly) (stage : Nat) :
    normalizedMoment (B extent)
      (polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids) p
      (selectedMass_positive hw0 hw1 (headCutoff w+stage) extent (Nat.le_add_right _ _) ids hids) ≈
      finiteValue w hw0 hw1 extent ids hids p stage := by
  unfold normalizedMoment finiteValue reciprocalTerm PositiveRationalCauchyReciprocal.term
    partitionSample heatProductHaar numerator
  exact qmul (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_refl _)

/-- The two existing finiteValue moments have the SAME cutoff, selected
action and reciprocal. No density or observable is replaced on normalization. -/
theorem finiteValue_variance_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (stage : Nat) :
    starRatio w ≤
      finiteValue w hw0 hw1 extent ids hids
        (polyMul (faceCharacter extent face) (faceCharacter extent face)) stage +
      -(finiteValue w hw0 hw1 extent ids hids (faceCharacter extent face) stage *
        finiteValue w hw0 hw1 extent ids hids (faceCharacter extent face) stage) := by
  have hmean := normalizedMoment_finiteValue hw0 hw1 extent ids hids (faceCharacter extent face) stage
  have hsquare := normalizedMoment_finiteValue hw0 hw1 extent ids hids
    (polyMul (faceCharacter extent face) (faceCharacter extent face)) stage
  exact Q'.le_trans' _ _ _
    (normalizedVariance_floor hw0 hw1 (headCutoff w+stage) extent (Nat.le_add_right _ _)
      ids hids hnodup hf link hl)
    (Q'.le_of_eqv (Q'.add_eqv_congr' hsquare (Q'.neg_eqv_congr _ _ (qmul hmean hmean))))

end YMGap.Continuum.BF4ExactSlabSelectedStarVariance

#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.selectedStar_length_le_six
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.selected_heat_partition
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.faceCharacter_supported
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.selected_star_bounds
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.selectedMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.shifted_square_floor
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.normalizedVariance_floor
#print axioms YMGap.Continuum.BF4ExactSlabSelectedStarVariance.finiteValue_variance_floor
