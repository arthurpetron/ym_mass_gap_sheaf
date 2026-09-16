/-
# The original one-link normalizer: exact marginal and strict Haar form bounds

D is the actual partial Haar integral of the incident heat product after
moving the selected physical link to block zero. The original exterior
weight is D times the untouched complement B, not B alone. Exact insertion
and partition identities retain this same action and every shared link.

The local floor/cap descend to every exterior polynomial-square test, also
with the actual complementary action B retained. These are Haar FORM bounds,
not an assumed pointwise positivity statement. Their constants depend on w,
independently of volume and sufficiently late K.
This does not assert a conditional ratio, spatial contraction or OS gap.
-/

import YMGap.Continuum.BF4ExactSlabLocalStarComparison
import YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.PositiveContractionOneStepForm

namespace YMGap.Continuum.BF4ExactSlabStarNormalizer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

def normalizer (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) : RatPoly :=
  partialHaarHead (reindexQuaternionPolynomial (linkHeadSwap extent link hl) (incidentHeat w K extent link))

def exterior (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) : RatPoly :=
  dropHeadPolynomial (reindexQuaternionPolynomial (linkHeadSwap extent link hl) (complementHeat w K extent link))

def insertedNormalizer (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (p : RatPoly) : RatPoly :=
  partialHaarHead (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
    (polyMul p (incidentHeat w K extent link)))

theorem normalizer_supported (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    SupportedQuaternionBlocks (blocks extent-1) (normalizer w K extent link hl) := by
  have hlt := List.idxOf_lt_length_of_mem hl
  have hn : blocks extent = (blocks extent-1)+1 := by dsimp only [blocks]; omega
  apply BF4ExactPhysicalCenteredVacuumTransmittedMarginal.partialHaarHead_supported
  rw [← hn]
  exact BF4ExactPhysicalCenteredVacuumTransmittedMarginal.reindexQuaternionPolynomial_supported _ _

/-- The partition function has the ORIGINAL exterior weight D*B. -/
theorem full_partition_pin (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    quaternionHaar (blocks extent)
      (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)) ≈
    quaternionHaar (blocks extent-1)
      (polyMul (normalizer w K extent link hl) (exterior w K extent link hl)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (heatProduct_partition w K extent link))
    (complementHeat_fubini w K extent link hl _ (incidentHeat_supported w K extent link))

/-- Integrating the selected original link retains the entire inserted
numerator, not a test under the star-deleted exterior law. -/
theorem full_insertion_pin (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    quaternionHaar (blocks extent)
      (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))) ≈
    quaternionHaar (blocks extent-1)
      (polyMul (insertedNormalizer w K extent link hl p) (exterior w K extent link hl)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    (((RatPolyCoeffEqv.refl p).mul (heatProduct_partition w K extent link)).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm))
    (complementHeat_fubini w K extent link hl _
      (supported_polyMul hp (incidentHeat_supported w K extent link)))

/-- Uniform coercivity and boundedness on ALL supported exterior square
tests. No passage from full Haar equality to pointwise equality is used. -/
theorem normalizer_form_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r) :
    lowerFactor w * quaternionHaar (blocks extent-1) (polyMul r r) ≤
      quaternionHaar (blocks extent-1) (polyMul (polyMul r r) (normalizer w K extent link hl)) ∧
    quaternionHaar (blocks extent-1) (polyMul (polyMul r r) (normalizer w K extent link hl)) ≤
      upperFactor w * quaternionHaar (blocks extent-1) (polyMul r r) := by
  let swap := linkHeadSwap extent link hl
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have hs := headProbe_supported swap r
  have h := atMostSix_bounds hw0 hw1 K extent hK (.square (headProbe swap r) hs)
    (incidentIds extent link) (fun _ hi => incidentIds_physical hi) (incidentIds_length_le_six extent link)
  have he := headProbe_square_pair hb swap r (incidentHeat w K extent link) hr
    (incidentHeat_supported w K extent link)
  have hn := headProbe_square_haar hb swap r hr
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hn))
      (Q'.le_trans' _ _ _ h.1 (Q'.le_of_eqv he)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
      (Q'.le_trans' _ _ _ h.2 (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hn)))⟩

theorem normalizer_square_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r) :
    (0 : Q') ≤ quaternionHaar (blocks extent-1)
      (polyMul (polyMul r r) (normalizer w K extent link hl)) :=
  Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (lowerFactor_positive hw0 hw1)) (Certificate.square r hr).haar_nonnegative)
    (normalizer_form_bounds hw0 hw1 K extent hK link hl r hr).1

private theorem multiplier_norm {n : Nat} {d : RatPoly}
    (hd : SupportedQuaternionBlocks n d) {U : Q'} (hU : (0 : Q') ≤ U)
    (hpos : ∀ p, SupportedQuaternionBlocks n p →
      (0 : Q') ≤ quaternionHaar n (polyMul (polyMul p p) d))
    (hupper : ∀ p, SupportedQuaternionBlocks n p →
      quaternionHaar n (polyMul (polyMul p p) d) ≤ U * quaternionHaar n (polyMul p p))
    (r : RatPoly) (hr : SupportedQuaternionBlocks n r) :
    quaternionHaar n (polyMul (polyMul r d) (polyMul r d)) ≤
      (U*U) * quaternionHaar n (polyMul r r) := by
  let G := weightedGNSData n polyOne (.one n)
  let P : G.V → G.V := fun p => ⟨polyMul p.val d, supported_polyMul p.property hd⟩
  have hb (a b : G.V) : G.B a b ≈ quaternionHaar n (polyMul a.val b.val) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one _)
  have hp (a : G.V) : G.B a (P a) ≈ quaternionHaar n (polyMul (polyMul a.val a.val) d) :=
    Q'.eqv_trans _ _ _ (hb a (P a)) (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  have hsa (a b : G.V) : G.B a (P b) ≈ G.B (P a) b :=
    Q'.eqv_trans _ _ _ (hb a (P b)) (Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => a.val | 1 => b.val | _ => d))) (Q'.eqv_symm (hb (P a) b)))
  have h := PositiveContractionOneStepForm.norm_bound G P hsa
    (fun a => Q'.le_trans' _ _ _ (hpos a.val a.property) (Q'.ge_of_eqv (hp a))) hU
    (fun a => Q'.le_trans' _ _ _ (Q'.le_of_eqv (hp a))
      (Q'.le_trans' _ _ _ (hupper a.val a.property)
        (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ (hb a a))))) ⟨r,hr⟩
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hb (P ⟨r,hr⟩) (P ⟨r,hr⟩)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (hb ⟨r,hr⟩ ⟨r,hr⟩))))

/-- Multiplication by the ACTUAL boundary normalizer is bounded in the
exterior Haar norm. This is not an OS transfer or heat-bath gap estimate. -/
theorem normalizer_multiplication_norm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r) :
    let d := normalizer w K extent link hl
    quaternionHaar (blocks extent-1) (polyMul (polyMul r d) (polyMul r d)) ≤
      (upperFactor w * upperFactor w) * quaternionHaar (blocks extent-1) (polyMul r r) :=
  multiplier_norm (normalizer_supported w K extent link hl) (Q'.le_of_lt (upperFactor_positive hw0))
    (normalizer_square_nonnegative hw0 hw1 K extent hK link hl)
    (fun p hp => (normalizer_form_bounds hw0 hw1 K extent hK link hl p hp).2) r hr

/-- The actual complementary exterior weight is positive under square
tests, proved by transport from its original full-carrier certificate. -/
theorem exterior_square_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r) :
    (0 : Q') ≤ quaternionHaar (blocks extent-1)
      (polyMul (polyMul r r) (exterior w K extent link hl)) := by
  let swap := linkHeadSwap extent link hl
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have he := headProbe_independent_pair hb swap (polyMul r r) (complementHeat w K extent link)
    (supported_polyMul hr hr) (complementHeat_supported w K extent link)
    (complementHeat_headIndependent w K extent link hl)
  rw [headProbe_mul] at he
  have hp := ((Certificate.square (headProbe swap r) (headProbe_supported swap r)).mul
    (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ hi => complementIds_physical hi))).haar_nonnegative
  exact Q'.le_trans' _ _ _ hp (Q'.le_of_eqv he)

/-- The SAME normalizer estimates retain the complementary action B.
Thus the lower and upper forms compare the original marginal D*B with B,
not just unweighted Haar on the exterior variables. -/
theorem normalizer_weighted_form_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r) :
    let d := normalizer w K extent link hl
    let b := exterior w K extent link hl
    lowerFactor w * quaternionHaar (blocks extent-1) (polyMul (polyMul r r) b) ≤
      quaternionHaar (blocks extent-1) (polyMul (polyMul (polyMul r r) d) b) ∧
    quaternionHaar (blocks extent-1) (polyMul (polyMul (polyMul r r) d) b) ≤
      upperFactor w * quaternionHaar (blocks extent-1) (polyMul (polyMul r r) b) := by
  let swap := linkHeadSwap extent link hl
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have he := headProbe_product_pair hb swap (polyMul r r) (incidentHeat w K extent link)
    (complementHeat w K extent link) (supported_polyMul hr hr)
    (incidentHeat_supported w K extent link) (complementHeat_supported w K extent link)
    (complementHeat_headIndependent w K extent link hl)
  rw [headProbe_mul] at he
  have hf := Q'.eqv_trans _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.refl (polyMul (headProbe swap r) (headProbe swap r))).mul
      (heatProduct_partition w K extent link))) he
  have hn := headProbe_independent_pair hb swap (polyMul r r) (complementHeat w K extent link)
    (supported_polyMul hr hr) (complementHeat_supported w K extent link)
    (complementHeat_headIndependent w K extent link hl)
  rw [headProbe_mul] at hn
  have h := original_star_bounds hw0 hw1 K extent hK link
    (.square (headProbe swap r) (headProbe_supported swap r))
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hn))
      (Q'.le_trans' _ _ _ h.1 (Q'.le_of_eqv hf)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hf)
      (Q'.le_trans' _ _ _ h.2 (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hn)))⟩

private def positiveWeightedData (n : Nat) (b : RatPoly)
    (hpos : ∀ p, SupportedQuaternionBlocks n p → (0 : Q') ≤ weightedPair n b p p) :
    GNSQuotient.GNSData :=
  { weightedGNSData n polyOne (.one n) with
    B := fun p q => weightedPair n b p.val q.val
    B_congr_left := fun q h => haar_of_coeff ((h.mul_right q.val).mul_right b)
    B_add_left := fun p q r => weighted_add_left n b p.val q.val r.val
    B_smul_left := fun c p q => weighted_smul_left n b c p.val q.val
    B_symm := fun p q => weighted_symm n b p.val q.val
    self_nonneg := fun p => hpos p.val p.property }

private theorem weighted_multiplier_norm {n : Nat} {d b : RatPoly}
    (hd : SupportedQuaternionBlocks n d) {U : Q'} (hU : (0 : Q') ≤ U)
    (hb : ∀ p, SupportedQuaternionBlocks n p → (0 : Q') ≤ weightedPair n b p p)
    (hpos : ∀ p, SupportedQuaternionBlocks n p →
      (0 : Q') ≤ quaternionHaar n (polyMul (polyMul (polyMul p p) d) b))
    (hupper : ∀ p, SupportedQuaternionBlocks n p →
      quaternionHaar n (polyMul (polyMul (polyMul p p) d) b) ≤ U * weightedPair n b p p)
    (r : RatPoly) (hr : SupportedQuaternionBlocks n r) :
    weightedPair n b (polyMul r d) (polyMul r d) ≤ (U*U) * weightedPair n b r r := by
  let G := positiveWeightedData n b hb
  let P : G.V → G.V := fun p => ⟨polyMul p.val d, supported_polyMul p.property hd⟩
  have hp (a : G.V) : G.B a (P a) ≈ quaternionHaar n (polyMul (polyMul (polyMul a.val a.val) d) b) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.mul_right b)
  have hsa (a c : G.V) : G.B a (P c) ≈ G.B (P a) c :=
    haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => a.val | 1 => c.val | _ => d)).mul_right b)
  exact PositiveContractionOneStepForm.norm_bound G P hsa
    (fun a => Q'.le_trans' _ _ _ (hpos a.val a.property) (Q'.ge_of_eqv (hp a))) hU
    (fun a => Q'.le_trans' _ _ _ (Q'.le_of_eqv (hp a)) (hupper a.val a.property)) ⟨r,hr⟩

/-- Bounded multiplication in the B-weighted exterior norm, the reference
form compared above with the ORIGINAL D*B marginal. -/
theorem normalizer_weighted_multiplication_norm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r) :
    let d := normalizer w K extent link hl
    let b := exterior w K extent link hl
    weightedPair (blocks extent-1) b (polyMul r d) (polyMul r d) ≤
      (upperFactor w * upperFactor w) * weightedPair (blocks extent-1) b r r := by
  apply weighted_multiplier_norm (normalizer_supported w K extent link hl)
    (Q'.le_of_lt (upperFactor_positive hw0))
    (exterior_square_nonnegative hw0 hw1 K extent hK link hl)
  · intro p hp
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (Q'.le_of_lt (lowerFactor_positive hw0 hw1))
      (exterior_square_nonnegative hw0 hw1 K extent hK link hl p hp))
      (normalizer_weighted_form_bounds hw0 hw1 K extent hK link hl p hp).1
  · exact fun p hp => (normalizer_weighted_form_bounds hw0 hw1 K extent hK link hl p hp).2
  · exact hr

/-- Exact conditional test identity before division: every exterior test
is lifted to the original full action and pairs with the actual numerator.
Neither the exterior weight nor the observable is replaced. -/
theorem full_test_pin (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r p : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r)
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    quaternionHaar (blocks extent)
      (polyMul (headProbe (linkHeadSwap extent link hl) r)
        (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)))) ≈
    quaternionHaar (blocks extent-1)
      (polyMul (polyMul r (insertedNormalizer w K extent link hl p)) (exterior w K extent link hl)) := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl _).mul
    (((RatPolyCoeffEqv.refl p).mul (heatProduct_partition w K extent link)).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm)))
    (headProbe_product_pair hb (linkHeadSwap extent link hl) r (polyMul p (incidentHeat w K extent link))
      (complementHeat w K extent link) hr (supported_polyMul hp (incidentHeat_supported w K extent link))
      (complementHeat_supported w K extent link) (complementHeat_headIndependent w K extent link hl))

end YMGap.Continuum.BF4ExactSlabStarNormalizer

#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.normalizer
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.exterior
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.insertedNormalizer
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.normalizer_supported
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.full_partition_pin
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.full_insertion_pin
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.normalizer_form_bounds
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.normalizer_square_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.normalizer_multiplication_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.exterior_square_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.normalizer_weighted_form_bounds
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.normalizer_weighted_multiplication_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarNormalizer.full_test_pin
