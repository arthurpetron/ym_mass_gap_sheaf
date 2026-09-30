/-
# Original selected-action covariance pays the plaquette prediction floor

An observable missing one actual plaquette link cannot perfectly predict the
plaquette. The already proved original prediction-error floor strengthens
Cauchy--Schwarz by subtracting starRatio(w) from the plaquette variance.
Every action factor and the SAME selected partition remain in the bound.

This holds at every rational 0<w<1, uniformly in extent and late heat cutoff,
for arbitrary duplicate-free physical face selections. It is a single
covariance deficit, NOT decay with distance or a physical spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError
import YMGap.Continuum.QuaternionHaarPredictionCovariance
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BF4ExactSlabSelectedPredictionCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPredictionCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
  (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
  (hnodup : ids.Nodup)

local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) ids
local notation "hZ" => selectedMass_positive hw0 hw1 K extent hK ids hids

include hnodup in
/-- Every affine predictor built from a link-free observable has the actual
normalized local prediction cost. The SAME selected density is used. -/
theorem affine_prediction_floor {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) (a t : Q') :
    starRatio w ≤ normalizedMoment (N extent) W
      (polyMul
        (polynomialError extent face (polyAdd (polySmul a polyOne) (polySmul t q)))
        (polynomialError extent face (polyAdd (polySmul a polyOne) (polySmul t q)))) hZ := by
  let predictor := polyAdd (polySmul a polyOne) (polySmul t q)
  have hs : SupportedQuaternionBlocks (N extent) predictor :=
    supported_add (support_smul (supported_one _) a) (support_smul hq t)
  have hlp : LinkLocal extent links predictor :=
    BlockLocal.add ((BlockLocal.one _ _).smul a) (hlocal.smul t)
  have h := polynomial_square_floor hw0 hw1 K extent hK ids hids hnodup
    hf link hl predictor hs links hlp hfree
  let Z := quaternionHaar (N extent) W
  let r := Q'.recipPos Z hZ
  have he : (starRatio w*Z)*r ≈ starRatio w :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_right _ _ r h (Q'.le_of_lt (Q'.recipPos_pos Z hZ)))

include hnodup in
/-- Supplied original prediction floor yields an explicit additive improvement
over ordinary covariance Cauchy--Schwarz, with no small-nome guard. -/
theorem normalized_covariance_deficit {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) :
    let p := faceCharacter extent face
    normalizedCovariance (N extent) W p q hZ * normalizedCovariance (N extent) W p q hZ ≤
      (normalizedVariance (N extent) W p hZ + -(starRatio w)) *
        normalizedVariance (N extent) W q hZ := by
  apply covariance_sq_le_variance_deficit
    (headProduct_certificate hw0 hw1 K extent hK ids hids) hZ
    (faceCharacter_supported extent face) hq (starRatio w)
  intro a t
  exact affine_prediction_floor hw0 hw1 K extent hK ids hids hnodup
    hf link hl q hq links hlocal hfree a t

omit K hK hnodup in
/-- Exact pin to the existing finite covariance, including the original
partition. No replacement normalized law is introduced. -/
theorem normalizedCovariance_finiteCovariance (p q : RatPoly) (stage : Nat) :
    normalizedCovariance (N extent)
      (polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids) p q
      (selectedMass_positive hw0 hw1 (headCutoff w+stage) extent
        (Nat.le_add_right _ _) ids hids) ≈
      finiteCovariance w hw0 hw1 extent ids hids p q stage :=
  Q'.add_eqv_congr'
    (normalizedMoment_finiteValue hw0 hw1 extent ids hids (polyMul p q) stage)
    (Q'.neg_eqv_congr _ _ (qmul
      (normalizedMoment_finiteValue hw0 hw1 extent ids hids p stage)
      (normalizedMoment_finiteValue hw0 hw1 extent ids hids q stage)))

omit K hK in
include hnodup in
/-- The SAME original finite selected-action covariance and diagonal forms
pay a nome-only deficit whenever the test misses one plaquette link. -/
theorem finite_covariance_deficit {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) (stage : Nat) :
    let p := faceCharacter extent face
    let C := fun a b => finiteCovariance w hw0 hw1 extent ids hids a b stage
    C p q * C p q ≤ (C p p + -(starRatio w))*C q q := by
  have h := normalized_covariance_deficit hw0 hw1 (headCutoff w+stage) extent
    (Nat.le_add_right _ _) ids hids hnodup hf link hl q hq links hlocal hfree
  have hpq := normalizedCovariance_finiteCovariance hw0 hw1 extent ids hids
    (faceCharacter extent face) q stage
  have hpp := normalizedCovariance_finiteCovariance hw0 hw1 extent ids hids
    (faceCharacter extent face) (faceCharacter extent face) stage
  have hqq := normalizedCovariance_finiteCovariance hw0 hw1 extent ids hids q q stage
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hpq hpq))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (qmul (Q'.add_eqv_congr_right _ _ _ hpp) hqq)))

omit K hK in
include hnodup in
/-- Passes the ACTUAL selected-action deficit through its existing heat-cutoff
limit. This is neither decay with distance nor a spatial/scaling limit. -/
theorem covariance_deficit {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) :
    let p := faceCharacter extent face
    let C := covariance w hw0 hw1 extent ids hids
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (CReal.sub (C p p) (ofQ' (starRatio w))) (C q q)) := by
  dsimp only
  let p := faceCharacter extent face
  let C := covariance w hw0 hw1 extent ids hids
  let f : RatPoly → RatPoly → Nat → CReal :=
    fun a b stage => ofQ' (finiteCovariance w hw0 hw1 extent ids hids a b stage)
  have hpq := finite_covariance_converges w hw0 hw1 extent ids hids p q
  have hpp := finite_covariance_converges w hw0 hw1 extent ids hids p p
  have hqq := finite_covariance_converges w hw0 hw1 extent ids hids q q
  have hs : ConvergesTo
      (fun stage => CReal.sub (f p p stage) (ofQ' (starRatio w)))
      (CReal.sub (C p p) (ofQ' (starRatio w))) :=
    CReal.convergesTo_add hpp
      (TrigAddCReal.convergesTo_neg (CReal.convergesTo_const (ofQ' (starRatio w))))
  have hleft : ConvergesTo (fun stage => CReal.mul (f p q stage) (f p q stage))
      (CReal.mul (C p q) (C p q)) := convergesTo_mul_general hpq hpq
  have hright : ConvergesTo
      (fun stage => CReal.mul (CReal.sub (f p p stage) (ofQ' (starRatio w)))
        (f q q stage))
      (CReal.mul (CReal.sub (C p p) (ofQ' (starRatio w))) (C q q)) :=
    convergesTo_mul_general hs hqq
  apply CReal.leEv_of_convergesTo_le hleft hright
  intro stage
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hfin := finite_covariance_deficit hw0 hw1 extent ids hids hnodup
    hf link hl q hq links hlocal hfree stage
  exact Q'.le_trans' _ _ _ hfin
    (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))

#print axioms affine_prediction_floor
#print axioms normalized_covariance_deficit
#print axioms normalizedCovariance_finiteCovariance
#print axioms finite_covariance_deficit
#print axioms covariance_deficit

end YMGap.Continuum.BF4ExactSlabSelectedPredictionCovariance
