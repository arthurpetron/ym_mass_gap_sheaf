/-
# Centered two-nome susceptibility of the ORIGINAL one-face expectation

The constructed score is the difference of the two original heat prefixes,
each normalized in the SAME retained background. Its background mean is
exactly zero. The actual normalized response is its covariance with the
probe; its square is bounded by probe variance times score variance.

Every shared-link background factor is retained. Positivity is constructed
for every 0<u,v<1 at the explicit late heat cutoffs, without a small-nome
guard. No beta-uniform bound on the score variance, summable spatial response,
cutoff-limit susceptibility or continuum survival is asserted.
-/
import YMGap.Continuum.QuaternionHaarCenteredResponse
import YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability

namespace YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarCenteredResponse
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

variable {u v : Q'} (hu0 : (0 : Q') < u) (hu1 : u < (1 : Q'))
  (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q'))
  (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
  (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
  {B : RatPoly} (HB : Certificate (blocks extent) B)
  (hB : (0 : Q') < quaternionHaar (blocks extent) B)

local notation "hU" => faceMass_positive hu0 hu1 extent id hi HB K hKu hB
local notation "hV" => faceMass_positive hv0 hv1 extent id hi HB K hKv hB
local notation "U" => faceHeatPolynomial u K extent id
local notation "V" => faceHeatPolynomial v K extent id

/-- A finite original polynomial: only scalar partition ratios occur. -/
def faceScore : RatPoly := responsePolynomial (blocks extent) B U V hU hV

/-- The response is centered in the ACTUAL retained background, not bare Haar. -/
theorem faceScore_centered :
    normalizedMoment (blocks extent) B
      (faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB) hB ≈ 0 :=
  response_centered hB hU hV

private theorem normalized_face_pin (w : Q') (K extent id : Nat) (B p : RatPoly)
    (h : (0 : Q') < faceMass w K extent id B) :
    normalizedMoment (blocks extent) (polyMul B (faceHeatPolynomial w K extent id)) p h ≈
      faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B) h :=
  Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.mul_comm _ p).trans (RatPolyCoeffEqv.mul_assoc p B _).symm))

/-- Exact pin to the SAME normalized face response used by the coupling path. -/
theorem face_response_pin (p : RatPoly) :
    normalizedMoment (blocks extent) B
      (polyMul p (faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB)) hB ≈
      faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hV +
        -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hU) :=
  Q'.eqv_trans _ _ _ (response_pin hB hU hV p)
    (Q'.add_eqv_congr' (normalized_face_pin v K extent id B p hV)
      (Q'.neg_eqv_congr _ _ (normalized_face_pin u K extent id B p hU)))

/-- The exact change is a CENTERED covariance in the same background. -/
theorem face_centered_response_pin (p : RatPoly) :
    normalizedMoment (blocks extent) B
      (polyMul (shifted p (normalizedMoment (blocks extent) B p hB))
        (faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB)) hB ≈
      faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hV +
        -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hU) :=
  Q'.eqv_trans _ _ _
    (centered_pair_pin hB (faceScore_centered hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB) _)
    (face_response_pin hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB p)

/-- Constructed finite susceptibility estimate. The probe variance and the
score's zero-mean second moment both retain the full interacting background. -/
theorem face_response_square_bound {p : RatPoly} (hp : SupportedQuaternionBlocks (blocks extent) p) :
    let d := faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hV +
      -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hU)
    let s := faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB
    d*d ≤ normalizedVariance (blocks extent) B p hB *
      normalizedMoment (blocks extent) B (polyMul s s) hB := by
  have hs := responsePolynomial_supported hU hV
    (facePrefixInterval hu0 hu1 K extent id hi).support
    (facePrefixInterval hv0 hv1 K extent id hi).support
  have he := face_response_pin hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB p
  have he2 := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he)
    (Q'.mul_eqv_congr_left _ _ _ he)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he2)
    (centered_response_square_bound HB hB hp hs (response_centered hB hU hV))

include hu0 hu1 hv0 hv1 hi hKu hKv in
/-- The spectator heat product supplies its own positivity; no analytic
background certificate is left uninhabited. Its nome and cutoff may differ
from the changed face, and shared links are not factored away. -/
theorem original_background_response_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (J : Nat) (hJ : headCutoff w ≤ J) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (blocks extent) p) :
    let B := polynomialProduct (faceHeatPolynomial w J extent) ids
    let HB := headProduct_certificate hw0 hw1 J extent hJ ids hids
    let hB : (0 : Q') < quaternionHaar (blocks extent) B :=
      Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
        (partition_floor hw0 hw1 extent ids hids J hJ)
    let hOld := faceMass_positive hu0 hu1 extent id hi HB K hKu hB
    let hNew := faceMass_positive hv0 hv1 extent id hi HB K hKv hB
    let d := faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hNew +
      -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hOld)
    let s := faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB
    d*d ≤ normalizedVariance (blocks extent) B p hB *
      normalizedMoment (blocks extent) B (polyMul s s) hB :=
  face_response_square_bound hu0 hu1 hv0 hv1 K extent id hi hKu hKv
    (headProduct_certificate hw0 hw1 J extent hJ ids hids)
    (Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partition_floor hw0 hw1 extent ids hids J hJ)) hp

end YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse

#print axioms YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse.faceScore
#print axioms YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse.faceScore_centered
#print axioms YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse.face_response_pin
#print axioms YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse.face_centered_response_pin
#print axioms YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse.face_response_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse.original_background_response_bound
