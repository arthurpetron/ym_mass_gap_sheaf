/-
# Original-action variance comparison from the constructed local Haar score

The weight is exactly R*A in the selected-link frame already pinned to
the original slab action. Its positivity is constructed at the explicit
late cutoff, not assumed. The Ward response squared is bounded by the
centered full-action square times the cost of the SAME local score.

Every rational center is allowed. No score norm, response floor, spatial
mixing, or continuum survival estimate is assumed or concluded here.
-/

import YMGap.Continuum.BF4ExactSlabLocalHaarWard
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
import YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence

namespace YMGap.Continuum.BF4ExactSlabLocalWardVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalHaarWard
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

private theorem neg_of_sum_zero (x y : Q') (h : x + y ≈ 0) : y ≈ -x := by
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 1) (.var 0)) (by decide) (fun n => if n = 0 then y else x)) h

private theorem negative_square (x : Q') : (-x)*(-x) ≈ x*x :=
  poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
    (.mul (.var 0) (.var 0)) (by decide) (fun _ => x)

private theorem scaled_product (x y r : Q') : (x*r)*(y*r) ≈ (x*y)*(r*r) :=
  poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2))) (by decide)
    (fun n => if n = 0 then x else if n = 1 then y else r)

variable (w : Q') (K extent : Nat) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "swap" => linkHeadSwap extent link hl
local notation "A" => reindexQuaternionPolynomial swap (incidentHeat w K extent link)
local notation "R" => reindexQuaternionPolynomial swap (complementHeat w K extent link)
local notation "W" => polyMul R A
local notation "originalWeight" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- Unnormalized original-action moment in the already-pinned head frame. -/
def frameMoment (p : RatPoly) : Q' :=
  quaternionHaar (blocks extent) (polyMul R (polyMul A p))

/-- The precise numerator paired against the mean-zero local score. -/
def scoreResponse (i j : Nat) (g f : RatPoly) : Q' :=
  frameMoment w K extent link hl (polyMul (polyMul A g) (angularDerivative i j f))

/-- Positivity for the SAME full weight, with the explicit late-cutoff guard. -/
def frameWeight_certificate (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) : Certificate (blocks extent) W :=
  (reindex_certificate swap (complementHeat_supported w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ h => complementIds_physical h))).mul
    (reindex_certificate swap (incidentHeat_supported w K extent link)
      (headProduct_certificate hw0 hw1 K extent hK (incidentIds extent link)
        (fun _ h => incidentIds_physical h)))

theorem localScore_supported {i j : Nat} (hi : i < 4) (hj : j < 4)
    {g : RatPoly} (hg : SupportedQuaternionBlocks (blocks extent) g) :
    SupportedQuaternionBlocks (blocks extent) (localScore w K extent link hl i j g) := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have hA := reindex_supported swap (incidentHeat w K extent link)
  exact polyAdd_supported
    (supported_polyMul hA (angularDerivative_supported hb hi hj hg))
    (polySmul_supported (supported_polyMul (angularDerivative_supported hb hi hj hA) hg) 2)

private theorem moment_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    frameMoment w K extent link hl p ≈ frameMoment w K extent link hl q :=
  haar_of_coeff ((h.mul_left A).mul_left R)

private theorem moment_add (p q : RatPoly) :
    frameMoment w K extent link hl (polyAdd p q) ≈
      frameMoment w K extent link hl p + frameMoment w K extent link hl q :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    (((RatPolyCoeffEqv.mul_add_right A p q).mul_left R).trans
      (RatPolyCoeffEqv.mul_add_right R _ _)))
    (quaternionHaar_append (blocks extent) _ _)

private theorem moment_pair (p q : RatPoly) :
    frameMoment w K extent link hl (polyMul p q) ≈
      weightedPair (blocks extent) W p q :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_assoc R A (polyMul p q)).symm.trans
    (RatPolyCoeffEqv.mul_comm W (polyMul p q)))

/-- Subtracting a rational center leaves the response unchanged, and the
cross moment is its exact negative under the original action. -/
theorem scoreResponse_centered_pin {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g f : RatPoly) (c : Q') :
    scoreResponse w K extent link hl i j g f ≈
      -(frameMoment w K extent link hl
        (polyMul (polyAdd f (polySmul (-c) polyOne)) (localScore w K extent link hl i j g))) := by
  let fc := polyAdd f (polySmul (-c) polyOne)
  let S := localScore w K extent link hl i j g
  have h := fullAction_score_identity w K extent link hl hi hj g fc
  have hc := moment_congr w K extent link hl
    ((angularDerivative_centered hi hj c f).mul_left (polyMul A g))
  have hz : frameMoment w K extent link hl (polyMul fc S) +
      scoreResponse w K extent link hl i j g f ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_eqv_congr_left _ _ _ hc))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (moment_add w K extent link hl _ _)) h)
  exact neg_of_sum_zero _ _ hz

/-- Sharp original-action variance/response comparison. The response is
independent of the chosen center; its cost is the ACTUAL score square,
not a supplied majorant or a deleted-action expectation. -/
theorem scoreResponse_squared_le_centered_cost
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w ≤ K)
    {i j : Nat} (hi : i < 4) (hj : j < 4) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (blocks extent) g)
    (hf : SupportedQuaternionBlocks (blocks extent) f) (c : Q') :
    scoreResponse w K extent link hl i j g f * scoreResponse w K extent link hl i j g f ≤
      frameMoment w K extent link hl
        (polyMul (polyAdd f (polySmul (-c) polyOne)) (polyAdd f (polySmul (-c) polyOne))) *
      frameMoment w K extent link hl
        (polyMul (localScore w K extent link hl i j g) (localScore w K extent link hl i j g)) := by
  let fc := polyAdd f (polySmul (-c) polyOne)
  let S := localScore w K extent link hl i j g
  have hfc := polyAdd_supported hf (polySmul_supported (supported_one (blocks extent)) (-c))
  have hcs := weighted_cauchySchwarz (blocks extent) W fc S
    (frameWeight_certificate w K extent link hl hw0 hw1 hK) hfc
    (localScore_supported w K extent link hl hi hj hg)
  have hpin := Q'.eqv_trans _ _ _ (scoreResponse_centered_pin w K extent link hl hi hj g f c)
    (Q'.neg_eqv_congr _ _ (moment_pair w K extent link hl fc S))
  have hsq : scoreResponse w K extent link hl i j g f * scoreResponse w K extent link hl i j g f ≈
      weightedPair (blocks extent) W fc S * weightedPair (blocks extent) W fc S :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpin)
        (Q'.mul_eqv_congr_left _ _ _ hpin))
      (negative_square _)
  have hr : frameMoment w K extent link hl (polyMul fc fc) *
      frameMoment w K extent link hl (polyMul S S) ≈
      weightedPair (blocks extent) W fc fc * weightedPair (blocks extent) W S S := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (moment_pair w K extent link hl fc fc))
    (Q'.mul_eqv_congr_left _ _ _ (moment_pair w K extent link hl S S))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsq)
    (Q'.le_trans' _ _ _ hcs (Q'.ge_of_eqv hr))

/-- The frame partition equals the original complete finite slab partition. -/
theorem framePartition_pin :
    quaternionHaar (blocks extent) originalWeight ≈ quaternionHaar (blocks extent) W := by
  have hc := (heatProduct_partition w K extent link).trans (RatPolyCoeffEqv.mul_comm _ _)
  have he := quaternionHaar_reindex swap
    (polyMul (complementHeat w K extent link) (incidentHeat w K extent link))
    (supported_polyMul (complementHeat_supported w K extent link) (incidentHeat_supported w K extent link))
  rw [reindexQuaternionPolynomial_mul] at he
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc) (Q'.eqv_symm he)

/-- Strict positivity is inherited from the ORIGINAL partition; no new
probability law or independent partition estimate is postulated. -/
theorem framePartition_positive (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) : (0 : Q') < quaternionHaar (blocks extent) W := by
  have hp := partition_floor hw0 hw1 extent (slabPhysicalFaceEdges extent) (fun _ h => h) K hK
  exact Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 _)
    (Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (framePartition_pin w K extent link hl)))

/-- Normalize the actual Ward response by the SAME positive full partition. -/
def normalizedResponse (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) (i j : Nat) (g f : RatPoly) : Q' :=
  scoreResponse w K extent link hl i j g f *
    Q'.recipPos (quaternionHaar (blocks extent) W)
      (framePartition_positive w K extent link hl hw0 hw1 hK)

/-- The center is now the computed mean of f under the full R*A action.
This is an inequality for its actual normalized variance, not a freely
supplied variance or score-cost bound. The entire signed f is retained. -/
theorem normalizedResponse_squared_le_variance_cost
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w ≤ K)
    {i j : Nat} (hi : i < 4) (hj : j < 4) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (blocks extent) g)
    (hf : SupportedQuaternionBlocks (blocks extent) f) :
    normalizedResponse w K extent link hl hw0 hw1 hK i j g f *
        normalizedResponse w K extent link hl hw0 hw1 hK i j g f ≤
      normalizedVariance (blocks extent) W f (framePartition_positive w K extent link hl hw0 hw1 hK) *
      normalizedMoment (blocks extent) W
        (polyMul (localScore w K extent link hl i j g) (localScore w K extent link hl i j g))
        (framePartition_positive w K extent link hl hw0 hw1 hK) := by
  let hZ := framePartition_positive w K extent link hl hw0 hw1 hK
  let r := Q'.recipPos (quaternionHaar (blocks extent) W) hZ
  let c := normalizedMoment (blocks extent) W f hZ
  let fc := polyAdd f (polySmul (-c) polyOne)
  let S := localScore w K extent link hl i j g
  have h := scoreResponse_squared_le_centered_cost w K extent link hl hw0 hw1 hK hi hj g f hg hf c
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ (r*r) h (SumOfSquares.q_mul_self_nonneg r)
  have hm (p : RatPoly) : frameMoment w K extent link hl p * r ≈ normalizedMoment (blocks extent) W p hZ :=
    Q'.mul_eqv_congr_right _ _ r (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R A p).symm)
  have hshift : RatPolyCoeffEqv fc (shifted f c) :=
    (RatPolyCoeffEqv.one_smul f).symm.add (RatPolyCoeffEqv.refl _)
  have hvar : frameMoment w K extent link hl (polyMul fc fc)*r ≈ normalizedVariance (blocks extent) W f hZ :=
    Q'.eqv_trans _ _ _ (hm _) (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ r (haar_of_coeff ((hshift.mul hshift).mul_left W)))
      (own_mean_pin (frameWeight_certificate w K extent link hl hw0 hw1 hK) hf hZ))
  have hright : (frameMoment w K extent link hl (polyMul fc fc)*r) *
      (frameMoment w K extent link hl (polyMul S S)*r) ≈
      normalizedVariance (blocks extent) W f hZ * normalizedMoment (blocks extent) W (polyMul S S) hZ :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hvar) (Q'.mul_eqv_congr_left _ _ _ (hm _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (scaled_product _ _ r))
    (Q'.le_trans' _ _ _ hs
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (scaled_product _ _ r)) (Q'.le_of_eqv hright)))

/-- Reindexing preserves each normalized moment of the ORIGINAL supported
observable. The reciprocal follows the proved partition equality. -/
theorem originalMoment_frame_pin (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hOriginal : (0 : Q') < quaternionHaar (blocks extent) originalWeight)
    (hFrame : (0 : Q') < quaternionHaar (blocks extent) W) :
    normalizedMoment (blocks extent) originalWeight p hOriginal ≈
      normalizedMoment (blocks extent) W (reindexQuaternionPolynomial swap p) hFrame := by
  have hnum := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm originalWeight p))
    (Q'.eqv_trans _ _ _ (fullAction_pair_pin w K extent link hl p hp)
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R A _).symm))
  have hrec := Q'.recipPos_eqv_congr _ _ hOriginal hFrame (framePartition_pin w K extent link hl)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hnum)
    (Q'.mul_eqv_congr_left _ _ _ hrec)

/-- The frame variance in the score inequality is the variance of the SAME
original supported observable, with its original partition and mean. -/
theorem originalVariance_frame_pin (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hOriginal : (0 : Q') < quaternionHaar (blocks extent) originalWeight)
    (hFrame : (0 : Q') < quaternionHaar (blocks extent) W) :
    normalizedVariance (blocks extent) originalWeight p hOriginal ≈
      normalizedVariance (blocks extent) W (reindexQuaternionPolynomial swap p) hFrame := by
  have h1 := originalMoment_frame_pin w K extent link hl p hp hOriginal hFrame
  have h2 := originalMoment_frame_pin w K extent link hl (polyMul p p)
    (supported_polyMul hp hp) hOriginal hFrame
  rw [reindexQuaternionPolynomial_mul] at h2
  exact Q'.add_eqv_congr' h2 (Q'.neg_eqv_congr _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.mul_eqv_congr_left _ _ _ h1)))

end YMGap.Continuum.BF4ExactSlabLocalWardVariance

#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.frameWeight_certificate
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.localScore_supported
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.scoreResponse_centered_pin
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.scoreResponse_squared_le_centered_cost
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.framePartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.framePartition_pin
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.normalizedResponse_squared_le_variance_cost
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.originalMoment_frame_pin
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardVariance.originalVariance_frame_pin
