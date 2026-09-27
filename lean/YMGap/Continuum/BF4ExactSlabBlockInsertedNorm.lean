/-
# Actual block inserted numerator: original-to-background norm bound

The numerator integrates only the selected original coordinates. Its norm is
measured with the exact detached original background; its input is measured
with the exact original full-face action. The upper coefficient depends on
nome and the selected-link count, not volume or late heat cutoff. This is
not a block-angle, mixing, scaling, or OS estimate.
-/

import YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
import YMGap.Continuum.BF4ExactSlabStarFullActionProbe
import YMGap.Continuum.OSReconstructionProgress

namespace YMGap.Continuum.BF4ExactSlabBlockInsertedNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- An arbitrary selected-family-independent test pairs with the inserted
numerator exactly as it pairs with the original full-action observable. -/
theorem insertedNormalizer_pair_pin (w : Q') (K extent : Nat)
    (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (r p : RatPoly)
    (hr : ∀ i, i ∈ slots extent links → QuaternionBlockIndependent i r) :
    weightedPair (blocks extent) (fullWeight w K extent) r p ≈
      weightedPair (blocks extent) (background w K extent links) r
        (insertedNormalizer w K extent links p) := by
  let s := slots extent links
  let A := collarHeat w K extent links
  let B := background w K extent links
  let N := insertedNormalizer w K extent links p
  have hnum : RatPolyCoeffEqv
      (insertedNormalizer w K extent links (polyMul r p)) (polyMul r N) :=
    (familyProject_congr s (RatPolyCoeffEqv.mul_assoc r p A)).trans
      (familyProject_mul_of_independent s r (polyMul p A) hr)
  have hfull := full_insertion_pin w K extent links hl (polyMul r p)
  exact Q'.eqv_trans _ _ _ hfull
    (haar_of_coeff ((hnum.mul_left B).trans (RatPolyCoeffEqv.mul_comm B (polyMul r N))))

/-- The actual family-integrated numerator has a squared norm ceiling on the
detached-background carrier, paid by the SAME original full-action norm of
the input polynomial. No locality condition is imposed on `p`. -/
theorem insertedNormalizer_weighted_norm {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p) :
    weightedPair (blocks extent) (background w K extent links)
      (insertedNormalizer w K extent links p)
      (insertedNormalizer w K extent links p) ≤
    blockUpper w links.length *
      weightedPair (blocks extent) (fullWeight w K extent) p p := by
  let W := fullWeight w K extent
  let B := background w K extent links
  let N := insertedNormalizer w K extent links p
  let x := weightedPair (blocks extent) B N N
  let A := weightedPair (blocks extent) W p p
  have hN : SupportedQuaternionBlocks (blocks extent) N :=
    insertedNormalizer_supported w K extent links hp
  have hW : Certificate (blocks extent) W :=
    headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent)
      (fun _ hi => hi)
  have hA : (0 : Q') ≤ A := hW.square_insertion_nonnegative p hp
  have he : weightedPair (blocks extent) W N p ≈ x :=
    insertedNormalizer_pair_pin w K extent links hl N p
      (fun i hi => familyProject_independent _ _ i hi)
  have hsq : weightedPair (blocks extent) W N p *
      weightedPair (blocks extent) W N p ≈ x*x :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he)
      (Q'.mul_eqv_congr_left _ _ _ he)
  have hcs := weighted_cauchySchwarz (blocks extent) W N p hW hN hp
  have hfull : weightedPair (blocks extent) W N N ≤
      blockUpper w links.length * x :=
    (collar_weighted_bounds hw0 hw1 K extent hK links links.length
      (Nat.le_refl _) (Certificate.square N hN)).2
  have hscaled : weightedPair (blocks extent) W N N * A ≤
      (blockUpper w links.length*x)*A :=
    Q'.mul_le_mul_of_nonneg_right _ _ A hfull hA
  have hproduct : x*x ≤ x*(blockUpper w links.length*A) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsq)
      (Q'.le_trans' _ _ _ hcs
        (Q'.le_trans' _ _ _ hscaled
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _
            (Q'.mul_assoc_eqv _ _ _) (mul_pull _ _ _)))))
  change x ≤ blockUpper w links.length*A
  by_cases hx : (0 : Q') < x
  · exact q_cancel_left hx hproduct
  · have hnum : x.num ≤ (0 : Int) :=
      Int.not_lt.mp (fun h => hx ((zero_lt_iff_num_pos x).mpr h))
    have hx0 : x ≤ (0 : Q') := by
      change x.num * (1 : Int) ≤ (0 : Int) * (x.den : Int)
      simpa only [Int.mul_one, Int.zero_mul] using hnum
    exact Q'.le_trans' _ _ _ hx0
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (blockUpper_positive hw0 links.length)) hA)

end YMGap.Continuum.BF4ExactSlabBlockInsertedNorm

#print axioms YMGap.Continuum.BF4ExactSlabBlockInsertedNorm.insertedNormalizer_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabBlockInsertedNorm.insertedNormalizer_weighted_norm
