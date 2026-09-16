/-
# Original-action control of the one-link inserted numerator

The actual partial Haar numerator N_p is a supported exterior polynomial.
Its norm with the complete complementary action B retained is bounded by
U(w) times the ORIGINAL full-action norm of p. The proof lifts N_p back to
the original carrier, applies weighted Cauchy--Schwarz there, and cancels
only in the decidable strictly positive rational-norm case.

No pointwise positivity, inverse normalizer, replacement exterior law,
OS quotient bound, spatial decay or uniformity as w approaches one is used.
-/

import YMGap.Continuum.BF4ExactSlabStarNormalizer

namespace YMGap.Continuum.BF4ExactSlabStarInsertedNumerator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

theorem insertedNormalizer_supported (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (p : RatPoly)
    (_hp : SupportedQuaternionBlocks (blocks extent) p) :
    SupportedQuaternionBlocks (blocks extent-1) (insertedNormalizer w K extent link hl p) := by
  have hlt := List.idxOf_lt_length_of_mem hl
  have hn : blocks extent = (blocks extent-1)+1 := by dsimp only [blocks]; omega
  apply BF4ExactPhysicalCenteredVacuumTransmittedMarginal.partialHaarHead_supported
  rw [← hn]
  exact BF4ExactPhysicalCenteredVacuumTransmittedMarginal.reindexQuaternionPolynomial_supported _ _

/-- The full-action pairing is exactly the numerator pairing with B retained. -/
theorem insertedNormalizer_pair_pin (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r p : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r)
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    weightedPair (blocks extent)
      (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
      (headProbe (linkHeadSwap extent link hl) r) p ≈
    weightedPair (blocks extent-1) (exterior w K extent link hl)
      r (insertedNormalizer w K extent link hl p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
    (full_test_pin w K extent link hl r p hr hp)

/-- The lifted exterior test is bounded in the ORIGINAL full-action norm. -/
theorem headProbe_full_norm_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks extent-1) r) :
    weightedPair (blocks extent)
      (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
      (headProbe (linkHeadSwap extent link hl) r) (headProbe (linkHeadSwap extent link hl) r) ≤
    upperFactor w * weightedPair (blocks extent-1) (exterior w K extent link hl) r r := by
  let swap := linkHeadSwap extent link hl
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have he := headProbe_independent_pair hb swap (polyMul r r) (complementHeat w K extent link)
    (supported_polyMul hr hr) (complementHeat_supported w K extent link)
    (complementHeat_headIndependent w K extent link hl)
  rw [headProbe_mul] at he
  exact Q'.le_trans' _ _ _
    (original_star_bounds hw0 hw1 K extent hK link
      (.square (headProbe swap r) (headProbe_supported swap r))).2
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he))

/-- A genuine numerator norm bound on the B-weighted exterior carrier,
with input measured in the original full action. The cap depends on w,
not on the volume, selected link or cutoff K above headCutoff(w). -/
theorem insertedNormalizer_weighted_norm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    weightedPair (blocks extent-1) (exterior w K extent link hl)
      (insertedNormalizer w K extent link hl p) (insertedNormalizer w K extent link hl p) ≤
    upperFactor w * weightedPair (blocks extent)
      (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)) p p := by
  let W := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
  let N := insertedNormalizer w K extent link hl p
  let R := headProbe (linkHeadSwap extent link hl) N
  let x := weightedPair (blocks extent-1) (exterior w K extent link hl) N N
  let A := weightedPair (blocks extent) W p p
  have hN : SupportedQuaternionBlocks (blocks extent-1) N :=
    insertedNormalizer_supported w K extent link hl p hp
  have hR : SupportedQuaternionBlocks (blocks extent) R := headProbe_supported _ _
  have hW : Certificate (blocks extent) W :=
    headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ hi => hi)
  have hA : (0 : Q') ≤ A := hW.square_insertion_nonnegative p hp
  have he : weightedPair (blocks extent) W R p ≈ x :=
    insertedNormalizer_pair_pin w K extent link hl N p hN hp
  have hsq : weightedPair (blocks extent) W R p * weightedPair (blocks extent) W R p ≈ x*x :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he) (Q'.mul_eqv_congr_left _ _ _ he)
  have hcs := weighted_cauchySchwarz (blocks extent) W R p hW hR hp
  have hscaled : weightedPair (blocks extent) W R R * A ≤ (upperFactor w*x)*A :=
    Q'.mul_le_mul_of_nonneg_right _ _ A
      (headProbe_full_norm_bound hw0 hw1 K extent hK link hl N hN) hA
  have hproduct : x*x ≤ x*(upperFactor w*A) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsq)
      (Q'.le_trans' _ _ _ hcs
        (Q'.le_trans' _ _ _ hscaled
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) (mul_pull _ _ _)))))
  change x ≤ upperFactor w*A
  by_cases hx : (0 : Q') < x
  · exact q_cancel_left hx hproduct
  · have hnum : x.num ≤ (0 : Int) :=
      Int.not_lt.mp (fun h => hx ((zero_lt_iff_num_pos x).mpr h))
    have hx0 : x ≤ (0 : Q') := by
      change x.num * (1 : Int) ≤ (0 : Int) * (x.den : Int)
      simpa only [Int.mul_one, Int.zero_mul] using hnum
    exact Q'.le_trans' _ _ _ hx0 (Q'.mul_nonneg _ _ (Q'.le_of_lt (upperFactor_positive hw0)) hA)

end YMGap.Continuum.BF4ExactSlabStarInsertedNumerator

#print axioms YMGap.Continuum.BF4ExactSlabStarInsertedNumerator.insertedNormalizer_supported
#print axioms YMGap.Continuum.BF4ExactSlabStarInsertedNumerator.insertedNormalizer_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabStarInsertedNumerator.headProbe_full_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabStarInsertedNumerator.insertedNormalizer_weighted_norm
