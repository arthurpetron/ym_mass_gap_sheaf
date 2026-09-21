/-
# The actual Ward response of a gradient test is a nonnegative energy

The selected-link derivative is evaluated in its original head-link frame.
Every complementary heat factor is retained, and normalization uses the
same original full partition for every selected link. The gradient pin is
an arbitrary-insertion Haar equality, so padded reindexing is not silently
identified with raw polynomial equality. This is ordinary Haar energy;
no positive response floor, OS norm or continuum estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabWardFamilyCost

namespace YMGap.Continuum.BF4ExactSlabWardGradientEnergy

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
open YMGap.Continuum.BF4ExactSlabLocalHaarWard
open YMGap.Continuum.BF4ExactSlabLocalWardVariance
open YMGap.Continuum.BF4ExactSlabOriginalWardLocality
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

private theorem first_neg_of_sum_zero (x y : Q') (h : x+y ≈ 0) : x ≈ -y := by
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 0) (.var 1)) (by decide) (fun n => if n = 0 then x else y)) h

variable (w : Q') (K extent : Nat) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)
local notation "swap" => linkHeadSwap extent link hl
local notation "A" => reindexQuaternionPolynomial swap (incidentHeat w K extent link)
local notation "R" => reindexQuaternionPolynomial swap (complementHeat w K extent link)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)

/-- The full-action energy numerator, with the extra incident factor forced
by the polynomial Ward score. It is not a deleted-action expectation. -/
def energyNumerator (i j : Nat) (f : RatPoly) : Q' :=
  let df := angularDerivative i j (reindexQuaternionPolynomial swap f)
  quaternionHaar (blocks extent) (polyMul R (polyMul A (polyMul A (polyMul df df))))

/-- Each link uses the identical ORIGINAL full partition. -/
def linkEnergy (i j : Nat) (f : RatPoly)
    (hW : (0 : Q') < quaternionHaar (blocks extent) W) : Q' :=
  energyNumerator w K extent link hl i j f * Q'.recipPos (quaternionHaar (blocks extent) W) hW

/-- A proved gradient pin turns the original score response into the negative
of its actual energy. No positivity or response lower estimate is assumed. -/
theorem originalScore_energy_pair {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f)
    (hg : HaarCarrierEqv (blocks extent) (reindexQuaternionPolynomial swap g)
      (angularDerivative i j (reindexQuaternionPolynomial swap f))) :
    quaternionHaar (blocks extent)
      (polyMul (polyMul f (originalScore w K extent link hl i j g)) W) ≈
      -(energyNumerator w K extent link hl i j f) := by
  let f' := reindexQuaternionPolynomial swap f
  let g' := reindexQuaternionPolynomial swap g
  let df := angularDerivative i j f'
  let p := polyMul f' (localScore w K extent link hl i j g')
  let q := polyMul (polyMul A g') df
  have hs : quaternionHaar (blocks extent) (polyMul R (polyMul A (polyAdd p q))) ≈
      quaternionHaar (blocks extent) (polyMul R (polyMul A p)) +
      quaternionHaar (blocks extent) (polyMul R (polyMul A q)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      (((RatPolyCoeffEqv.mul_add_right A p q).mul_left R).trans
        (RatPolyCoeffEqv.mul_add_right R _ _)))
      (quaternionHaar_append (blocks extent) _ _)
  have he : quaternionHaar (blocks extent) (polyMul R (polyMul A q)) ≈
      energyNumerator w K extent link hl i j f :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      (((RatPolyCoeffEqv.mul_assoc A g' df).mul_left A).mul_left R))
      (haar_of_carrier (HaarCarrierEqv.mul_left R (HaarCarrierEqv.mul_left A
        (HaarCarrierEqv.mul_left A (HaarCarrierEqv.mul_right df hg)))))
  have hz := Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
    (fullAction_score_identity w K extent link hl hi hj g' f')
  have hraw : quaternionHaar (blocks extent)
      (polyMul (polyMul f (originalScore w K extent link hl i j g)) W) +
      energyNumerator w K extent link hl i j f ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (originalScore_pair_pin w K extent link hl hi hj g f hf) (Q'.eqv_symm he)) hz
  exact first_neg_of_sum_zero _ _ hraw

/-- The normalized response and energy still share the same original W. -/
theorem normalized_pair_energy {i j : Nat} (hi : i < 4) (hj : j < 4)
    (g f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f)
    (hg : HaarCarrierEqv (blocks extent) (reindexQuaternionPolynomial swap g)
      (angularDerivative i j (reindexQuaternionPolynomial swap f)))
    (hW : (0 : Q') < quaternionHaar (blocks extent) W) :
    normalizedMoment (blocks extent) W (polyMul f (originalScore w K extent link hl i j g)) hW ≈
      -(linkEnergy w K extent link hl i j f hW) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm W _))
      (originalScore_energy_pair w K extent link hl hi hj g f hf hg)))
    (Q'.neg_mul_eqv _ _)

/-- The actual energy numerator is nonnegative at the explicit heat cutoff.
This does not assert a positive floor for a chosen nonconstant observable. -/
theorem energyNumerator_nonnegative (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4) (f : RatPoly) :
    (0 : Q') ≤ energyNumerator w K extent link hl i j f := by
  have hA := reindex_certificate swap (incidentHeat_supported w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (incidentIds extent link)
      (fun _ h => incidentIds_physical h))
  have hR := reindex_certificate swap (complementHeat_supported w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ h => complementIds_physical h))
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  exact (hR.mul (hA.mul (hA.mul (.square _
    (angularDerivative_supported hb hi hj (reindex_supported swap f)))))).haar_nonnegative

theorem linkEnergy_nonnegative (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4) (f : RatPoly)
    (hW : (0 : Q') < quaternionHaar (blocks extent) W) :
    (0 : Q') ≤ linkEnergy w K extent link hl i j f hW :=
  Q'.mul_nonneg _ _ (energyNumerator_nonnegative w K extent link hl hw0 hw1 hK hi hj f)
    (Q'.le_of_lt (Q'.recipPos_pos _ hW))

end YMGap.Continuum.BF4ExactSlabWardGradientEnergy

#print axioms YMGap.Continuum.BF4ExactSlabWardGradientEnergy.originalScore_energy_pair
#print axioms YMGap.Continuum.BF4ExactSlabWardGradientEnergy.normalized_pair_energy
#print axioms YMGap.Continuum.BF4ExactSlabWardGradientEnergy.energyNumerator_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabWardGradientEnergy.linkEnergy_nonnegative
