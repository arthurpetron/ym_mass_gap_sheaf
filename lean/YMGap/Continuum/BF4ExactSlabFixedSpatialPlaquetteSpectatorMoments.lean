/-
# One-edge spectator moments of the literal spatial plaquette

The fundamental plaquette character has zero first moment and unit second
moment against any supported polynomial independent of one of its four links.
The same exact Haar identities determine the shifted-square and original
inverse-heat dual/source moments with that spectator.  No positivity or
normalization of the spectator is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (character_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment (character_pair_moment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive (source dualTest)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost (inverseRate)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

/-- A single absent face edge kills the character's Haar moment, with the
entire supported spectator retained. -/
theorem plaquette_first_moment {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (R : RatPoly) (hR : SupportedQuaternionBlocks (N width) R)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) R) :
    quaternionHaar (N width)
      (polyMul (characterPolynomial (plaquette width face).scalar 1) R) ≈ 0 :=
  character_haar_zero hf l hl 1 (by decide) R hR hi

/-- The square of the same character has the spectator's exact Haar mass. -/
theorem plaquette_second_moment {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (R : RatPoly) (hR : SupportedQuaternionBlocks (N width) R)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) R) :
    quaternionHaar (N width)
      (polyMul
        (polyMul (characterPolynomial (plaquette width face).scalar 1)
          (characterPolynomial (plaquette width face).scalar 1)) R) ≈
      quaternionHaar (N width) R := by
  simpa using character_pair_moment hf l hl R hR hi 1

private theorem weighted_add_right (blocks : Nat) (W a b c : RatPoly) :
    weightedPair blocks W a (polyAdd b c) ≈
      weightedPair blocks W a b + weightedPair blocks W a c :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks W a (polyAdd b c))
    (Q'.eqv_trans _ _ _ (weighted_add_left blocks W b c a)
      (Q'.add_eqv_congr' (weighted_symm blocks W b a)
        (weighted_symm blocks W c a)))

private theorem weighted_smul_right (blocks : Nat) (W : RatPoly)
    (c : Q') (p q : RatPoly) :
    weightedPair blocks W p (polySmul c q) ≈
      c * weightedPair blocks W p q :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks W p (polySmul c q))
    (Q'.eqv_trans _ _ _ (weighted_smul_left blocks W c q p)
      (Q'.mul_eqv_congr_left c _ _ (weighted_symm blocks W q p)))

private theorem affine_pair (blocks : Nat) (W p q : RatPoly)
    (a b c d : Q') :
    weightedPair blocks W
        (polyAdd (polySmul a p) (polySmul b q))
        (polyAdd (polySmul c p) (polySmul d q)) ≈
      a * (c * weightedPair blocks W p p + d * weightedPair blocks W p q) +
        b * (c * weightedPair blocks W q p + d * weightedPair blocks W q q) := by
  have hp : weightedPair blocks W p
      (polyAdd (polySmul c p) (polySmul d q)) ≈
      c * weightedPair blocks W p p + d * weightedPair blocks W p q :=
    Q'.eqv_trans _ _ _ (weighted_add_right blocks W p (polySmul c p) (polySmul d q))
      (Q'.add_eqv_congr' (weighted_smul_right blocks W c p p)
        (weighted_smul_right blocks W d p q))
  have hq : weightedPair blocks W q
      (polyAdd (polySmul c p) (polySmul d q)) ≈
      c * weightedPair blocks W q p + d * weightedPair blocks W q q :=
    Q'.eqv_trans _ _ _ (weighted_add_right blocks W q (polySmul c p) (polySmul d q))
      (Q'.add_eqv_congr' (weighted_smul_right blocks W c q p)
        (weighted_smul_right blocks W d q q))
  exact Q'.eqv_trans _ _ _
    (weighted_add_left blocks W (polySmul a p) (polySmul b q)
      (polyAdd (polySmul c p) (polySmul d q)))
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (weighted_smul_left blocks W a p
          (polyAdd (polySmul c p) (polySmul d q)))
        (Q'.mul_eqv_congr_left a _ _ hp))
      (Q'.eqv_trans _ _ _
        (weighted_smul_left blocks W b q
          (polyAdd (polySmul c p) (polySmul d q)))
        (Q'.mul_eqv_congr_left b _ _ hq)))

/-- Exact one-edge spectator moment for two affine character probes. -/
theorem affine_plaquette_pair_moment {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (R : RatPoly) (hR : SupportedQuaternionBlocks (N width) R)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) R)
    (a c m : Q') :
    weightedPair (N width) R
      (polyAdd (polySmul a (characterPolynomial (plaquette width face).scalar 1))
        (polySmul (-m) polyOne))
      (polyAdd (polySmul c (characterPolynomial (plaquette width face).scalar 1))
        (polySmul (-m) polyOne)) ≈
      (a*c + m*m) * quaternionHaar (N width) R := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let z := quaternionHaar (N width) R
  have hff : weightedPair (N width) R f f ≈ z :=
    plaquette_second_moment hf l hl R hR hi
  have hfo : weightedPair (N width) R f polyOne ≈ 0 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.mul_one f).mul_right R))
      (plaquette_first_moment hf l hl R hR hi)
  have hof : weightedPair (N width) R polyOne f ≈ 0 :=
    Q'.eqv_trans _ _ _ (weighted_symm (N width) R polyOne f) hfo
  have hoo : weightedPair (N width) R polyOne polyOne ≈ z :=
    haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right R).trans
      (RatPolyCoeffEqv.one_mul R))
  have hpair := affine_pair (N width) R f polyOne a (-m) c (-m)
  have hmom := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left a _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left c _ _ hff)
        (Q'.mul_eqv_congr_left (-m) _ _ hfo)))
    (Q'.mul_eqv_congr_left (-m) _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left c _ _ hof)
        (Q'.mul_eqv_congr_left (-m) _ _ hoo)))
  exact Q'.eqv_trans _ _ _ hpair (Q'.eqv_trans _ _ _ hmom
    (poly_identity_of_normal_eq
      (.add
        (.mul (.var 0)
          (.add (.mul (.var 1) (.var 3))
            (.mul (.neg (.var 2)) (.const 0))))
        (.mul (.neg (.var 2))
          (.add (.mul (.var 1) (.const 0))
            (.mul (.neg (.var 2)) (.var 3)))))
      (.mul (.add (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.var 2))) (.var 3))
      (by decide) (fun | 0 => a | 1 => c | 2 => m | _ => z)))

/-- The centered source has exact square mass `(1+m²) H[R]` even with
the full independent spectator, in its original multiplication order. -/
theorem shifted_square_moment {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (R : RatPoly) (hR : SupportedQuaternionBlocks (N width) R)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) R)
    (m : Q') :
    quaternionHaar (N width)
      (polyMul R (polyMul (source width face m) (source width face m))) ≈
      ((1 : Q') + m*m) * quaternionHaar (N width) R := by
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm R
      (polyMul (source width face m) (source width face m)))) ?_
  change weightedPair (N width) R (source width face m) (source width face m) ≈ _
  unfold source QuaternionHaarDensityVariance.shifted
  exact affine_plaquette_pair_moment hf l hl R hR hi 1 1 m

/-- The exact inverse-heat dual/source moment is `(w^(-12)+m²) H[R]`.
This is an identity for the literal original dual test and the same
one-edge-independent spectator, with no positivity assumption on `R`. -/
theorem dual_source_moment {w : Q'} (hw0 : (0 : Q') < w)
    {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (R : RatPoly) (hR : SupportedQuaternionBlocks (N width) R)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) R)
    (m : Q') :
    quaternionHaar (N width)
      (polyMul R (polyMul (dualTest hw0 width face m) (source width face m))) ≈
      (inverseRate hw0 + m*m) * quaternionHaar (N width) R := by
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm R
      (polyMul (dualTest hw0 width face m) (source width face m)))) ?_
  change weightedPair (N width) R (dualTest hw0 width face m)
    (source width face m) ≈ _
  let f := characterPolynomial (plaquette width face).scalar 1
  have hdual : dualTest hw0 width face m =
      polyAdd (polySmul (inverseRate hw0) f) (polySmul (-m) polyOne) := rfl
  have hsource : source width face m =
      polyAdd (polySmul 1 f) (polySmul (-m) polyOne) := rfl
  rw [hdual, hsource]
  have haff := affine_plaquette_pair_moment hf l hl R hR hi
    (inverseRate hw0) 1 m
  exact Q'.eqv_trans _ _ _ haff
    (Q'.mul_eqv_congr_right _ _ (quaternionHaar (N width) R)
      (Q'.add_eqv_congr' (Q'.mul_one_eqv (inverseRate hw0))
        (Q'.eqv_refl (m*m))))

#print axioms plaquette_first_moment
#print axioms plaquette_second_moment
#print axioms affine_plaquette_pair_moment
#print axioms shifted_square_moment
#print axioms dual_source_moment

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments
