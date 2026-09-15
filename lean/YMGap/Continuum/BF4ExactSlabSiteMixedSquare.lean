/-
# Mixed site forms retain the ORIGINAL shared-slice heat weight

For two arbitrary supported one-sided polynomials, conditional Haar
integration gives H(theta(p)*q*W)=H(C(p)*C(q)*W). The original fixed-slice
weight W is retained inside the same integral. Dressing both arguments with
the actual lower heat action then identifies the FULL original mixed site
form with this weighted boundary pairing, at every cutoff and extent.

These are exact rational identities, not a supplied positivity or range
hypothesis. They provide the mixed, not only diagonal, input for weighted
Cauchy--Schwarz. Time zero and the continuum/all-group Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabSiteHeatAction

namespace YMGap.Continuum.BF4ExactSlabSiteMixedSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteHeatAction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

private def weightedPair (blocks : Nat) (W p q : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul (polyMul p q) W)

private theorem weighted_add_left (blocks : Nat) (W a b c : RatPoly) :
    weightedPair blocks W (polyAdd a b) c ≈ weightedPair blocks W a c + weightedPair blocks W b c := by
  unfold weightedPair
  rw [polyMul_add_left_exact, polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

private theorem weighted_add_right (blocks : Nat) (W a b c : RatPoly) :
    weightedPair blocks W a (polyAdd b c) ≈ weightedPair blocks W a b + weightedPair blocks W a c := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks ((RatPolyCoeffEqv.mul_add_right a b c).mul_right W)) ?_
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

private theorem weighted_zero_right (blocks : Nat) (W p : RatPoly) : weightedPair blocks W p polyZero ≈ 0 :=
  haar_of_coeff_eqv blocks ((RatPolyCoeffEqv.mul_zero_right p).mul_right W)

private theorem weighted_separated_pair {radius : Nat} {W p q b c : RatPoly}
    (hW : SupportedQuaternionBlocks (blockCount radius) W) (lW : Local radius .fixed W)
    (hp : SupportedQuaternionBlocks (blockCount radius) p) (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hb : SupportedQuaternionBlocks (blockCount radius) b) (hc : SupportedQuaternionBlocks (blockCount radius) c)
    (lp : Local radius .lower p) (lq : Local radius .lower q)
    (lb : Local radius .fixed b) (lc : Local radius .fixed c) :
    weightedPair (blockCount radius) W
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) b) (polyMul q c) ≈
    weightedPair (blockCount radius) W
      (polySmul (quaternionHaar (blockCount radius) p) b) (polySmul (quaternionHaar (blockCount radius) q) c) := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    ((RatPolyCoeffEqv.mul_assoc _ _ W).trans (RatPolyCoeffEqv.mul_left _ (RatPolyCoeffEqv.mul_assoc q c W)))) ?_
  exact Q'.eqv_trans _ _ _
    (separated_pair hp hq hb (supported_polyMul hc hW) lp lq lb (lc.mul lW))
    (Q'.eqv_symm (haar_of_coeff_eqv _
      ((RatPolyCoeffEqv.mul_assoc _ _ W).trans (RatPolyCoeffEqv.mul_left _ (RatPolyCoeffEqv.polyMul_smul_left _ c W)))))

section FiniteSum

variable {A : Type} (radius : Nat) (W : RatPoly)
  (hW : SupportedQuaternionBlocks (blockCount radius) W) (lW : Local radius .fixed W)
  (lower boundary : A → RatPoly)
  (hl : ∀ a, SupportedQuaternionBlocks (blockCount radius) (lower a))
  (hb : ∀ a, SupportedQuaternionBlocks (blockCount radius) (boundary a))
  (ll : ∀ a, Local radius .lower (lower a)) (lb : ∀ a, Local radius .fixed (boundary a))

include hW lW hl hb ll lb in
private theorem weighted_row (a : A) : ∀ ys : List A,
    weightedPair (blockCount radius) W
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lower a)) (boundary a)) (lowerSum lower boundary ys) ≈
    weightedPair (blockCount radius) W
      (polySmul (quaternionHaar (blockCount radius) (lower a)) (boundary a)) (boundarySum radius lower boundary ys)
  | [] => Q'.eqv_trans _ _ _ (weighted_zero_right _ _ _) (Q'.eqv_symm (weighted_zero_right _ _ _))
  | b::ys => Q'.eqv_trans _ _ _ (weighted_add_right _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (weighted_separated_pair hW lW (hl a) (hl b) (hb a) (hb b) (ll a) (ll b) (lb a) (lb b))
        (weighted_row a ys)) (Q'.eqv_symm (weighted_add_right _ _ _ _ _)))

include hW lW hl hb ll lb in
private theorem weighted_sum_pairing : ∀ xs ys : List A,
    weightedPair (blockCount radius) W (upperSum radius lower boundary xs) (lowerSum lower boundary ys) ≈
    weightedPair (blockCount radius) W (boundarySum radius lower boundary xs) (boundarySum radius lower boundary ys)
  | [], _ => Q'.eqv_refl _
  | a::xs, ys => Q'.eqv_trans _ _ _ (weighted_add_left _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (weighted_row radius W hW lW lower boundary hl hb ll lb a ys)
        (weighted_sum_pairing xs ys)) (Q'.eqv_symm (weighted_add_left _ _ _ _ _)))

end FiniteSum

/-- Signed mixed terms and the original shared-slice weight are retained. -/
theorem conditional_weighted_pair (radius : Nat) (p q W : RatPoly)
    (lp : OneSided radius p) (lq : OneSided radius q)
    (_hp : SupportedQuaternionBlocks (blockCount radius) p) (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hW : SupportedQuaternionBlocks (blockCount radius) W) (lW : Local radius .fixed W) :
    quaternionHaar (blockCount radius) (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q) W) ≈
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (conditionalPolynomial radius p lp) (conditionalPolynomial radius q lq)) W) := by
  let xs := pieces radius p lp
  let ys := pieces radius q lq
  let Q := lowerSum lowerFactor boundaryFactor ys
  have hl := fun t : OneSidedTerm radius => masked_supported radius .lower t.term.1 t.term.2
  have hb := fun t : OneSidedTerm radius => masked_supported radius .fixed t.term.1 1
  have ll := fun t : OneSidedTerm radius => masked_local radius .lower t.term.1 t.term.2
  have lb := fun t : OneSidedTerm radius => masked_local radius .fixed t.term.1 1
  have hQ : SupportedQuaternionBlocks (blockCount radius) Q := lowerSum_supported radius lowerFactor boundaryFactor hl hb ys
  have hi := prefix_symm (pieces_pin radius p lp)
  have hj := prefix_symm (pieces_pin radius q lq)
  have hr := (QuaternionPrefixPolynomialEqv.reindex
    (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius)) hi).signSelected
    (correctedSlabTimeVectorCoordinate (adjacentEvenExtent radius))
  have he := (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.of_prefix (hr.mul hj)) (.refl _ W)).haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq) hW)
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hQ) hW)
  have hR := lowerSum_reflection radius lowerFactor boundaryFactor (fun t => boundary_reflection (lb t)) xs
  have hf := (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.mul hR (.refl _ Q)) (.refl _ W)).haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hQ) hW)
    (supported_polyMul (supported_polyMul (upperSum_supported radius lowerFactor boundaryFactor hb xs) hQ) hW)
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hf
    (weighted_sum_pairing radius W hW lW lowerFactor boundaryFactor hl hb ll lb xs ys))

theorem fullAction_dressing_pair (w : Q') (K radius : Nat) (p q : RatPoly) :
    PaddedPolynomialCoeffEqv (blockCount radius)
      (polyMul (polyMul
        (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (polyMul p (lowerHeat w K radius)))
        (polyMul q (lowerHeat w K radius))) (fixedHeat w K radius))
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q) (fullHeat w K radius)) := by
  have hR := (show ReflectionImage (adjacentEvenExtent radius) p
    (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) from .refl _ _).mul (lowerHeat_reflection w K radius)
  refine (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.mul hR (.refl _ _)) (.refl _ _)).trans ?_
  apply PaddedPolynomialCoeffEqv.of_coeff
  exact (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (by decide)
    (fun | 0 => reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p
         | 1 => q | 2 => lowerHeat w K radius | 3 => fixedHeat w K radius | _ => upperHeat w K radius)).trans
    ((fullHeat_split w K radius).symm.mul_left _)

/-- The computed boundary pair is exactly the FULL original site form. -/
theorem fullAction_pair (w : Q') (K radius : Nat) (p q : RatPoly)
    (lp : OneSided radius p) (lq : OneSided radius q)
    (hp : SupportedQuaternionBlocks (blockCount radius) p) (hq : SupportedQuaternionBlocks (blockCount radius) q) :
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q) (fullHeat w K radius)) ≈
    quaternionHaar (blockCount radius)
      (polyMul (polyMul
        (conditionalPolynomial radius (polyMul p (lowerHeat w K radius)) (lp.mul (lowerHeat_oneSided w K radius)))
        (conditionalPolynomial radius (polyMul q (lowerHeat w K radius)) (lq.mul (lowerHeat_oneSided w K radius))))
        (fixedHeat w K radius)) := by
  have hP := supported_polyMul hp (lowerHeat_supported w K radius)
  have hQ := supported_polyMul hq (lowerHeat_supported w K radius)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm ((fullAction_dressing_pair w K radius p q).haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hQ) (fixedHeat_supported w K radius))
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq) (fullHeat_supported w K radius))))
    (conditional_weighted_pair radius _ _ _ (lp.mul (lowerHeat_oneSided w K radius)) (lq.mul (lowerHeat_oneSided w K radius))
      hP hQ (fixedHeat_supported w K radius) (fixedHeat_local w K radius))

end YMGap.Continuum.BF4ExactSlabSiteMixedSquare

#print axioms YMGap.Continuum.BF4ExactSlabSiteMixedSquare.conditional_weighted_pair
#print axioms YMGap.Continuum.BF4ExactSlabSiteMixedSquare.fullAction_dressing_pair
#print axioms YMGap.Continuum.BF4ExactSlabSiteMixedSquare.fullAction_pair
