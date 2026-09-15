/-
# Retaining the shared-slice weight in the actual conditional Haar square

For every supported one-sided polynomial p and supported boundary-local W,
the ORIGINAL even-slab Haar law satisfies

    H((theta(p) * p) * W) = H((C(p) * C(p)) * W).

The identity is linear in W and needs no positivity assumption. An existing
Haar square certificate for W then proves nonnegativity. In particular, the
certificate's individual square features need not be boundary-local: only
the original weight W must be. All mixed terms and shared links are retained.

This removes the unweighted restriction of the conditional-square theorem.
Identifying the full original heat action and its thermodynamic one-step
pairing remains separate. No geometric T1 positivity, range density, time-zero
modulus, physical mass or continuum/Clay closure is claimed here.
-/

import YMGap.Continuum.BF4ExactSlabSiteConditionalSquare

namespace YMGap.Continuum.BF4ExactSlabSiteWeightedSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
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
    weightedPair blocks W (polyAdd a b) c ≈
      weightedPair blocks W a c + weightedPair blocks W b c := by
  unfold weightedPair
  rw [polyMul_add_left_exact, polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

private theorem weighted_add_right (blocks : Nat) (W a b c : RatPoly) :
    weightedPair blocks W a (polyAdd b c) ≈
      weightedPair blocks W a b + weightedPair blocks W a c := by
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff_eqv blocks ((RatPolyCoeffEqv.mul_add_right a b c).mul_right W)) ?_
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

private theorem weighted_zero_right (blocks : Nat) (W p : RatPoly) :
    weightedPair blocks W p polyZero ≈ 0 :=
  haar_of_coeff_eqv blocks ((RatPolyCoeffEqv.mul_zero_right p).mul_right W)

private theorem weighted_separated_pair {radius : Nat} {W p q b c : RatPoly}
    (hW : SupportedQuaternionBlocks (blockCount radius) W) (lW : Local radius .fixed W)
    (hp : SupportedQuaternionBlocks (blockCount radius) p)
    (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hb : SupportedQuaternionBlocks (blockCount radius) b)
    (hc : SupportedQuaternionBlocks (blockCount radius) c)
    (lp : Local radius .lower p) (lq : Local radius .lower q)
    (lb : Local radius .fixed b) (lc : Local radius .fixed c) :
    weightedPair (blockCount radius) W
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) b) (polyMul q c) ≈
    weightedPair (blockCount radius) W
      (polySmul (quaternionHaar (blockCount radius) p) b)
      (polySmul (quaternionHaar (blockCount radius) q) c) := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    ((RatPolyCoeffEqv.mul_assoc _ _ W).trans
      (RatPolyCoeffEqv.mul_left _ (RatPolyCoeffEqv.mul_assoc q c W)))) ?_
  exact Q'.eqv_trans _ _ _
    (separated_pair hp hq hb (supported_polyMul hc hW) lp lq lb (lc.mul lW))
    (Q'.eqv_symm (haar_of_coeff_eqv _
      ((RatPolyCoeffEqv.mul_assoc _ _ W).trans
        (RatPolyCoeffEqv.mul_left _ (RatPolyCoeffEqv.polyMul_smul_left _ c W)))))

section FiniteSum

variable {A : Type} (radius : Nat) (W : RatPoly)
  (hW : SupportedQuaternionBlocks (blockCount radius) W) (lW : Local radius .fixed W)
  (lower boundary : A → RatPoly)
  (hl : ∀ a, SupportedQuaternionBlocks (blockCount radius) (lower a))
  (hb : ∀ a, SupportedQuaternionBlocks (blockCount radius) (boundary a))
  (ll : ∀ a, Local radius .lower (lower a))
  (lb : ∀ a, Local radius .fixed (boundary a))

include hW lW hl hb ll lb in
private theorem weighted_row (a : A) : ∀ ys : List A,
    weightedPair (blockCount radius) W
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lower a)) (boundary a))
      (lowerSum lower boundary ys) ≈
    weightedPair (blockCount radius) W
      (polySmul (quaternionHaar (blockCount radius) (lower a)) (boundary a))
      (boundarySum radius lower boundary ys)
  | [] => Q'.eqv_trans _ _ _ (weighted_zero_right _ _ _) (Q'.eqv_symm (weighted_zero_right _ _ _))
  | b :: ys => Q'.eqv_trans _ _ _ (weighted_add_right _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (weighted_separated_pair hW lW (hl a) (hl b) (hb a) (hb b) (ll a) (ll b) (lb a) (lb b))
        (weighted_row a ys)) (Q'.eqv_symm (weighted_add_right _ _ _ _ _)))

include hW lW hl hb ll lb in
private theorem weighted_sum_pairing : ∀ xs ys : List A,
    weightedPair (blockCount radius) W
      (upperSum radius lower boundary xs) (lowerSum lower boundary ys) ≈
    weightedPair (blockCount radius) W
      (boundarySum radius lower boundary xs) (boundarySum radius lower boundary ys)
  | [], _ => Q'.eqv_refl _
  | a :: xs, ys => Q'.eqv_trans _ _ _ (weighted_add_left _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (weighted_row radius W hW lW lower boundary hl hb ll lb a ys)
        (weighted_sum_pairing xs ys)) (Q'.eqv_symm (weighted_add_left _ _ _ _ _)))

end FiniteSum

/-- The original boundary weight stays inside the same Haar integral. -/
theorem conditional_weighted_square (radius : Nat) (p W : RatPoly)
    (hp : OneSided radius p) (hs : SupportedQuaternionBlocks (blockCount radius) p)
    (hW : SupportedQuaternionBlocks (blockCount radius) W) (lW : Local radius .fixed W) :
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) W) ≈
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (conditionalPolynomial radius p hp) (conditionalPolynomial radius p hp)) W) := by
  let xs := pieces radius p hp
  let P := lowerSum lowerFactor boundaryFactor xs
  have hl := fun t : OneSidedTerm radius => masked_supported radius .lower t.term.1 t.term.2
  have hb := fun t : OneSidedTerm radius => masked_supported radius .fixed t.term.1 1
  have ll := fun t : OneSidedTerm radius => masked_local radius .lower t.term.1 t.term.2
  have lb := fun t : OneSidedTerm radius => masked_local radius .fixed t.term.1 1
  have hP : SupportedQuaternionBlocks (blockCount radius) P :=
    lowerSum_supported radius lowerFactor boundaryFactor hl hb xs
  have hi := prefix_symm (pieces_pin radius p hp)
  have hr := (QuaternionPrefixPolynomialEqv.reindex
    (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius)) hi).signSelected
    (correctedSlabTimeVectorCoordinate (adjacentEvenExtent radius))
  have he := (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.of_prefix (hr.mul hi))
    (.refl _ W)).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs) hW)
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hP) hW)
  have hR := lowerSum_reflection radius lowerFactor boundaryFactor
    (fun t => boundary_reflection (lb t)) xs
  have hf := (PaddedPolynomialCoeffEqv.mul
    (PaddedPolynomialCoeffEqv.mul hR (.refl _ P)) (.refl _ W)).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hP) hW)
      (supported_polyMul
        (supported_polyMul (upperSum_supported radius lowerFactor boundaryFactor hb xs) hP) hW)
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hf
    (weighted_sum_pairing radius W hW lW lowerFactor boundaryFactor hl hb ll lb xs xs))

/-- Positivity is supplied by a constructed certificate for the original W,
not an asserted positive form or boundary-locality of its square features. -/
theorem certified_weighted_nonnegative (radius : Nat) (p W : RatPoly)
    (hp : OneSided radius p) (hs : SupportedQuaternionBlocks (blockCount radius) p)
    (hW : SupportedQuaternionBlocks (blockCount radius) W) (lW : Local radius .fixed W)
    (cert : Certificate (blockCount radius) W) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) W) :=
  Q'.le_trans' _ _ _
    (cert.square_insertion_nonnegative _ (conditional_supported radius p hp))
    (Q'.ge_of_eqv (conditional_weighted_square radius p W hp hs hW lW))

end YMGap.Continuum.BF4ExactSlabSiteWeightedSquare

#print axioms YMGap.Continuum.BF4ExactSlabSiteWeightedSquare.conditional_weighted_square
#print axioms YMGap.Continuum.BF4ExactSlabSiteWeightedSquare.certified_weighted_nonnegative
