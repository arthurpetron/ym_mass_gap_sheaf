/-
# The actual centered seed family approximates the same marginal observable

Sum the certified finite defects on all retained coordinates, use the exact
Haar telescope pin, and cancel the positive floor of the ORIGINAL density.
This gives a computed degree for H[nu*(sum q_i-Phi)^2] <= epsilon.
The norm retains nu; neither an independent product density nor a normalized
surrogate is substituted. The finite cap may grow with every regulator.

This is approximation, not a signed-cost estimate or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation
import YMGap.Continuum.QuaternionHaarFiniteSquareBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
  (lower lower_positive lowerCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed (rate rate_nonnegative rate_lt_one defect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation (pieceDefectSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (piece)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
  (defectSum rawError rawError_supported density_error_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels labels_lt)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)
open YMGap.Continuum.QuaternionHaarFiniteSquareBudget
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation (weighted_norm_floor)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem cancel_floor {a c ell : Q'} (hell : (0 : Q') < ell)
    (h : ell*a ≤ c) : a ≤ Q'.recipPos ell hell*c := by
  have hi : ell*(Q'.recipPos ell hell*c) ≈ c :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ c (Q'.mul_recipPos_eqv ell hell))
        (Q'.one_mul_eqv c))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm hi))) hell

private theorem move_scale (a r C : Q') : a*(r*C) ≈ r*(a*C) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => a | 1 => r | _ => C)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

def defectBudget (f : RatPoly) : Q' :=
  sumCap (fun i => BF4ExactSlabFixedSpatialSeedApproximation.prefactor hw0 hw1 K width hK n
    (polynomialCap (piece w K width n i f))) (labels width)

theorem defectBudget_nonnegative (f : RatPoly) :
    (0 : Q') ≤ defectBudget hw0 hw1 K width hK n f :=
  sumCap_nonnegative _ _ (fun _ _ =>
    BF4ExactSlabFixedSpatialSeedApproximation.prefactor_nonnegative hw0 hw1 K width hK n _)

def defectSumSquareBound (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SquareBound (N width) (defectSum hw0 hw1 K width hK n k f)
      (((rate hw0 hw1 K width hK n)^k * (rate hw0 hw1 K width hK n)^k) *
        defectBudget hw0 hw1 K width hK n f) :=
  SquareBound.changeCap (sumCap_scale _ _ _)
    (sumSquareBound
      (fun i => defect hw0 hw1 K width hK n i k (piece w K width n i f)) _ (labels width)
      (fun i hi => pieceDefectSquareBound hw0 hw1 K width hK n i (labels_lt width i hi) k hf))

/-- Only one additional power of the density floor is lost in this SAME
weighted norm. This is a finite approximation constant, not a gap rate. -/
def prefactor (f : RatPoly) : Q' :=
  Q'.recipPos (lower w K width n) (lower_positive hw0 hw1 K width hK n) *
    defectBudget hw0 hw1 K width hK n f

theorem prefactor_nonnegative (f : RatPoly) :
    (0 : Q') ≤ prefactor hw0 hw1 K width hK n f :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ _))
    (defectBudget_nonnegative hw0 hw1 K width hK n f)

theorem rawError_weighted_square_bound (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (polyMul (rawError hw0 hw1 K width hK n k f) (rawError hw0 hw1 K width hK n k f))) ≤
      ((rate hw0 hw1 K width hK n)^k * (rate hw0 hw1 K width hK n)^k) *
        prefactor hw0 hw1 K width hK n f := by
  have h := weighted_norm_floor (rawError_supported hw0 hw1 K width hK n k hf)
    (lower_positive hw0 hw1 K width hK n) (lowerCertificate hw0 hw1 K width hK n)
  have hsum := Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (density_error_square hw0 hw1 K width hK n k hf))
      (squareHaar (defectSumSquareBound hw0 hw1 K width hK n k hf)))
  exact Q'.le_trans' _ _ _ (cancel_floor (lower_positive hw0 hw1 K width hK n) hsum)
    (Q'.le_of_eqv (move_scale _ _ _))

theorem rawError_weighted_square_le_geometric (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (polyMul (rawError hw0 hw1 K width hK n k f) (rawError hw0 hw1 K width hK n k f))) ≤
      (rate hw0 hw1 K width hK n)^k * prefactor hw0 hw1 K width hK n f := by
  have h0 := Q'.pow_nonneg _ (rate_nonnegative hw0 hw1 K width hK n) k
  have h1 := HKPos.pow_le_one (rate_nonnegative hw0 hw1 K width hK n)
    (Q'.le_of_lt (rate_lt_one hw0 hw1 K width hK n)) k
  have hs : (rate hw0 hw1 K width hK n)^k * (rate hw0 hw1 K width hK n)^k ≤
      (rate hw0 hw1 K width hK n)^k :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h1 h0)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (rawError_weighted_square_bound hw0 hw1 K width hK n k hf)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hs (prefactor_nonnegative hw0 hw1 K width hK n f))

def approximationCutoff (f : RatPoly) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (rate hw0 hw1 K width hK n)
    (prefactor hw0 hw1 K width hK n f) epsilon

theorem rawError_weighted_square_le {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : approximationCutoff hw0 hw1 K width hK n f epsilon ≤ k) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (polyMul (rawError hw0 hw1 K width hK n k f) (rawError hw0 hw1 K width hK n k f))) ≤ epsilon :=
  Q'.le_trans' _ _ _ (rawError_weighted_square_le_geometric hw0 hw1 K width hK n k hf)
    (PositiveContractionResidual.geometric_bound (rate_nonnegative hw0 hw1 K width hK n)
      (rate_lt_one hw0 hw1 K width hK n) (prefactor_nonnegative hw0 hw1 K width hK n f)
      hepsilon k hk)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.defectBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.defectBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.defectSumSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.prefactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.prefactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.rawError_weighted_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.rawError_weighted_square_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.approximationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation.rawError_weighted_square_le
