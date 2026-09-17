/-
# Same-marginal approximation of the full corrected family sum

The error is exactly FamilyCost.correctedSum qs (constant k) minus the
raw sum of qs over the SAME active-plus-fringe labels. Its coefficient
pin to the component-error sum feeds the finite square-certificate budget.
The original odd marginal remains inside the final norm:
  H[nu*error^2] <= chi^(2*k) * u * sumCap(polynomialCap(q_i)^2).
A computable cutoff makes this finite norm arbitrarily small.

The cap retains the actual finite weight, list, and polynomial presentations.
No decomposition or signed-cost budget is supplied as a hypothesis, and no
uniformity over cutoff, width, boundary depth or spacing is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
import YMGap.Continuum.QuaternionHaarFiniteSquareBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow (upper upper_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed (marginalInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse
  (radius radius_nonnegative radius_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost (correctedTest_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost (corrected correctedSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (sum_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation
  (correctionDefect correctionDefectSquareBound)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarFiniteSquareBudget (sumCap sumCap_nonnegative sumCap_scale sumSquareBound)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks activeBlocks

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem sum_difference {A : Type} (f g : A → RatPoly) : ∀ ids : List A,
    RatPolyCoeffEqv (polyAdd (polySum (ids.map f)) (polyNeg (polySum (ids.map g))))
      (polySum (ids.map (fun i => polyAdd (f i) (polyNeg (g i)))))
  | [] => .refl _
  | i::ids =>
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
        (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
        (by decide) (fun
          | 0 => f i
          | 1 => polySum (ids.map f)
          | 2 => g i
          | _ => polySum (ids.map g))).trans
        ((RatPolyCoeffEqv.refl _).add (sum_difference f g ids))

private theorem weightedSquareHaar {blocks : Nat} {p m : RatPoly} {c u : Q'}
    (P : SquareBound blocks p c) (M : Certificate blocks m) (I : Interval blocks m u) :
    quaternionHaar blocks (polyMul m (polyMul p p)) ≤ u*c := by
  let S : Interval blocks (polyMul p p) c :=
    ⟨supported_polyMul P.support P.support, P.nonnegative, P.certificate,
      (Certificate.constant blocks c P.nonnegative).add (Certificate.square p P.support)⟩
  have hm : quaternionHaar blocks m ≤ u :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) I.haar_bound
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _ (S.weighted_haar_bound M)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ c hm P.nonnegative)
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

def rawSum (width : Nat) (qs : Nat → RatPoly) : RatPoly :=
  polySum ((labels width).map qs)

/-- Explicit finite-family square cap, including the original label order. -/
def squareBudget (width : Nat) (qs : Nat → RatPoly) : Q' :=
  sumCap (fun i => polynomialCap (qs i) * polynomialCap (qs i)) (labels width)

theorem squareBudget_nonnegative (width : Nat) (qs : Nat → RatPoly) :
    (0 : Q') ≤ squareBudget width qs :=
  sumCap_nonnegative _ _ (fun i _ => SumOfSquares.q_mul_self_nonneg (polynomialCap (qs i)))

def prefactor (w : Q') (K width n : Nat) (qs : Nat → RatPoly) : Q' :=
  upper w K width n * squareBudget width qs

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

def correctionError (qs : Nat → RatPoly) (k : Nat) : RatPoly :=
  polyAdd (correctedSum hw0 hw1 K width hK n qs (fun _ => k)) (polyNeg (rawSum width qs))

theorem correctionError_supported (qs : Nat → RatPoly) (k : Nat)
    (hq : ∀ i, i ∈ labels width → SupportedQuaternionBlocks (N width) (qs i)) :
    SupportedQuaternionBlocks (N width) (correctionError hw0 hw1 K width hK n qs k) := by
  unfold correctionError correctedSum rawSum
  refine supported_add (sum_supported _ _ ?_) (support_neg (sum_supported qs (labels width) hq))
  intro i hi
  unfold corrected
  by_cases ha : i ∈ activeBlocks width
  · rw [if_pos ha]
    exact correctedTest_supported hw0 hw1 K width hK n i (hq i hi) k
  · rw [if_neg ha]
    exact hq i hi

/-- Raw coefficient equality; no quotient or nullity strengthening is used. -/
theorem correctionError_pin (qs : Nat → RatPoly) (k : Nat) :
    RatPolyCoeffEqv (correctionError hw0 hw1 K width hK n qs k)
      (polySum ((labels width).map (correctionDefect hw0 hw1 K width hK n qs k))) :=
  sum_difference (corrected hw0 hw1 K width hK n qs (fun _ => k)) qs (labels width)

def correctionErrorSquareBound (qs : Nat → RatPoly) (k : Nat)
    (hq : ∀ i, i ∈ labels width → SupportedQuaternionBlocks (N width) (qs i)) :
    SquareBound (N width) (correctionError hw0 hw1 K width hK n qs k)
      (((radius hw0 hw1 K width hK n)^k * (radius hw0 hw1 K width hK n)^k) * squareBudget width qs) :=
  SquareBound.ofCoeff (correctionError_supported hw0 hw1 K width hK n qs k hq)
    (correctionError_pin hw0 hw1 K width hK n qs k)
    (SquareBound.changeCap (sumCap_scale _ _ _)
      (sumSquareBound (correctionDefect hw0 hw1 K width hK n qs k)
        (fun i => ((radius hw0 hw1 K width hK n)^k * (radius hw0 hw1 K width hK n)^k) *
          (polynomialCap (qs i) * polynomialCap (qs i))) (labels width)
        (fun i hi => correctionDefectSquareBound hw0 hw1 K width hK n qs k i (hq i hi))))

include hw0 hw1 hK in
theorem prefactor_nonnegative (qs : Nat → RatPoly) :
    (0 : Q') ≤ prefactor w K width n qs :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (upper_positive hw0 hw1 K width hK n)) (squareBudget_nonnegative width qs)

/-- Original-density norm of the exact corrected-sum error. -/
theorem correctionError_weighted_square_bound (qs : Nat → RatPoly) (k : Nat)
    (hq : ∀ i, i ∈ labels width → SupportedQuaternionBlocks (N width) (qs i)) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (polyMul (correctionError hw0 hw1 K width hK n qs k) (correctionError hw0 hw1 K width hK n qs k))) ≤
        (((radius hw0 hw1 K width hK n)^k * (radius hw0 hw1 K width hK n)^k) * prefactor w K width n qs) :=
  Q'.le_trans' _ _ _
    (weightedSquareHaar (correctionErrorSquareBound hw0 hw1 K width hK n qs k hq)
      (marginalCertificate hw0 hw1 K width hK n) (marginalInterval hw0 hw1 K width hK n))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => upper w K width n
           | 1 => (radius hw0 hw1 K width hK n)^k * (radius hw0 hw1 K width hK n)^k
           | _ => squareBudget width qs)))

theorem correctionError_weighted_square_le_geometric (qs : Nat → RatPoly) (k : Nat)
    (hq : ∀ i, i ∈ labels width → SupportedQuaternionBlocks (N width) (qs i)) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (polyMul (correctionError hw0 hw1 K width hK n qs k) (correctionError hw0 hw1 K width hK n qs k))) ≤
        (radius hw0 hw1 K width hK n)^k * prefactor w K width n qs := by
  have h0 := Q'.pow_nonneg _ (radius_nonnegative hw0 hw1 K width hK n) k
  have h1 := HKPos.pow_le_one (radius_nonnegative hw0 hw1 K width hK n)
    (Q'.le_of_lt (radius_lt_one hw0 hw1 K width hK n)) k
  have hs : (radius hw0 hw1 K width hK n)^k * (radius hw0 hw1 K width hK n)^k ≤
      (radius hw0 hw1 K width hK n)^k :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h1 h0)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (correctionError_weighted_square_bound hw0 hw1 K width hK n qs k hq)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hs (prefactor_nonnegative hw0 hw1 K width hK n qs))

def approximationCutoff (qs : Nat → RatPoly) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (radius hw0 hw1 K width hK n) (prefactor w K width n qs) epsilon

theorem correctionError_weighted_square_le (qs : Nat → RatPoly)
    (hq : ∀ i, i ∈ labels width → SupportedQuaternionBlocks (N width) (qs i))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : approximationCutoff hw0 hw1 K width hK n qs epsilon ≤ k) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (polyMul (correctionError hw0 hw1 K width hK n qs k) (correctionError hw0 hw1 K width hK n qs k))) ≤ epsilon :=
  Q'.le_trans' _ _ _ (correctionError_weighted_square_le_geometric hw0 hw1 K width hK n qs k hq)
    (PositiveContractionResidual.geometric_bound (radius_nonnegative hw0 hw1 K width hK n)
      (radius_lt_one hw0 hw1 K width hK n) (prefactor_nonnegative hw0 hw1 K width hK n qs) hepsilon k hk)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.rawSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.squareBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.squareBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.prefactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.correctionError
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.correctionError_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.correctionError_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.correctionErrorSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.prefactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.correctionError_weighted_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.correctionError_weighted_square_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.approximationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.correctionError_weighted_square_le
