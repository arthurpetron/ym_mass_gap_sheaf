/-
# The combined active and grouped-fringe cost on the same marginal

The active-only seeds and one whole fringe test recover the ORIGINAL
corrected sum. Their common-energy inequality pays (1-h) times the
squared norm of the signed fringe SUM, not its component diagonal sum.
All active--fringe cross terms stay inside the norm of the full sum.

No sign is assigned to the active determinant remainder. Bounding this
new combined cost uniformly remains open; approximation alone does not
provide such a bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeFlow
import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeFlow
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (familySeeds familySeeds_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation (approximant)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering (weightedResidual)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] spatialWeight baseLinks

private theorem pair_add (w : Q') (K width n : Nat) (f s r : RatPoly) :
    marginalPair w K width n f (polyAdd s r) ≈
      marginalPair w K width n f s + marginalPair w K width n f r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_add_right f s r).mul_left _))
    (haar_weighted_add (N width) (marginalWeight w K width n) _ _)

private theorem norm_add (w : Q') (K width n : Nat) (s r : RatPoly) :
    marginalPair w K width n (polyAdd s r) (polyAdd s r) ≈
      (marginalPair w K width n s s + marginalPair w K width n r r) +
        (marginalPair w K width n r s + marginalPair w K width n r s) := by
  let mu := marginalWeight w K width n
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))))
      (by decide) (fun | 0 => s | _ => r)).mul_left mu))
    (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) mu _ _)
      (Q'.add_eqv_congr' (haar_weighted_add (N width) mu _ _) (haar_weighted_add (N width) mu _ _)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

set_option maxHeartbeats 800000 in
/-- Exact signed cost identity for appending a whole test r. No support,
centering, orthogonality, or uniform-budget premise enters this identity. -/
theorem grouped_cost_split (qs : Nat → RatPoly) (degrees : Nat → Nat) (r : RatPoly) :
    let s := correctedSum hw0 hw1 K width hK n qs degrees
    marginalCost w K width n (finiteTests hw0 hw1 K width hK n qs degrees) +
      marginalPair w K width n r r + ((2 : Q')*headFloor w)*
        marginalFlow w K width n (finiteTests hw0 hw1 K width hK n qs degrees) r ≈
      headFloor w*marginalPair w K width n (polyAdd s r) (polyAdd s r) +
        diagonalRemainder hw0 hw1 K width hK n qs degrees +
        ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs degrees +
        ((1 : Q') + -(headFloor w))*marginalPair w K width n r r := by
  let s := correctedSum hw0 hw1 K width hK n qs degrees
  have hc := cost_actual_split hw0 hw1 K width hK n qs degrees
  have hf := flow_actual_pin hw0 hw1 K width hK n qs degrees r
  have hn := norm_add w K width n s r
  have he := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hc (Q'.eqv_refl _)) (Q'.mul_eqv_congr_left _ _ _ hf))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.add (.mul (.var 0) (.var 1)) (.var 4))
        (.mul (.mul (.const 2) (.var 0)) (.var 5))) (.var 2))
        (.mul (.mul (.const 2) (.var 0)) (.var 3)))
      (.add (.add (.add (.mul (.var 0) (.add (.add (.var 1) (.var 2)) (.add (.var 3) (.var 3))))
        (.var 4)) (.mul (.mul (.const 2) (.var 0)) (.var 5)))
        (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)))
      (by decide) (fun
        | 0 => headFloor w | 1 => marginalPair w K width n s s
        | 2 => marginalPair w K width n r r | 3 => marginalPair w K width n r s
        | 4 => diagonalRemainder hw0 hw1 K width hK n qs degrees
        | _ => determinantRemainder hw0 hw1 K width hK n qs degrees))
  exact Q'.eqv_trans _ _ _ he
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hn)) (Q'.eqv_refl _)) (Q'.eqv_refl _)) (Q'.eqv_refl _))

set_option maxHeartbeats 800000 in
/-- The SAME original corrected sum now uses active-only diagonal costs
and ONE grouped fringe norm. This is a proved finite-degree estimate,
not an assumed stable-decomposition budget. -/
theorem actualResidual_grouped_energy (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (hs : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (seeds i))
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := fun i => weightedResidual i (marginalWeight w K width n) (seeds i)
    let qa := fun i => weightedResidual i (marginalWeight w K width n) (activeSeeds width seeds i)
    let s := correctedSum hw0 hw1 K width hK n qs degrees
    let r := fringeSum w K width n seeds
    headFloor w*(marginalPair w K width n f s * marginalPair w K width n f s) ≤
      energy w K width (terminalMessage w K width n) f *
        (headFloor w*marginalPair w K width n s s + diagonalRemainder hw0 hw1 K width hK n qa degrees +
          ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qa degrees +
          ((1 : Q') + -(headFloor w))*marginalPair w K width n r r) := by
  let qs := fun i => weightedResidual i (marginalWeight w K width n) (seeds i)
  let qa := fun i => weightedResidual i (marginalWeight w K width n) (activeSeeds width seeds i)
  let sa := correctedSum hw0 hw1 K width hK n qa degrees
  let s := correctedSum hw0 hw1 K width hK n qs degrees
  let r := fringeSum w K width n seeds
  let tests := finiteTests hw0 hw1 K width hK n qa degrees
  have ha := activeSeeds_supported width seeds hs
  have h := grouped_fringe_marginal_energy hw0 hw1 K width hK n tests seeds
    (residualTests_supported hw0 hw1 K width hK n (activeSeeds width seeds) degrees ha)
    (residualTests_centered hw0 hw1 K width hK n (activeSeeds width seeds) degrees)
    (fun i hi => hs i (fringeBlocks_lt width i hi)) hf
  have hp := correctedSum_split hw0 hw1 K width hK n seeds degrees
  have hl : marginalFlow w K width n tests f + marginalPair w K width n f r ≈
      marginalPair w K width n f s :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (flow_actual_pin hw0 hw1 K width hK n qa degrees f) (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (pair_add w K width n f sa r))
        (haar_of_coeff ((hp.mul_left f).mul_left (marginalWeight w K width n))))
  have hn : marginalPair w K width n (polyAdd sa r) (polyAdd sa r) ≈ marginalPair w K width n s s :=
    haar_of_coeff (((hp.mul_right _).trans (hp.mul_left s)).mul_left (marginalWeight w K width n))
  have hc := Q'.eqv_trans _ _ _ (grouped_cost_split hw0 hw1 K width hK n qa degrees r)
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hn) (Q'.eqv_refl _)) (Q'.eqv_refl _)) (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hl) (Q'.mul_eqv_congr_left _ _ _ hl))))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hc)))

/-- The previously constructed approximant, with its SAME two explicit
degrees, enters the grouped estimate without a new centering hypothesis. -/
theorem approximant_grouped_energy (k l : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let seeds := familySeeds hw0 hw1 K width hK n k f
    let qa := fun i => weightedResidual i (marginalWeight w K width n) (activeSeeds width seeds i)
    let s := approximant hw0 hw1 K width hK n k l f
    let r := fringeSum w K width n seeds
    headFloor w*(marginalPair w K width n f s * marginalPair w K width n f s) ≤
      energy w K width (terminalMessage w K width n) f *
        (headFloor w*marginalPair w K width n s s + diagonalRemainder hw0 hw1 K width hK n qa (fun _ => l) +
          ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qa (fun _ => l) +
          ((1 : Q') + -(headFloor w))*marginalPair w K width n r r) :=
  actualResidual_grouped_energy hw0 hw1 K width hK n
    (familySeeds hw0 hw1 K width hK n k f) (fun _ => l)
    (fun i _ => familySeeds_supported hw0 hw1 K width hK n k i hf) hf

end YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeCost

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeCost.grouped_cost_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeCost.actualResidual_grouped_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeCost.approximant_grouped_energy
