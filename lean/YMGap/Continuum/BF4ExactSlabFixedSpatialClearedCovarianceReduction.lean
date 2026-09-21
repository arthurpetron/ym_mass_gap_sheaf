/-
# Removing an invisible component from the ORIGINAL signed covariance test

The actual residual R_i satisfies P_i((V*g)*R_i)=0. Hence a multiple of
P_i(F_s) contributes exactly zero to its pairing with the combined signed
test F_s. Remove the computed SAME-weight least-squares multiple, not the
unweighted multiple one. The resulting test has no greater weighted norm,
and gives a Cauchy bound on the SAME original partition-cleared defect.

All three terms of F_s, including its original marginal-mean correction,
are retained before this exact cancellation. No spatial/action factor is
discarded. The conditional Haar projection is an auxiliary test direction,
not an asserted original observable or temporal invariant sector.

This is a guaranteed non-worsening of the one-residual cross bound for every
0<w<1 and late cutoff. The remaining norm and the aggregate decomposition
cost are NOT bounded uniformly in width, depth, cutoff or changing nome.
No new global/completed gap, continuum survival or Clay closure follows.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceCauchy
import YMGap.Continuum.SU2QuaternionWeightedResidualOrthogonality
import YMGap.Continuum.QuaternionHaarWeightedTestReduction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceReduction

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionWeightedResidualOrthogonality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarWeightedTestReduction

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Concrete direction and coefficient; no choice of a best approximation. -/
def reducedCombinedTest (w delta : Q') (K width n i : Nat) (s : RatPoly) : RatPoly :=
  let g := terminalMessage w K width n
  let F := combinedTest w delta K width g s
  reducedTest (N width) (polyMul (spatialWeight w K width) g) F (project i F)

theorem reducedCombinedTest_supported (w delta : Q') (K width n i : Nat) {s : RatPoly}
    (hs : SupportedQuaternionBlocks (N width) s) :
    SupportedQuaternionBlocks (N width) (reducedCombinedTest w delta K width n i s) := by
  have hF := combinedTest_supported w delta K width _ s
    (terminalMessage_supported w K width n) hs
  exact reducedTest_supported _ hF (project_supported i hF)

/-- SAME defect, EXACT equality, without a positivity or small-nome premise. -/
theorem terminalResidual_reduced_pairing (w delta : Q') (K width n i : Nat)
    (hi : i < N width) (f s : RatPoly) :
    let g := terminalMessage w K width n
    let W := polyMul (spatialWeight w K width) g
    let r := terminalResidual w K width n i f
    clearedDefect w delta K width g r s ≈
      weightedPair (N width) W r (reducedCombinedTest w delta K width n i s) := by
  dsimp only
  exact Q'.eqv_trans _ _ _ (clearedDefect_pairing_weightedPair w delta K width _ _ s)
    (Q'.eqv_symm (weightedResidual_pair_sub_independent (N width) i hi _ f _ _ _
      (project_independent i _)))

/-- Actual finite SU(2) estimate with the reduced test and original weight. -/
theorem terminalResidual_reduced_square_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (delta : Q') (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i < N width) {f s : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hs : SupportedQuaternionBlocks (N width) s) :
    let g := terminalMessage w K width n
    let W := polyMul (spatialWeight w K width) g
    let r := terminalResidual w K width n i f
    let F := reducedCombinedTest w delta K width n i s
    clearedDefect w delta K width g r s * clearedDefect w delta K width g r s ≤
      weightedPair (N width) W r r * weightedPair (N width) W F F := by
  dsimp only
  let g := terminalMessage w K width n
  let W := polyMul (spatialWeight w K width) g
  let r := terminalResidual w K width n i f
  let F := reducedCombinedTest w delta K width n i s
  have H : Certificate (N width) W :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK n)
  have hcs := weighted_cauchySchwarz (N width) W r F H
    (terminalResidual_supported w K width n i hf)
    (reducedCombinedTest_supported w delta K width n i hs)
  have he := terminalResidual_reduced_pairing w delta K width n i hi f s
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he)
      (Q'.mul_eqv_congr_left _ _ _ he))) hcs

/-- Guaranteed non-increase, not a claim that free Haar centering is
contractive under the interacting weight. -/
theorem reducedCombinedTest_norm_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (delta : Q') (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) {s : RatPoly} (hs : SupportedQuaternionBlocks (N width) s) :
    let g := terminalMessage w K width n
    let W := polyMul (spatialWeight w K width) g
    let F := combinedTest w delta K width g s
    let R := reducedCombinedTest w delta K width n i s
    weightedPair (N width) W R R ≤ weightedPair (N width) W F F := by
  have hF := combinedTest_supported w delta K width _ s
    (terminalMessage_supported w K width n) hs
  exact reducedTest_norm_le (N width) _ _ _
    ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK n)) hF (project_supported i hF)

/-- The entire new Cauchy budget is at most the old one. The improvement
can be zero; no strictly positive or uniform gain is asserted. -/
theorem reduced_square_budget_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (delta : Q') (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) {f s : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hs : SupportedQuaternionBlocks (N width) s) :
    let g := terminalMessage w K width n
    let W := polyMul (spatialWeight w K width) g
    let r := terminalResidual w K width n i f
    let F := combinedTest w delta K width g s
    let R := reducedCombinedTest w delta K width n i s
    weightedPair (N width) W r r * weightedPair (N width) W R R ≤
      weightedPair (N width) W r r * weightedPair (N width) W F F := by
  dsimp only
  apply Q'.mul_le_mul_of_nonneg_left
  · exact reducedCombinedTest_norm_le hw0 hw1 delta K width hK n i hs
  · exact ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK n)).square_insertion_nonnegative _
        (terminalResidual_supported w K width n i hf)

#print axioms reducedCombinedTest
#print axioms reducedCombinedTest_supported
#print axioms terminalResidual_reduced_pairing
#print axioms terminalResidual_reduced_square_le
#print axioms reducedCombinedTest_norm_le
#print axioms reduced_square_budget_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceReduction
