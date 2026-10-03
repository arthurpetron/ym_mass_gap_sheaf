/-
# ORIGINAL terminal drift relative to the SAME surviving block norm

The constructed multiplier proves ell[A^2*phi_k^2]<=ell[b^2], where
A=g_(n+t), b=T^t(g_n*psi), and phi_k is the actual finite reciprocal ratio.
The original terminal comparison therefore bounds the drift relative to
Z1*ell[b^2] for EVERY reciprocal degree. A computed terminal-depth onset
depends only on fixed w,width and epsilon, not K,k or the source amplitude.
No inverse of A, surviving norm floor, stationary center or changing-family
uniformity is asserted. The other signed-cost components remain unpaid.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
  (transferStep_quadratic_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
  (comparisonEta comparisonEta_nonnegative comparisonKappa comparisonKappa_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (kineticFloor_le_cap mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
  (boundaryDrift boundaryDrift_terminal_abs_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (multiplierSquareCertificate)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage weightedMass

private theorem source_supported (w : Q') (K width n t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    t (supported_polyMul (terminalMessage_supported w K width n) hp)

private theorem window_order {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    blockWindowLower w K width n t ≤ blockWindowUpper w K width n t :=
  Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1)))

private theorem weighted_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -weightedMass w K width p :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => weightedMass w K width p)))

/-- The actual polynomial ratio does not enlarge the surviving V-weighted
square, including zero source/norm and all reciprocal degrees. -/
theorem blockConditionalRatio_surviving_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    weightedMass w K width (polyMul (polyMul A A) (polyMul phi phi)) ≤
      weightedMass w K width (polyMul b b) := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hK n t k
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  have hA := terminalMessage_supported w K width (n+t)
  have hb := source_supported w K width n t hp
  have hwindow := blockWindowCertificates hw0 hw1 K width hK n t hdepth
  have hM := multiplierSquareCertificate hA
    (blockWindowLower_positive hw0 hw1 K width hK n t)
    (blockWindowUpper_positive hw0 hw1 K width hK n t)
    (window_order hw0 hw1 K width hK n t) hwindow.1 hwindow.2 k
  have hn := weightedMass_nonnegative hw0 hw1 K width hK
    ((Certificate.square b hb).mul hM)
  have hid : RatPolyCoeffEqv
      (polyMul (polyMul b b)
        (polyAdd polyOne (polyNeg (polyMul (polyMul A G) (polyMul A G)))))
      (polyAdd (polyMul b b) (polyNeg (polyMul (polyMul A A) (polyMul phi phi)))) := by
    dsimp only [phi, blockConditionalRatio]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 2) (.var 2))
        (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))))
      (.add (.mul (.var 2) (.var 2))
        (.neg (.mul (.mul (.var 0) (.var 0))
          (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))))
      (by decide) (fun
        | 0 => A
        | 1 => G
        | _ => b)
  have he := Q'.eqv_trans _ _ _ (weightedMass_congr w K width hid)
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (weighted_neg w K width _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- ALL-degree boundary control relative to the SAME surviving square.
Neither partition, action, original source nor center is replaced. -/
theorem blockConditionalRatio_boundaryDrift_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    Q'.abs (boundaryDrift w K width A
      (blockConditionalRatio hw0 hw1 K width hK n t psi k)) ≤
      comparisonEta hw0 hw1 width (n+t-1) *
        weightedMass w K width (polyMul A (transferStep w K width A)) *
        weightedMass w K width (polyMul b b) := by
  dsimp only
  have hd := boundaryDrift_terminal_abs_le hw0 hw1 K width hK (n+t-1)
    (blockConditionalRatio_supported hw0 hw1 K width hK n t hp k)
  dsimp only at hd
  rw [show n+t-1+1 = n+t by omega] at hd
  have hZ1 := transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width
    (terminalMessage w K width (n+t)) (terminalMessage_supported w K width (n+t))
  have hcoef := Q'.mul_nonneg _ _
    (comparisonEta_nonnegative hw0 hw1 width (n+t-1)) hZ1
  exact Q'.le_trans' _ _ _ hd
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (blockConditionalRatio_surviving_square_le hw0 hw1 K width hK n t hdepth hp k) hcoef)

/-- Computed onset at FIXED original nome/width, independent of cutoff,
reciprocal degree and source. It is not a scaling-family uniform modulus. -/
def blockConditionalDriftDepthCutoff {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) (epsilon : Q') : Nat :=
  geometricCutoff (mixRate hw0 hw1 width) (comparisonKappa hw0 hw1 width) epsilon

/-- Terminal depth alone pays the drift, uniformly in every later cutoff
and EVERY reciprocal degree, with the same Z1 and surviving block norm. -/
theorem blockConditionalRatio_boundaryDrift_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k : Nat)
    (honset : blockConditionalDriftDepthCutoff hw0 hw1 width epsilon ≤ n+t-1) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    Q'.abs (boundaryDrift w K width A
      (blockConditionalRatio hw0 hw1 K width hK n t psi k)) ≤
      epsilon * weightedMass w K width (polyMul A (transferStep w K width A)) *
        weightedMass w K width (polyMul b b) := by
  dsimp only
  have heta : comparisonEta hw0 hw1 width (n+t-1) ≤ epsilon := by
    change comparisonKappa hw0 hw1 width * (mixRate hw0 hw1 width)^(n+t-1) ≤ epsilon
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (geometric_bound (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
        (comparisonKappa_nonnegative hw0 hw1 width) he (n+t-1) honset)
  have hZ1 := transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width
    (terminalMessage w K width (n+t)) (terminalMessage_supported w K width (n+t))
  have hB := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square _ (source_supported w K width n t hp))
  exact Q'.le_trans' _ _ _
    (blockConditionalRatio_boundaryDrift_abs_le hw0 hw1 K width hK n t hdepth hp k)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ heta hZ1) hB)

#print axioms blockConditionalRatio_surviving_square_le
#print axioms blockConditionalRatio_boundaryDrift_abs_le
#print axioms blockConditionalDriftDepthCutoff
#print axioms blockConditionalRatio_boundaryDrift_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
