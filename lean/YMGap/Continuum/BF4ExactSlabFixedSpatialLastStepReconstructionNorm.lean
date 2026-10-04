/-
# Original incoming-ratio error in the SAME weighted squared norm

The original T=K*V has a constructed weighted Schur cap stepCap(w,width)^2.
Combining it with the actual incoming reciprocal's polynomial error
certificate gives ell[(T e_k)^2] <= rho^(2k)*stepCap^2*ell[c^2].
The coefficient does not contain cutoff, depth, source or source norm.
Nome/width dependence remains explicit; no scaling-uniform rate is claimed.

This is the reconstruction leg for the last-step variance-dissipation
estimate. It is not a small bound on the actual innovation or signed drift.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (partialHaarHeads_add partialHaarHeads_neg)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks kineticWeight spatialWeight weightedMass

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one blocks))
    (Q'.eqv_refl _)) (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem heads_cap (blocks : Nat) (c : Q') :
    RatPolyCoeffEqv (partialHaarHeads blocks (cap c)) (cap c) :=
  (partialHaarHeads_supported_constant blocks (support_smul (supported_one blocks) c)).trans
    (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _
      (quaternionHaar_polySmul blocks c polyOne)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (haar_one blocks))
        (Q'.mul_one_eqv c))) polyOne)

/-- The complete original step supplies its cap at the constant test one.
This is an actual polynomial cone certificate, not a supplied norm bound. -/
def original_step_one_upper_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) :
    Certificate (N width) (polyAdd (polySmul (stepCap w width) polyOne)
      (polyNeg (transferStep w K width polyOne))) := by
  let W := stepWeight w K width
  let C := stepCap w width
  have P := partialHaarHeads_certificate (N width) (N width)
    (stepWeightInterval hw0 hw1 K width).upper
  have hT : RatPolyCoeffEqv (transferStep w K width polyOne)
      (partialHaarHeads (N width) W) :=
    (transferStep_kernelMap w K width polyOne).trans
      (partialHaarHeads_congr (N width) (RatPolyCoeffEqv.mul_one W))
  have hid : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyAdd (cap C) (polyNeg W)))
      (polyAdd (cap C) (polyNeg (transferStep w K width polyOne))) := by
    rw [partialHaarHeads_add]
    exact (heads_cap (N width) C).add
      ((partialHaarHeads_neg (N width) W).trans (RatPolyCoeffEqv.neg hT.symm))
  exact Certificate.ofCoeff hid.symm P

/-- Weighted Schur control for the ORIGINAL transfer, with single V on
both norms. Its explicit cap is independent of cutoff and source. -/
theorem original_step_weighted_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    weightedMass w K width
        (polyMul (transferStep w K width p) (transferStep w K width p)) ≤
      (stepCap w width*stepCap w width)*weightedMass w K width (polyMul p p) := by
  have h := original_block_terminal_schur_square_le hw0 hw1 K width hK 1
    (supported_one (N width)) hp (Certificate.one (N width))
    (stepCap w width) (stepCap_nonnegative hw0 hw1 width)
    (original_step_one_upper_certificate hw0 hw1 K width)
  have hT : RatPolyCoeffEqv (transferStep w K width (polyMul polyOne p))
      (transferStep w K width p) :=
    partialHaarHeads_congr (N width)
      (((RatPolyCoeffEqv.one_mul p).mul_left (spatialWeight w K width)).mul_left
        (kineticWeight w K width))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (weightedMass_congr w K width (hT.mul hT)))
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (weightedMass_congr w K width
          ((RatPolyCoeffEqv.one_mul p).mul (RatPolyCoeffEqv.one_mul p))))))

private theorem mass_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -(weightedMass w K width p) :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

/-- The actual reciprocal error is small relative to the SAME incoming
square, even when that square is zero. No excitation is inverted. -/
theorem incomingRatioError_weighted_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let c := incomingNumerator w K width n r psi
    let e := incomingRatioError hw0 hw1 K width hK n r psi k
    weightedMass w K width (polyMul e e) ≤
      (mixRate hw0 hw1 width)^(2*k)*weightedMass w K width (polyMul c c) := by
  dsimp only
  let c := incomingNumerator w K width n r psi
  let e := incomingRatioError hw0 hw1 K width hK n r psi k
  let v := (mixRate hw0 hw1 width)^(2*k)
  have hn := weightedMass_nonnegative hw0 hw1 K width hK
    (incomingRatioError_square_certificate hw0 hw1 K width hK n r hdepth hpsi k)
  have he : weightedMass w K width
      (polyAdd (polyMul (cap v) (polyMul c c)) (polyNeg (polyMul e e))) ≈
      v*weightedMass w K width (polyMul c c) + -(weightedMass w K width (polyMul e e)) :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (weightedMass_congr w K width (cap_mul_left v (polyMul c c)))
          (weightedMass_smul w K width v _))
        (mass_neg w K width (polyMul e e)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- Propagation of the ACTUAL incoming reconstruction error through T.
The rate/cap depend on nome and width, not K,n,r,psi or a norm inverse. -/
theorem incomingRatioError_transferred_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let c := incomingNumerator w K width n r psi
    let e := incomingRatioError hw0 hw1 K width hK n r psi k
    weightedMass w K width
        (polyMul (transferStep w K width e) (transferStep w K width e)) ≤
      (((mixRate hw0 hw1 width)^(2*k))*(stepCap w width*stepCap w width))*
        weightedMass w K width (polyMul c c) := by
  dsimp only
  let c := incomingNumerator w K width n r psi
  let e := incomingRatioError hw0 hw1 K width hK n r psi k
  let v := (mixRate hw0 hw1 width)^(2*k)
  let C := stepCap w width
  have hc : SupportedQuaternionBlocks (N width) c :=
    iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
      r (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have he : SupportedQuaternionBlocks (N width) e :=
    supported_add hc (support_neg (supported_polyMul
      (terminalMessage_supported w K width (n+r))
      (blockConditionalRatio_supported hw0 hw1 K width hK n r hpsi k)))
  have h1 := original_step_weighted_square_le hw0 hw1 K width hK he
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (C*C)
    (incomingRatioError_weighted_square_le hw0 hw1 K width hK n r hdepth hpsi k)
    (SumOfSquares.q_mul_self_nonneg C)
  have hid : (C*C)*(v*weightedMass w K width (polyMul c c)) ≈
      (v*(C*C))*weightedMass w K width (polyMul c c) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.mul (.var 0) (.var 0))) (.var 2))
      (by decide) (fun | 0 => C | 1 => v | _ => weightedMass w K width (polyMul c c))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hid))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm.original_step_one_upper_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm.original_step_weighted_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm.incomingRatioError_weighted_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm.incomingRatioError_transferred_square_le
