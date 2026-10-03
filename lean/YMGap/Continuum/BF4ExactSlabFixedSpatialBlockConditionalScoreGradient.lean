/-
# Actual coupled-noise bound for the original conditional gradient

The full interacting window produces the score/noise certificate. Its
finite reciprocal consumer keeps the SAME output weight and the exact
reciprocal correction. Specializing the weight to Vbar^2 meets the original
qbar^2 angular plane in the energy formula. No replacement of Vbar^2 by V,
comparison to surviving filtered variance, or scaling uniformity is made.
-/

import YMGap.Continuum.QuaternionHaarConditionalScoreGradient
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
import YMGap.Continuum.SU2QuaternionAngularSquareLocality

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalScoreGradient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularSquare blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionAngularSquareLocality (blockAngularSquare_zero)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_mono haar_six)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairBudget)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage

/-- No noise or score bound is supplied by the caller: both certificates
are produced from the original full window at a positive block length. -/
theorem original_block_coupled_gradient_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (f : RatPoly) (c : Q') (hf : SupportedQuaternionBlocks (N width) f)
    {W : RatPoly} (MW : Certificate (N width) W) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let psi := shifted f c
    let b := originalBlockTransfer w K width (r+1)
      (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
    quaternionHaar (N width) (polyMul W
      (polyMul (polyMul A (angularDerivative (4*s+i) (4*s+j) phi))
        (polyMul A (angularDerivative (4*s+i) (4*s+j) phi)))) ≤
      sumBound
        ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
          (polyMul W (blockNoise w K width (r+1) (terminalMessage w K width n) psi)))
        (quaternionHaar (N width) (polyMul W (polyMul e e))) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hp := shifted_supported hf c
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hsn := activeBlocks_lt width s hs
  have hwindow := blockWindowCertificates hw0 hw1 K width hhead n (r+1) (by omega)
  have PN := blockNoise_certificate hw0 hw1 K width hhead (r+1)
    (terminalMessage_supported w K width n) hp
    (terminalMessage_certificate hw0 hw1 K width hhead n)
  have PS := original_block_scoreVariance_certificate hw0 hw1 K width hK n r s hs hi hj f c hf
  exact reciprocal_score_gradient_square_le (by omega) (by omega) MW
    (terminalMessage_supported w K width (n+(r+1))) hb
    (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1))
    (terminalMessage_certificate hw0 hw1 K width hhead (n+(r+1))) hwindow.2 PN PS k

/-- The coupled estimate meets the SAME actual projected-action angular
plane. Vbar^2 is retained on noise AND the finite reciprocal correction. -/
theorem original_block_projected_plane_score_gradient_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (f : RatPoly) (c : Q') (hf : SupportedQuaternionBlocks (N width) f) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let psi := shifted f c
    let b := originalBlockTransfer w K width (r+1)
      (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    let qbar := projectedEndpointSource w K width A
    let Vbar := spatialFringeMass w K width
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
    quaternionHaar (N width) (polyMul (polyMul qbar qbar)
      (polyMul (angularDerivative (4*s+i) (4*s+j) phi)
        (angularDerivative (4*s+i) (4*s+j) phi))) ≤
      sumBound
        ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
          (polyMul (polyMul Vbar Vbar)
            (blockNoise w K width (r+1) (terminalMessage w K width n) psi)))
        (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e))) := by
  dsimp only
  have hp := projected_terminal_source_pin w K width (n+(r+1))
  have hid (d : RatPoly) : RatPolyCoeffEqv
      (polyMul
        (polyMul (projectedEndpointSource w K width (terminalMessage w K width (n+(r+1))))
          (projectedEndpointSource w K width (terminalMessage w K width (n+(r+1)))))
        (polyMul d d))
      (polyMul (polyMul (spatialFringeMass w K width) (spatialFringeMass w K width))
        (polyMul (polyMul (terminalMessage w K width (n+(r+1))) d)
          (polyMul (terminalMessage w K width (n+(r+1))) d))) :=
    ((hp.mul hp).mul_right _).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
          (.mul (.var 2) (.var 2)))
        (.mul (.mul (.var 0) (.var 0))
          (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (by decide) (fun
          | 0 => spatialFringeMass w K width
          | 1 => terminalMessage w K width (n+(r+1)) | _ => d))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (hid _)))
    (original_block_coupled_gradient_square_le hw0 hw1 K width hK n r s hs hi hj f c hf
      (Certificate.square _ (spatialFringeMass_supported w K width)) k)

/-- Computed angular budget over exactly the active original links and
six planes. The actual noise, projected weight and correction stay literal. -/
def originalBlockScoreAngularBudget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (f : RatPoly) (c : Q') (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let psi := shifted f c
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let Vbar := spatialFringeMass w K width
  let noise := blockNoise w K width (r+1) (terminalMessage w K width n) psi
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun i j =>
      let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
        (blockWindowUpper w K width n (r+1))
        (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
      sumBound
        ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
          (polyMul (polyMul Vbar Vbar) noise))
        (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e))))
    else 0) (N width)

private theorem sum_le_on (f g : Nat → Q') : (m : Nat) →
    (∀ s, s < m → f s ≤ g s) → finSum f m ≤ finSum g m
  | 0, _ => Q'.le_of_eqv (Q'.eqv_refl _)
  | m+1, h => Q'.add_le_add
      (sum_le_on f g m (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self m))))
      (h m (Nat.lt_succ_self m))

/-- Every original plane is consumed. Inactive output links contribute
exactly zero by actual fringe independence, not by dropping action terms. -/
theorem original_block_score_weightedAngularEnergy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (f : RatPoly) (c : Q') (hf : SupportedQuaternionBlocks (N width) f) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) (shifted f c) k
    weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi ≤
      originalBlockScoreAngularBudget hw0 hw1 K width hK n r f c k := by
  dsimp only
  unfold weightedAngularEnergy originalBlockScoreAngularBudget
  have hn : N width-1+1 = N width := Nat.sub_add_cancel hN
  simp only [hn]
  apply sum_le_on
  intro s hs
  split
  · rename_i ha
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_six (N width) _ _))
      (sixValue_mono _ _ (fun i j hi hj =>
        original_block_projected_plane_score_gradient_le hw0 hw1 K width hK n r s ha
          hi hj f c hf k))
  · rename_i ha
    have hi := (fringeBlocks_mem_iff width s).mpr ⟨hs, ha⟩
    have hz := blockAngularSquare_zero
      (blockConditionalRatio_fringe_independent hw0 hw1 K width
        (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) n (r+1) (by omega)
        (shifted_supported hf c) k s hi)
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (haar_of_coeff ((hz.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _)))
      (Q'.eqv_refl _))

/-- Direct consumer in the original positive edge energy. The heat-gap
mixed Taylor budget is retained; no favorable drift or relative norm is assumed. -/
theorem original_block_score_energy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (hkin : sufficientCutoff w ≤ K)
    (n r : Nat) (hN : 0 < N width) (f : RatPoly) (c : Q')
    (hf : SupportedQuaternionBlocks (N width) f) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) (shifted f c) k
    let qbar := projectedEndpointSource w K width A
    energy w K width A phi ≤
      (1-w)*originalBlockScoreAngularBudget hw0 hw1 K width hK n r f c k+
      ((1-w)*(1-w))*pairBudget (N width-1) qbar (polyMul qbar (polyMul phi phi)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hp := shifted_supported hf c
  have hs := BF4ExactSlabFixedSpatialSourceTaylor.energy_le_angular_add_mixed_quadratic
    (Q'.le_of_lt hw0) hw1 K width hkin (terminalMessage w K width (n+(r+1)))
    (blockConditionalRatio hw0 hw1 K width hhead n (r+1) (shifted f c) k)
    (terminalMessage_supported w K width (n+(r+1)))
    (blockConditionalRatio_supported hw0 hw1 K width hhead n (r+1) hp k) hN
    (fun i hi => blockConditionalRatio_fringe_independent hw0 hw1 K width hhead
      n (r+1) (by omega) hp k i hi)
  have hb := original_block_score_weightedAngularEnergy_le hw0 hw1 K width hK n r hN f c hf k
  exact Q'.le_trans' _ _ _ hs
    (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hb
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))))

#print axioms original_block_coupled_gradient_square_le
#print axioms original_block_projected_plane_score_gradient_le
#print axioms originalBlockScoreAngularBudget
#print axioms original_block_score_weightedAngularEnergy_le
#print axioms original_block_score_energy_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalScoreGradient
