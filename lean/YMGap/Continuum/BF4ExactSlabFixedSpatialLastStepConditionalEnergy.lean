/-
# Last-step paired score in the ORIGINAL full angular energy

The incoming pair is a=g_(n+r), c=T^r(g_n*psi), not an unrelated source.
The same finite conditional ratio consumes its last-step score budget with
G^2 retained inside Vbar^2. All six planes on every active link are paid;
inactive links vanish by the actual ratio's fringe independence. The
reciprocal correction has a computed fixed-window onset. No replacement
of Vbar^2, relative surviving-norm estimate or family uniformity is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalScoreGradient
import YMGap.Continuum.QuaternionHaarReciprocalScoreCorrection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticFloor_le_cap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSquareLocality (blockAngularSquare_zero)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep iterateStep_supported)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (remainder radius)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (reciprocalScoreCorrection)
open YMGap.Continuum.QuaternionHaarReciprocalScoreCorrection
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_mono haar_six)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage

private theorem terminal_output (w : Q') (K width n r : Nat) :
    transferStep w K width (terminalMessage w K width (n+r)) =
      terminalMessage w K width (n+(r+1)) :=
  (terminalMessage_next w K width (n+r)).trans
    (congrArg (terminalMessage w K width) (by omega))

private theorem source_output (w : Q') (K width r : Nat) (p : RatPoly) :
    transferStep w K width (originalBlockTransfer w K width r p) =
      originalBlockTransfer w K width (r+1) p := by
  exact (show originalBlockTransfer w K width (r+1) p =
      transferStep w K width (originalBlockTransfer w K width r p) from
    by simpa only [originalBlockTransfer, iterateStep, transferStep] using
      iterateStep_add (N width) (kineticWeight w K width)
        (spatialWeight w K width) r 1 p).symm

/-- Actual successive messages, with an arbitrary certified SAME output
weight. The reciprocal and the paired budget are not decoupled. -/
theorem original_block_lastStep_gradient_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi)
    {W : RatPoly} (MW : Certificate (N width) W) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
    quaternionHaar (N width) (polyMul W
      (polyMul (polyMul A (angularDerivative (4*s+i) (4*s+j) phi))
        (polyMul A (angularDerivative (4*s+i) (4*s+j) phi)))) ≤
      sumBound
        ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
          (polyMul (polyMul W (polyMul G G)) (lastStepScoreBudget w K width a c)))
        (quaternionHaar (N width) (polyMul W (polyMul e e))) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hc : SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)) :=
    iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) r
      (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have hp := lastStep_reciprocal_gradient_square_le hw0 hw1 K width hK s hs hi hj
    (terminalMessage_supported w K width (n+r)) hc MW
    (blockWindowUpper w K width n (r+1))
    (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
  dsimp only at hp
  rw [terminal_output w K width n r, source_output] at hp
  exact hp

/-- The original projected density is qbar=Vbar*A. Both Vbar^2 and
the finite reciprocal square stay on the last-step cost. -/
theorem original_block_projected_plane_lastStep_gradient_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
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
          (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
            (lastStepScoreBudget w K width a c)))
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
          | 1 => terminalMessage w K width (n+(r+1))
          | _ => d))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (hid _)))
    (original_block_lastStep_gradient_square_le hw0 hw1 K width hK n r s hs hi hj
      psi hpsi (Certificate.square _ (spatialFringeMass_supported w K width)) k)

/-- Computed last-step budget over the actual active links and six planes. -/
def originalBlockLastStepAngularBudget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun i j =>
      let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
        (blockWindowUpper w K width n (r+1))
        (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
      sumBound
        ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
          (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
            (lastStepScoreBudget w K width a c)))
        (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e))))
    else 0) (N width)

private theorem sum_le_on (f g : Nat → Q') : (m : Nat) →
    (∀ s, s < m → f s ≤ g s) → finSum f m ≤ finSum g m
  | 0, _ => Q'.le_of_eqv (Q'.eqv_refl _)
  | m+1, h => Q'.add_le_add
      (sum_le_on f g m (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self m))))
      (h m (Nat.lt_succ_self m))

/-- Complete original angular energy, including all active planes and
exact inactive-link zeros. No Taylor remainder or boundary term is discarded. -/
theorem original_block_lastStep_weightedAngularEnergy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi ≤
      originalBlockLastStepAngularBudget hw0 hw1 K width hK n r psi k := by
  dsimp only
  unfold weightedAngularEnergy originalBlockLastStepAngularBudget
  have hn : N width-1+1 = N width := Nat.sub_add_cancel hN
  simp only [hn]
  apply sum_le_on
  intro s hs
  split
  · rename_i ha
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_six (N width) _ _))
      (sixValue_mono _ _ (fun i j hi hj =>
        original_block_projected_plane_lastStep_gradient_le hw0 hw1 K width hK n r s ha
          hi hj psi hpsi k))
  · rename_i ha
    have hi := (fringeBlocks_mem_iff width s).mpr ⟨hs, ha⟩
    have hz := blockAngularSquare_zero
      (blockConditionalRatio_fringe_independent hw0 hw1 K width
        (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) n (r+1) (by omega)
        hpsi k s hi)
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (haar_of_coeff ((hz.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _)))
      (Q'.eqv_refl _))

/-- The actual fixed window pays the per-plane correction at every later
degree. The derivative cost and radius are computed, not supplied ceilings. -/
theorem original_block_lastStep_correction_square_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi)
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let u := blockWindowUpper w K width n (r+1)
    let hu := blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)
    let ell := blockWindowLower w K width n (r+1)
    let Vbar := spatialFringeMass w K width
    let d := polyMul b (angularDerivative (4*s+i) (4*s+j) (remainder A u hu))
    correctionSquareModulus (radius ell u hu)
        (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul d d))) epsilon ≤ k →
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu (k+1)
    quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e)) ≤ epsilon := by
  dsimp only
  intro hk
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hsn := activeBlocks_lt width s hs
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have hwindow := blockWindowCertificates hw0 hw1 K width hhead n (r+1) (by omega)
  have horder : blockWindowLower w K width n (r+1) ≤ blockWindowUpper w K width n (r+1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hhead (n+(r+1)-1)))
  exact reciprocalScoreCorrection_square_tolerance (by omega) (by omega)
    (Certificate.square _ (spatialFringeMass_supported w K width))
    (terminalMessage_supported w K width (n+(r+1))) hb
    (blockWindowLower_positive hw0 hw1 K width hhead n (r+1))
    (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1))
    horder hwindow.1 hwindow.2 he k hk

#print axioms original_block_lastStep_gradient_square_le
#print axioms original_block_projected_plane_lastStep_gradient_le
#print axioms originalBlockLastStepAngularBudget
#print axioms original_block_lastStep_weightedAngularEnergy_le
#print axioms original_block_lastStep_correction_square_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
