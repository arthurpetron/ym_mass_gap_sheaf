/-
# The three-column alternative in the COMPLETE ORIGINAL signed cost

Replace ONLY the last-step paired budget by its certified M^2*Gram
ceiling. The full active-link/six-plane sum, Vbar^2*G^2, both signed
Taylor remainders, and the SAME-norm depth/degree payments are retained.
The old paired ceiling remains available and is no larger. This module
constructs no useful family-relative estimate, scaling limit or mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepThreeGramBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepDriftPaidCost

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepThreeGramCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepDriftPaidCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepThreeGramBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal_supported)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (reciprocalScoreCorrection)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_mono)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage weightedMass

/-- Literal alternative angular budget; all original correction terms are kept. -/
def originalBlockThreeGramAngularBudget {w : Q'}
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
            (lastStepThreeGramBudget w K width a c)))
        (quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e))))
    else 0) (N width)

private theorem sum_le_on (f g : Nat → Q') : (m : Nat) →
    (∀ s, s < m → f s ≤ g s) → finSum f m ≤ finSum g m
  | 0, _ => Q'.le_of_eqv (Q'.eqv_refl _)
  | m+1, h => Q'.add_le_add
      (sum_le_on f g m (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self m))))
      (h m (Nat.lt_succ_self m))

/-- The comparison direction is explicit: the three-Gram ceiling is
LARGER than the still available original paired-residual budget. -/
theorem originalBlockLastStepAngularBudget_le_threeGram {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    originalBlockLastStepAngularBudget hw0 hw1 K width hK n r psi k ≤
      originalBlockThreeGramAngularBudget hw0 hw1 K width hK n r psi k := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hc := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) r
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hG := reciprocal_supported (terminalMessage_supported w K width (n+(r+1)))
    (blockWindowUpper w K width n (r+1))
    (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _
    (lastStep_threeGram_weighted_multiplier_le hw0 hw1 K width hhead
      (terminalMessage_supported w K width (n+r)) hc
      (Certificate.square _ (spatialFringeMass_supported w K width)) hG)
    (SumOfSquares.q_mul_self_nonneg (relativeCap w 32))
  unfold originalBlockLastStepAngularBudget originalBlockThreeGramAngularBudget
  apply sum_le_on
  intro s hs
  split
  · exact sixValue_mono _ _ (fun _ _ _ _ =>
      Q'.add_le_add (Q'.add_le_add h h) (Q'.le_refl' _))
  · exact Q'.le_refl' _

/-- Complete active-plane angular energy of the actual conditional ratio. -/
theorem original_block_threeGram_weightedAngularEnergy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi ≤
      originalBlockThreeGramAngularBudget hw0 hw1 K width hK n r psi k := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (original_block_lastStep_weightedAngularEnergy_le hw0 hw1 K width hK n r hN psi hp k)
    (originalBlockLastStepAngularBudget_le_threeGram hw0 hw1 K width hK n r hp k)

/-- Both exact Taylor remainders remain signed; ONLY the angular budget changes. -/
def originalBlockThreeGramBulkBudget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  weightedMass w K width (polyMul A A) *
    ((1-w)*originalBlockThreeGramAngularBudget hw0 hw1 K width hK n r psi k +
      (pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
        -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))))

/-- The SAME original bulk cost accepts the new alternative without
normalizer cancellation, independent remainder caps or discarded cross terms. -/
theorem originalBlockLastStepBulkBudget_le_threeGram {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    originalBlockLastStepBulkBudget hw0 hw1 K width hK n r psi k ≤
      originalBlockThreeGramBulkBudget hw0 hw1 K width hK n r psi k := by
  have h := originalBlockLastStepAngularBudget_le_threeGram hw0 hw1 K width hK n r hp k
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))))
    (weightedMass_nonnegative hw0 hw1 K width
      (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK)
      (Certificate.square _ (terminalMessage_supported w K width (n+(r+1)))))

/-- Both existing explicit onsets pay in Z1*B on this same cost. No
changing-width/nome uniformity or useful signed-bulk ratio is assumed. -/
theorem original_block_threeGram_cost_relative_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (delta epsilon : Q') (hdelta : (0 : Q') < delta) (hepsilon : (0 : Q') < epsilon)
    (hdepth : blockConditionalDriftDepthCutoff hw0 hw1 width delta ≤ n+(r+1)-1)
    (k : Nat) (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      (originalBlockThreeGramBulkBudget hw0 hw1 K width hK n r psi k +
        delta * weightedMass w K width (polyMul A (transferStep w K width A)) *
          weightedMass w K width (polyMul b b)) +
        epsilon * (weightedMass w K width (polyMul A (transferStep w K width A)) *
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (original_block_lastStep_driftPaid_cost_relative_tolerance hw0 hw1 K width hK
      n r hN hp delta epsilon hdelta hepsilon hdepth k hk)
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _
      (originalBlockLastStepBulkBudget_le_threeGram hw0 hw1 K width hK n r hp k)))

#print axioms originalBlockThreeGramAngularBudget
#print axioms originalBlockLastStepAngularBudget_le_threeGram
#print axioms original_block_threeGram_weightedAngularEnergy_le
#print axioms originalBlockThreeGramBulkBudget
#print axioms originalBlockLastStepBulkBudget_le_threeGram
#print axioms original_block_threeGram_cost_relative_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepThreeGramCost
