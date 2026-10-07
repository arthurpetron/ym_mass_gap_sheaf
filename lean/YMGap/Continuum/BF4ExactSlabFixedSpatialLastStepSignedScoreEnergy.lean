/-
# Reassemble the actual signed score into original energy and signed correction

The finite reciprocal derivative is G*S+e after multiplication by A.
Its squared identity, not a square triangle, exposes the exact correction
sigma*|G*S|^2-2<G*S,e>-|e|^2. Summing the actual active planes and joining
the existing full Taylor identity reassembles BOTH signed remainders into
the ORIGINAL energy. The negative correction square is retained.

This is an exact finite identity, not a new smallness bound. The interacting
energy and signed correction still need quantitative control on the chosen
scaling family. It neither supplies an all-vector RG map/comparison nor
continuum survival, a Hamiltonian or the Clay target.
-/

import YMGap.Continuum.QuaternionHaarExactScoreEnergySplit
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr_lt finSum_add)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_congr haar_six)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
open YMGap.Continuum.QuaternionHaarExactScoreEnergySplit
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.SU2QuaternionAngularSquareLocality (blockAngularSquare_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor (energy_taylor_angular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
  (projected_terminal_source_pin blockConditionalRatio_fringe_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection (spatialFringeMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exactScoreAngularBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost (exactScoreSignedBulk)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass
  originalBlockTransfer projectedEndpointSource spatialFringeMass

private theorem add_exchange (a b c d : Q') : (a+b)+(c+d) ≈ (a+c)+(b+d) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem six_add (f g : Nat → Nat → Q') :
    sixValue (fun i j => f i j+g i j) ≈ sixValue f+sixValue g := by
  unfold sixValue
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (add_exchange _ _ _ _))
            (add_exchange _ _ _ _))) (add_exchange _ _ _ _))) (add_exchange _ _ _ _)))
    (add_exchange _ _ _ _)

/-- Literal signed reciprocal correction, including its favorable negative
square. No sign or smallness premise is imposed on the mixed term. -/
def exactScoreReciprocalDebt (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  let W := polyMul Vbar Vbar
  finSum (fun s => if s ∈ activeBlocks width then sixValue (fun i j =>
    let S := conditionalScore (4*s+i) (4*s+j) A b
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k
    (sigma*quaternionHaar (N width) (polyMul (polyMul W (polyMul G G)) (polyMul S S)) +
      -(2*quaternionHaar (N width) (polyMul W (polyMul (polyMul G S) e)))) +
      -(quaternionHaar (N width) (polyMul W (polyMul e e)))) else 0) (N width)

/-- No angular plane is estimated: the coupled score equals the actual
projected angular energy plus its complete signed reciprocal correction. -/
theorem exactScoreAngularBudget_energy_split (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi k ≈
      weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi +
        exactScoreReciprocalDebt sigma hw0 hw1 K width hK n r psi k := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let Vbar := spatialFringeMass w K width
  let q := projectedEndpointSource w K width A
  have hq := projected_terminal_source_pin w K width (n+(r+1))
  have hid (d : RatPoly) : RatPolyCoeffEqv
      (polyMul (polyMul q q) (polyMul d d))
      (polyMul (polyMul Vbar Vbar) (polyMul (polyMul A d) (polyMul A d))) :=
    ((hq.mul hq).mul_right _).trans (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => Vbar | 1 => A | _ => d))
  have hn : N width-1+1 = N width := Nat.sub_add_cancel hN
  dsimp only
  unfold exactScoreAngularBudget exactScoreReciprocalDebt weightedAngularEnergy
  simp only [hn]
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr_lt _ _ (N width) ?_)
    (finSum_add _ _ (N width))
  intro s hs
  split
  · rename_i ha
    have h := sixValue_congr _ _ (fun i j _ _ =>
      reciprocal_score_weighted_energy_split (N width) (4*s+i) (4*s+j)
        (polyMul Vbar Vbar) sigma A b
        (blockWindowUpper w K width n (r+1))
        (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) k)
    have hregroup (a b c d : Q') : ((a+b)+c)+d ≈ a+((b+c)+d) :=
      poly_identity_of_normal_eq
        (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.add (.var 0) (.add (.add (.var 1) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
    exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
      (sixValue_congr _ _ (fun _ _ _ _ => hregroup _ _ _ _))
      (Q'.eqv_trans _ _ _ (six_add _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (sixValue_congr _ _ (fun i j _ _ => Q'.eqv_symm (haar_of_coeff
              (hid (angularDerivative (4*s+i) (4*s+j) phi)))))
            (Q'.eqv_symm (haar_six (N width) (polyMul q q) _)))
          (Q'.eqv_refl _))))
  · rename_i ha
    have hz := blockAngularSquare_zero (blockConditionalRatio_fringe_independent
      hw0 hw1 K width hhead n (r+1) (by omega) hp k s
        ((fringeBlocks_mem_iff width s).mpr ⟨hs, ha⟩))
    have heq := haar_of_coeff (blocks := N width)
      ((hz.mul_left (polyMul q q)).trans (RatPolyCoeffEqv.mul_zero_right _))
    exact Q'.eqv_trans _ _ _ (by decide : (0 : Q') ≈ 0+0)
      (Q'.eqv_symm (Q'.add_eqv_congr' heq (Q'.eqv_refl 0)))

/-- BOTH Taylor remainders reassemble to the genuine ORIGINAL finite energy.
Only the explicit signed reciprocal debt remains; no bound is asserted. -/
theorem exactScoreSignedBulk_energy_split (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    exactScoreSignedBulk sigma hw0 hw1 K width hK n r psi k ≈
      weightedMass w K width (polyMul A A)*
        (energy w K width A phi +
          (1-w)*exactScoreReciprocalDebt sigma hw0 hw1 K width hK n r psi k) := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  let R := pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
    -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))
  have hs := exactScoreAngularBudget_energy_split sigma hw0 hw1 K width hK n r hN hp k
  have ht := energy_taylor_angular w K width A phi
    (terminalMessage_supported w K width (n+(r+1)))
    (blockConditionalRatio_supported hw0 hw1 K width hhead n (r+1) hp k) hN
    (fun i hi => blockConditionalRatio_fringe_independent
      hw0 hw1 K width hhead n (r+1) (by omega) hp k i hi)
  unfold exactScoreSignedBulk
  refine Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (1-w) _ _ hs) (Q'.eqv_refl _)) ?_)
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
    (.add (.add (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 0) (.var 2)))
    (by decide) (fun
      | 0 => 1-w
      | 1 => weightedAngularEnergy (N width-1) (projectedEndpointSource w K width A) phi
      | 2 => exactScoreReciprocalDebt sigma hw0 hw1 K width hK n r psi k
      | _ => R))
    (Q'.add_eqv_congr' (Q'.eqv_symm ht) (Q'.eqv_refl _))

#print axioms exactScoreReciprocalDebt
#print axioms exactScoreAngularBudget_energy_split
#print axioms exactScoreSignedBulk_energy_split

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy
