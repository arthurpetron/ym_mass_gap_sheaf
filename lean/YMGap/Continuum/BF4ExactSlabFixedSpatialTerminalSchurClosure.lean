/-
# Sharp terminal Schur control of the ACTUAL filtered signed source

Finite polynomial ratio tests have the sharp terminal-bracket U^2 bound.
The existing original reciprocal reconstruction and bounded original block
continuity extend it to b=T^u(g_n*psi), with no surviving-norm inverse.
The coarse continuity cap pays approximation only and disappears entirely
from the final bound. No stationary eigenpin, lower survival estimate,
changing-family uniformity, physical/continuum/QFT/every-group/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWeightedContinuity
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
import YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle
import YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
import YMGap.Continuum.RCDistBridge

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurClosure

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (transferStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWeightedContinuity
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
  (costTolerance costTolerance_pos costTolerance_pays)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem block_congr (w : Q') (K width : Nat) :
    (d : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
      RatPolyCoeffEqv (originalBlockTransfer w K width d p)
        (originalBlockTransfer w K width d q)
  | 0, _, _, h => h
  | d+1, _, _, h =>
      block_congr w K width d
        (partialHaarHeads_congr (N width)
          ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width)))

private theorem block_add (w : Q') (K width : Nat) : (d : Nat) → (p q : RatPoly) →
    RatPolyCoeffEqv (originalBlockTransfer w K width d (polyAdd p q))
      (polyAdd (originalBlockTransfer w K width d p) (originalBlockTransfer w K width d q))
  | 0, _, _ => RatPolyCoeffEqv.refl _
  | d+1, p, q =>
      (block_congr w K width d (transferStep_add w K width p q)).trans
        (block_add w K width d (transferStep w K width p) (transferStep w K width q))

private theorem mass_square_add_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p)
    (hq : SupportedQuaternionBlocks (N width) q)
    (eta : Q') (heta : (0 : Q') < eta) {a b : Q'}
    (ha : weightedMass w K width (polyMul p p) ≤ a)
    (hb : weightedMass w K width (polyMul q q) ≤ b) :
    weightedMass w K width (polyMul (polyAdd p q) (polyAdd p q)) ≤
      (1+eta)*a+(1+Q'.recipPos eta heta)*b := by
  have ha' : quaternionHaar (N width)
      (polyMul (spatialWeight w K width) (polyMul p p)) ≤ a := by
    simpa only [weightedMass] using ha
  have hb' : quaternionHaar (N width)
      (polyMul (spatialWeight w K width) (polyMul q q)) ≤ b := by
    simpa only [weightedMass] using hb
  simpa only [weightedMass] using
    QuaternionHaarAsymmetricSquareTriangle.weighted_square_add_bound eta heta
      (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
      hp hq ha' hb'

set_option maxHeartbeats 2000000 in
/-- Actual signed block source, not only sources with an exact polynomial
ratio. The constructed original reciprocal closes the sharp bound without
retaining its coarse continuity constant in the conclusion. -/
theorem original_block_terminal_schur_source_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (n u d : Nat) (hdepth : 1 ≤ n+u)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (U : Q') (hU : (0 : Q') ≤ U)
    (PU : Certificate (N width)
      (polyAdd (polySmul U (terminalMessage w K width (n+u)))
        (polyNeg (originalBlockTransfer w K width d (terminalMessage w K width (n+u)))))) :
    let b := originalBlockTransfer w K width u (polyMul (terminalMessage w K width n) psi)
    weightedMass w K width (polyMul (originalBlockTransfer w K width d b)
      (originalBlockTransfer w K width d b)) ≤
      (U*U)*weightedMass w K width (polyMul b b) := by
  dsimp only
  let A := terminalMessage w K width (n+u)
  let b := originalBlockTransfer w K width u (polyMul (terminalMessage w K width n) psi)
  let S := fun p => originalBlockTransfer w K width d p
  let M := fun p => weightedMass w K width (polyMul p p)
  let B := M b
  let Q := (U*U)*B
  let capPower := ((transferWeightedCap w K width)*(transferWeightedCap w K width))^d
  have hA := terminalMessage_supported w K width (n+u)
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) u
    (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square _ hb)
  have hQ : (0 : Q') ≤ Q := Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg U) hB
  have hcap : (0 : Q') ≤ capPower := Q'.pow_nonneg _
    (SumOfSquares.q_mul_self_nonneg (transferWeightedCap w K width)) d
  have hnear (eta : Q') (heta : (0 : Q') < eta) : M (S b) ≤ (1+eta)*Q := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hepsilon
    let coef := 1+Q'.recipPos eta heta
    have hcoef : (0 : Q') ≤ coef := Q'.zero_le_add _ _ Q'.zero_le_one
      (Q'.le_of_lt (Q'.recipPos_pos eta heta))
    let cost := coef*(capPower*B)
    have hcost : (0 : Q') ≤ cost := Q'.mul_nonneg _ _ hcoef (Q'.mul_nonneg _ _ hcap hB)
    let k := geometricCutoff (mixRate hw0 hw1 width) cost epsilon
    let phi := blockConditionalRatio hw0 hw1 K width hK n u psi k
    let p := polyMul A phi
    let e := polyAdd b (polyNeg p)
    have hphi := blockConditionalRatio_supported hw0 hw1 K width hK n u hp k
    have hps := supported_polyMul hA hphi
    have hes := supported_add hb (support_neg hps)
    have hSp := iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) d hps
    have hSe := iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) d hes
    have hpB : M p ≤ B := Q'.le_trans' _ _ _
      (Q'.le_of_eqv (weightedMass_congr w K width
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => A | _ => phi))))
      (blockConditionalRatio_surviving_square_le hw0 hw1 K width hK n u hdepth hp k)
    have hschur : M (S p) ≤ Q := Q'.le_trans' _ _ _
      (original_block_terminal_schur_square_le hw0 hw1 K width hK d hA hphi
        (terminalMessage_certificate hw0 hw1 K width hK (n+u)) U hU PU)
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hpB
        (SumOfSquares.q_mul_self_nonneg U))
    have herror : M (S e) ≤ capPower*((mixRate hw0 hw1 width)^(2*k)*B) :=
      Q'.le_trans' _ _ _
        (originalBlockTransfer_weighted_square_le hw0 hw1 K width hK d hes)
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (blockConditionalRatio_reconstruction hw0 hw1 K width hK n u hdepth hp k) hcap)
    have hgeo := geometric_bound (mixRate_nonnegative hw0 hw1 width)
      (mixRate_lt_one hw0 hw1 width) hcost hepsilon k (Nat.le_refl _)
    have hpow : (mixRate hw0 hw1 width)^(2*k) ≤ (mixRate hw0 hw1 width)^k :=
      HKConvGen.pow_base_antitone (mixRate_nonnegative hw0 hw1 width)
        (Q'.le_of_lt (mixRate_lt_one hw0 hw1 width)) (by omega)
    have hpay : coef*(capPower*((mixRate hw0 hw1 width)^(2*k)*B)) ≤ epsilon :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.var 2) (.mul (.var 0) (.mul (.var 1) (.var 3))))
        (by decide) (fun
          | 0 => coef | 1 => capPower
          | 2 => (mixRate hw0 hw1 width)^(2*k) | _ => B)))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hcost) hgeo)
    have hid : RatPolyCoeffEqv b (polyAdd p e) :=
      coeffEvalExpr_eqv_of_normalize_eq (.var 0)
        (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
        (by decide) (fun | 0 => b | _ => p)
    have hsum : RatPolyCoeffEqv (S b) (polyAdd (S p) (S e)) :=
      (block_congr w K width d hid).trans (block_add w K width d p e)
    have htri : M (polyAdd (S p) (S e)) ≤
        (1+eta)*Q+coef*(capPower*((mixRate hw0 hw1 width)^(2*k)*B)) :=
      mass_square_add_bound hw0 hw1 K width hK hSp hSe eta heta hschur herror
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (weightedMass_congr w K width (hsum.mul hsum)))
      (Q'.le_trans' _ _ _ htri (Q'.add_le_add_left _ _ _ hpay))
  apply Q'.le_of_forall_pos_add
  intro epsilon hepsilon
  let eta := costTolerance Q hQ epsilon
  have heta : (0 : Q') < eta := costTolerance_pos Q hQ epsilon hepsilon
  have hpay := costTolerance_pays Q hQ epsilon (Q'.le_of_lt hepsilon)
  exact Q'.le_trans' _ _ _ (hnear eta heta)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.var 0)) (.var 1))
      (.add (.var 1) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => eta | _ => Q))) (Q'.add_le_add_left _ _ _ hpay))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurClosure

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurClosure.original_block_terminal_schur_source_le
