/-
# Exact normalized pins for the actual middle-slice ratio

Weighted symmetry identifies the middle numerator with the mass of
T^n((T^m 1)*p), and the SAME middle denominator with the mass of T^n(T^m 1).
The comparison mass is proved positive by the existing certified iterate
construction. Rational reciprocal congruence then preserves normalization.

Exchanging the two finite terminal messages preserves the middle ratio by
polynomial commutativity, without any support assumption on that algebraic
identity. The iterate pin retains the supported-probe guard needed by weighted
symmetry. No interior decay, stationary law, geometric placement or OS claim
is asserted here; these pins feed the actual middle-probe bracket consumer.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay (iterateWeightedMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (iterateStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

-- Use the proved scalar laws without expanding face lists or Haar sums.
attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- Equality of the actual numerator and denominator masses preserves the
ratio. Both positive-denominator proofs remain explicit; no arbitrary choice
of a reciprocal or denominator replacement is involved. -/
theorem massRatio_congr (w : Q') (K width : Nat) {f f' g g' : RatPoly}
    (hg : (0 : Q') < weightedMass w K width g)
    (hg' : (0 : Q') < weightedMass w K width g')
    (hf : weightedMass w K width f ≈ weightedMass w K width f')
    (hd : weightedMass w K width g ≈ weightedMass w K width g') :
    massRatio w K width f g hg ≈ massRatio w K width f' g' hg' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hf)
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.recipPos_eqv_congr _ _ hg hg' hd))

private theorem terminal_pair_mass (w : Q') (K width n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    weightedMass w K width (polyMul p (terminalMessage w K width n)) ≈
      weightedMass w K width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n p) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (iterateStep_weighted_symmetric w K width n hp (supported_one (N width))))
    (weightedMass_congr w K width (RatPolyCoeffEqv.one_mul _))

/-- The normalized interior insertion is the actual n-step ratio starting
from ((T^m 1)*p,T^m 1). Its comparison mass is constructed from the certified
terminal message, not added as an analytic premise. -/
theorem middleRatio_iterate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    middleRatio hw0 hw1 K width hK m n p ≈
      massRatio w K width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
          (polyMul (terminalMessage w K width m) p))
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
          (terminalMessage w K width m))
        (iterateWeightedMass_positive hw0 hw1 K width hK n
          (terminalMessage_supported w K width m)
          (terminalMessage_certificate hw0 hw1 K width hK m)
          (terminalMessage_mass_positive hw0 hw1 K width hK m)) :=
  massRatio_congr w K width (terminalPair_positive hw0 hw1 K width hK m n)
    (iterateWeightedMass_positive hw0 hw1 K width hK n
      (terminalMessage_supported w K width m)
      (terminalMessage_certificate hw0 hw1 K width hK m)
      (terminalMessage_mass_positive hw0 hw1 K width hK m))
    (terminal_pair_mass w K width n
      (supported_polyMul (terminalMessage_supported w K width m) hp))
    (terminal_pair_mass w K width n (terminalMessage_supported w K width m))

/-- Interchanging the actual finite left/right messages preserves the
interior ratio. This pure commutativity identity needs no probe support. -/
theorem middleRatio_swap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (p : RatPoly) :
    middleRatio hw0 hw1 K width hK m n p ≈ middleRatio hw0 hw1 K width hK n m p :=
  massRatio_congr w K width (terminalPair_positive hw0 hw1 K width hK m n)
    (terminalPair_positive hw0 hw1 K width hK n m)
    (weightedMass_congr w K width
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 2) (.var 1)) (.var 0)) (by decide)
        (fun | 0 => terminalMessage w K width m | 1 => p | _ => terminalMessage w K width n)))
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins.massRatio_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins.middleRatio_iterate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins.middleRatio_swap
