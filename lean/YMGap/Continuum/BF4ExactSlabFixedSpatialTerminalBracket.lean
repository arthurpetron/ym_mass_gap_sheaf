/-
# Certified terminal-message comparison for the original transfer

Multiplying both sides of a relative bracket by a certified polynomial
preserves its endpoints. The actual transfer floor constructs positive
pairing denominators for every pair of finite messages T^m1 and T^n1.
Consequently the same shrinking source-probe interval bounds normalized
pairings with any such terminal message, with no new positivity premise.

Every mass retains its single original spatial weight V. No stationary
vacuum, original interior-insertion pin, physical OS form, or spatial/spacing
uniformity is asserted. The ordinary finite terminal message is not a vacuum.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Shared coordinates are retained; the multiplier needs an actual square
certificate, not a pointwise positivity assumption. -/
def multiplyBracket {width : Nat} {f g r : RatPoly}
    (B : Bracket width f g) (R : Certificate (N width) r) :
    Bracket width (polyMul r f) (polyMul r g) where
  lower := B.lower
  upper := B.upper
  lowerCertificate := Certificate.ofCoeff
    ((RatPolyCoeffEqv.mul_add_right r f (polySmul (-B.lower) g)).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right (-B.lower) r g))).symm
    (R.mul B.lowerCertificate)
  upperCertificate := Certificate.ofCoeff
    ((RatPolyCoeffEqv.mul_add_right r (polySmul B.upper g) (polySmul (-1) f)).trans
      ((RatPolyCoeffEqv.polyMul_smul_right B.upper r g).add
        (RatPolyCoeffEqv.polyMul_smul_right (-1) r f))).symm
    (R.mul B.upperCertificate)

/-- The same normalized weighted pairing lies between the same endpoints.
Its positive denominator is explicit and is constructed below for actual
terminal-message pairs. -/
theorem terminalMassRatio_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f g r : RatPoly}
    (B : Bracket width f g) (R : Certificate (N width) r)
    (hmass : (0 : Q') < weightedMass w K width (polyMul r g)) :
    B.lower ≤ massRatio w K width (polyMul r f) (polyMul r g) hmass ∧
      massRatio w K width (polyMul r f) (polyMul r g) hmass ≤ B.upper :=
  massRatio_bounds hw0 hw1 K width hK hmass (multiplyBracket B R)

/-- Multiplication of a certified lower bound gives a quantitative ORIGINAL
weighted pairing floor. No sign or independence of coordinates is assumed. -/
theorem weightedMass_product_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p h : RatPoly} {c : Q'}
    (P : Certificate (N width) p)
    (H : Certificate (N width) (polyAdd h (polyNeg (cap c)))) :
    c * weightedMass w K width p ≤ weightedMass w K width (polyMul p h) := by
  have hn := weightedMass_nonnegative hw0 hw1 K width hK (P.mul H)
  have hcapneg : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
    intro weight
    change (-(c*1)) * weight [] + 0 ≈ ((-c)*1) * weight [] + 0
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)
  have hc : RatPolyCoeffEqv (polyMul p (polyNeg (cap c))) (polySmul (-c) p) :=
    ((RatPolyCoeffEqv.refl p).mul hcapneg).trans
      ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left (-c) p))
  have he : weightedMass w K width (polyMul p (polyAdd h (polyNeg (cap c)))) ≈
      weightedMass w K width (polyMul p h) + -(c * weightedMass w K width p) :=
    Q'.eqv_trans _ _ _
      (weightedMass_congr w K width ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
        ((RatPolyCoeffEqv.refl _).add hc)))
      (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-c) p) (Q'.neg_mul_eqv c _))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- A transfer floor makes this product pairing strictly positive from the
two already positive masses; mere individual nonnegativity is not used. -/
theorem weightedMass_pair_transfer_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (F : Certificate (N width) f) (G : Certificate (N width) g)
    (hfm : (0 : Q') < weightedMass w K width f)
    (hgm : (0 : Q') < weightedMass w K width g) :
    (0 : Q') < weightedMass w K width (polyMul g (transferStep w K width f)) :=
  HeatKernelRGStep.lt_of_lt_of_le
    (Q'.mul_pos (Q'.mul_pos (kineticFloor_positive hw0 hw1 width) hfm) hgm)
    (weightedMass_product_floor hw0 hw1 K width hK G
      (transferStepLowerCertificate hw0 hw1 K width hK hf F))

/-- An actual finite terminal message; this is not a stationary vacuum. -/
def terminalMessage (w : Q') (K width n : Nat) : RatPoly :=
  iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n polyOne

theorem terminalMessage_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width) (terminalMessage w K width n) :=
  iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) n (supported_one _)

def terminalMessage_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width) (terminalMessage w K width n) :=
  iterateStep_certificate hw0 hw1 K width hK n polyOne (supported_one _) (Certificate.one _)

theorem terminalMessage_mass_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < weightedMass w K width (terminalMessage w K width n) :=
  iterateWeightedMass_positive hw0 hw1 K width hK n (supported_one _) (Certificate.one _)
    (weightedMass_one_positive hw0 hw1 K width hK)

private theorem iterate_front (blocks : Nat) (kernel weight : RatPoly) (n : Nat) (f : RatPoly) :
    iterateStep blocks kernel weight (n+1) f = step blocks kernel weight
      (iterateStep blocks kernel weight n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => exact ih (step blocks kernel weight f)

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- Every actual pair has a constructed positive denominator, including
zero iterations. No disjoint-support or new Perron-vector premise. -/
theorem terminalPair_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) :
    (0 : Q') < weightedMass w K width
      (polyMul (terminalMessage w K width m) (terminalMessage w K width n)) := by
  cases n with
  | zero =>
      exact HeatKernelRGStep.lt_of_lt_of_le (terminalMessage_mass_positive hw0 hw1 K width hK m)
        (Q'.ge_of_eqv (weightedMass_congr w K width (RatPolyCoeffEqv.mul_one _)))
  | succ n =>
      have hstep : terminalMessage w K width (n+1) =
          transferStep w K width (terminalMessage w K width n) :=
        iterate_front _ _ _ n polyOne
      rw [hstep]
      exact weightedMass_pair_transfer_positive hw0 hw1 K width hK
        (terminalMessage_supported w K width n)
        (terminalMessage_certificate hw0 hw1 K width hK n)
        (terminalMessage_certificate hw0 hw1 K width hK m)
        (terminalMessage_mass_positive hw0 hw1 K width hK n)
        (terminalMessage_mass_positive hw0 hw1 K width hK m)

/-- The original source-probe iterate paired with an arbitrary finite terminal
message, normalized by its actual positive product mass. -/
def terminalProbeRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (fs : List FaceFactor) : Q' :=
  massRatio w K width
    (polyMul (terminalMessage w K width m)
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (sourceProbe width fs)))
    (polyMul (terminalMessage w K width m) (terminalMessage w K width n))
    (terminalPair_positive hw0 hw1 K width hK m n)

/-- All finite terminal messages obey the SAME n-step interval of width
2*probeCap*q^n. The interval does not depend on terminal length m. -/
theorem terminalProbeRatio_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (fs : List FaceFactor) :
    (sourceProbeBracket hw0 hw1 K width hK n fs).lower ≤
        terminalProbeRatio hw0 hw1 K width hK m n fs ∧
      terminalProbeRatio hw0 hw1 K width hK m n fs ≤
        (sourceProbeBracket hw0 hw1 K width hK n fs).upper :=
  terminalMassRatio_bounds hw0 hw1 K width hK (sourceProbeBracket hw0 hw1 K width hK n fs)
    (terminalMessage_certificate hw0 hw1 K width hK m)
    (terminalPair_positive hw0 hw1 K width hK m n)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.multiplyBracket
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalMassRatio_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.weightedMass_product_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.weightedMass_pair_transfer_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_mass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalPair_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalProbeRatio
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket.terminalProbeRatio_bounds
