/-
# Constant-observable obstruction to arbitrary input-norm/noise conversion

The actual conditional noise vanishes for the observable one, whereas the
actual terminal source has positive squared mass. Thus no scalar coefficient
bounds arbitrary input squared mass by that conditional noise. This is NOT a
vacuum-complement no-go and says nothing about a reciprocal-algorithm residual.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalNoiseVacuumObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv

private theorem iterate_congr (blocks : Nat) (kernel weight : RatPoly) (t : Nat)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (iterateStep blocks kernel weight t p)
      (iterateStep blocks kernel weight t q) := by
  induction t generalizing p q with
  | zero => exact h
  | succ t ih =>
    exact ih (partialHaarHeads_congr blocks
      ((RatPolyCoeffEqv.refl kernel).mul ((RatPolyCoeffEqv.refl weight).mul h)))

/-- No support or positivity premise is needed for the exact cancellation. -/
theorem blockNoise_one (w : Q') (K width t : Nat) (g : RatPoly) :
    RatPolyCoeffEqv (blockNoise w K width t g polyOne) polyZero := by
  let A := originalBlockTransfer w K width t g
  have hb : RatPolyCoeffEqv
      (originalBlockTransfer w K width t (polyMul g polyOne)) A :=
    iterate_congr _ _ _ t (RatPolyCoeffEqv.mul_one g)
  have hH : RatPolyCoeffEqv
      (originalBlockTransfer w K width t (polyMul g (polyMul polyOne polyOne))) A :=
    iterate_congr _ _ _ t
      (((RatPolyCoeffEqv.refl g).mul (RatPolyCoeffEqv.mul_one polyOne)).trans
        (RatPolyCoeffEqv.mul_one g))
  have hneg := (neg_smul _).trans (((hb.mul hb).smul (-1)).trans (neg_smul _).symm)
  exact (((RatPolyCoeffEqv.refl A).mul hH).add hneg).trans
    (((RatPolyCoeffEqv.refl _).add (neg_smul _)).trans
      (RatPolyCoeffEqv.add_neg_smul (polyMul A A)))

private theorem mass_zero (w : Q') (K width : Nat) :
    weightedMass w K width polyZero ≈ 0 :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.zero_smul polyOne).symm)
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width 0 polyOne) (Q'.zero_mul_eqv _))

/-- Counterexample to arbitrary input-norm-to-conditional-noise conversion,
using the same original terminal source and its constructed positive mass. -/
theorem terminal_input_not_le_noise {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (stage t : Nat) (c : Q') :
    ¬ weightedMass w K width
        (polyMul (terminalMessage w K width stage) (terminalMessage w K width stage)) ≤
      c * weightedMass w K width
        (blockNoise w K width t (terminalMessage w K width stage) polyOne) := by
  intro h
  have hz : weightedMass w K width
      (blockNoise w K width t (terminalMessage w K width stage) polyOne) ≈ 0 :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width
      (blockNoise_one w K width t (terminalMessage w K width stage))) (mass_zero w K width)
  have hr : c * weightedMass w K width
      (blockNoise w K width t (terminalMessage w K width stage) polyOne) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ hz) (Q'.mul_zero_eqv c)
  have hle := Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr)
  exact (Int.lt_irrefl _) (Q'.lt_of_le_of_lt hle
    (terminalPair_positive hw0 hw1 K width hK stage stage))

#print axioms blockNoise_one
#print axioms terminal_input_not_le_noise

end YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalNoiseVacuumObstruction
