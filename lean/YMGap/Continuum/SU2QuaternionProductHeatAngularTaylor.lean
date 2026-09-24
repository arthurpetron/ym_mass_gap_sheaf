/-
# Source-cancelled first order of the actual full-product heat energy

The computed Casimir tree equals a cyclic differential sweep. Pairing in
the rotating frame cancels every derivative of the endpoint source at
first order. Weighted coordinate transport returns the sum over the original
blocks. Both signed higher-order remainders remain in the exact identity.

The resulting factor-one angular estimate has a source-dependent quadratic
remainder; it is not a source-free, scaling-uniform or SAME-variance bound.
-/

import YMGap.Continuum.SU2QuaternionCyclicSourceCancellation
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionCyclicWeightedAngular
open YMGap.Continuum.SU2QuaternionCyclicSourceCancellation
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Angular cost of the observable with the square of the complete source.
This weight is not identified with a stationary or odd-time marginal. -/
def weightedAngularEnergy (tail : Nat) (a f : RatPoly) : Q' :=
  finSum (fun i => H (tail+1)
    (polyMul (polyMul a a) (blockAngularSquare i f))) (tail+1)

private theorem rotatedAngularSum_finSum (tail : Nat) :
    ∀ (m : Nat) (a f : RatPoly),
    rotatedAngularSum tail m a f ≈
      finSum (fun i => H (tail+1) (polyMul
        (polyMul (rotateIterate (tail+1) i a) (rotateIterate (tail+1) i a))
        (angularSquare (rotateIterate (tail+1) i f)))) m
  | 0, _, _ => Q'.eqv_refl _
  | m+1, a, f => by
      have hi := rotatedAngularSum_finSum tail m
        (SU2QuaternionProductHeatCyclicRotation.cycleRotation (tail+1) a)
        (SU2QuaternionProductHeatCyclicRotation.cycleRotation (tail+1) f)
      have hs := finSum_eqv_congr
        (fun i => H (tail+1) (polyMul
          (polyMul
            (rotateIterate (tail+1) i (SU2QuaternionProductHeatCyclicRotation.cycleRotation (tail+1) a))
            (rotateIterate (tail+1) i (SU2QuaternionProductHeatCyclicRotation.cycleRotation (tail+1) a)))
          (angularSquare
            (rotateIterate (tail+1) i (SU2QuaternionProductHeatCyclicRotation.cycleRotation (tail+1) f)))))
        (fun i => H (tail+1) (polyMul
          (polyMul (rotateIterate (tail+1) (i+1) a) (rotateIterate (tail+1) (i+1) a))
          (angularSquare (rotateIterate (tail+1) (i+1) f)))) (fun i => by
        dsimp only
        rw [rotateIterate_succ_right (tail+1) i a,
          rotateIterate_succ_right (tail+1) i f]
        exact Q'.eqv_refl _) m
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ hi hs))
        (Q'.eqv_symm (finSum_peel_left _ m))

private theorem pairCasimir_sweepPair (tail : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    pairCasimir tail p test ≈ sweepPair tail (tail+1) p test := by
  have hperiod := rotateIterate_period_carrier (tail+1) test ht
    (casimirSweep tail (tail+1) p)
  exact Q'.eqv_trans _ _ _ (pairCasimir_sweep tail p test hp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hperiod)
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- The computed full-product first-order coefficient has NO source
derivatives: all six angular planes at every original block are retained. -/
theorem sourceFirstOrder_eq_weightedAngularEnergy (tail : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceFirstOrder tail a f ≈ weightedAngularEnergy tail a f := by
  have haf := supported_polyMul ha hf
  have hstart := Q'.add_eqv_congr'
    (pairCasimir_sweepPair tail (polyMul a f) (polyMul a f) haf haf)
    (Q'.neg_eqv_congr _ _ (pairCasimir_sweepPair tail a
      (polyMul a (polyMul f f)) ha (supported_polyMul ha (supported_polyMul hf hf))))
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ (sourceSweep_eq_rotatedAngularSum tail (tail+1) a f ha hf)
      (Q'.eqv_trans _ _ _ (rotatedAngularSum_finSum tail (tail+1) a f)
        (finSum_eqv_congr_lt _ _ (tail+1) (fun i hi =>
          rotateIterate_head_weightedAngularSquare_haar_of_lt tail i hi a f ha hf))))

/-- Exact first-order source cancellation with BOTH signed remainders. -/
theorem sourceEnergy_taylor_angular (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≈
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
        (pairRemainder tail w K a (polyMul a (polyMul f f)) +
          -(pairRemainder tail w K (polyMul a f) (polyMul a f))) :=
  Q'.eqv_trans _ _ _ (sourceEnergy_taylor tail w K a f ha hf)
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (sourceFirstOrder_eq_weightedAngularEnergy tail a f ha hf))
      (Q'.eqv_refl _))

/-- Factor one at first order, with the complete source-dependent quadratic
budget explicitly retained. No uniformity for changing sources is asserted. -/
theorem sourceEnergy_le_angular_add_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
        (((1 : Q')-w)*((1 : Q')-w))*sourceTaylorBudget tail a f :=
  Q'.le_trans' _ _ _ (sourceEnergy_le_firstOrder_add_quadratic tail hw0 hw1 K hK a f ha hf)
    (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (sourceFirstOrder_eq_weightedAngularEnergy tail a f ha hf))
      (Q'.eqv_refl _)))

end YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor.sourceFirstOrder_eq_weightedAngularEnergy
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor.sourceEnergy_taylor_angular
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor.sourceEnergy_le_angular_add_quadratic
