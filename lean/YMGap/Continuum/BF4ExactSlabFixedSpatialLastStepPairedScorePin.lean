/-
# Three paired output scores from the last ORIGINAL transfer step

The full half-open action, including its spatial source and lifted unit,
produces both outgoing messages. Differentiation is at the surviving upper
block N+s before N lower heads are integrated. The incoming a,c are arbitrary
lower-supported polynomials, and the paired residual is unchanged. This is
the three-direction coefficient pin for the existing exact original score;
it does not factor c as a times an observable or differentiate frozen weights.

The single-plane argument follows the private derivative_integral_pin and
paired_integral in BF4ExactSlabFixedSpatialLastStepScoreVariance. The target
uses pairedScorePlus from QuaternionHaarConditionalScorePairedFrame.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
import YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame
import YMGap.Continuum.SU2QuaternionPairedFrameAt

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
  (lastStepPairedResidual)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (supported_upper_independent)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (pairedScorePlus)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- The literal full last-step action, including its lifted unit. -/
def lastStepAction (w : Q') (K width : Nat) : RatPoly :=
  halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) 1

/-- Integrating the same full action produces the original transfer output. -/
theorem action_integral_pin (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul (lastStepAction w K width) p))
      (transferStep w K width p) := by
  refine (partialHaarHeads_congr (N width)
    ((RatPolyCoeffEqv.mul_comm _ p).trans
      ((RatPolyCoeffEqv.mul_one p).symm.mul_right _))).trans ?_
  simpa only [windowMessage, Nat.one_mul, transferStep, iterateStep, lastStepAction] using
    windowMessage_one (N width) (kineticWeight w K width) (spatialWeight w K width) 1 p

private theorem derivative_integral_pin (w : Q') (K width s i j : Nat)
    (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j))
          (lastStepAction w K width)) p))
      (angularDerivative (4*s+i) (4*s+j) (transferStep w K width p)) := by
  have hz := angularDerivative_blockIndependent_zero hi hj (supported_upper_independent hp s)
  have hz' : RatPolyCoeffEqv
      (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j)) p) polyZero := by
    simpa only [Nat.mul_add, Nat.add_assoc] using hz
  have hd : RatPolyCoeffEqv
      (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j))
        (polyMul (lastStepAction w K width) p))
      (polyMul (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j))
        (lastStepAction w K width)) p) :=
    (angularDerivative_mul _ _ _ p).trans
      (((RatPolyCoeffEqv.refl _).add
        ((hz'.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _))).trans
        (RatPolyCoeffEqv.add_zero _))
  exact ((angularDerivative_partialHaarHeads (N width) (4*s+i) (4*s+j) _).trans
    (partialHaarHeads_congr (N width) hd)).symm.trans
      (angularDerivative_congr _ _ (action_integral_pin w K width p))

private theorem paired_integral (heads : Nat) (P A b a c : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyMul P
        (polyAdd (polyMul (liftBoundary heads A) c)
          (polyNeg (polyMul (liftBoundary heads b) a)))))
      (polyAdd (polyMul A (partialHaarHeads heads (polyMul P c)))
        (polyNeg (polyMul b (partialHaarHeads heads (polyMul P a))))) := by
  have hsplit := partialHaarHeads_congr heads
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 4)))))
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (.neg (.mul (.mul (.var 0) (.var 4)) (.var 3))))
      (by decide) (fun
        | 0 => P | 1 => liftBoundary heads A | 2 => c
        | 3 => liftBoundary heads b | _ => a))
  change RatPolyCoeffEqv
    (partialHaarHeads heads (polyMul P (polyAdd (polyMul (liftBoundary heads A) c)
      (polyNeg (polyMul (liftBoundary heads b) a)))))
    (partialHaarHeads heads (polyAdd (polyMul (polyMul P c) (liftBoundary heads A))
      (polyNeg (polyMul (polyMul P a) (liftBoundary heads b))))) at hsplit
  rw [partialHaarHeads_add] at hsplit
  exact hsplit.trans
    (((partialHaarHeads_mul_lift heads (polyMul P c) A).trans
      (RatPolyCoeffEqv.mul_comm _ A)).add
      ((partialHaarHeads_neg heads _).trans
        (RatPolyCoeffEqv.neg ((partialHaarHeads_mul_lift heads (polyMul P a) b).trans
          (RatPolyCoeffEqv.mul_comm _ b)))))

/-- One upper-plane derivative of the full original action gives the
unchanged two-source output score. -/
theorem plane_score_integral_pin (w : Q') (K width s i j : Nat)
    (hi : i < 4) (hj : j < 4) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j))
          (lastStepAction w K width))
        (lastStepPairedResidual w K width a c)))
      (conditionalScore (4*s+i) (4*s+j)
        (transferStep w K width a) (transferStep w K width c)) := by
  exact (paired_integral (N width) _ (transferStep w K width a)
    (transferStep w K width c) a c).trans
    (((derivative_integral_pin w K width s i j hi hj hc).mul_left _).add
      (RatPolyCoeffEqv.neg
        ((derivative_integral_pin w K width s i j hi hj ha).mul_left _)))

private theorem integrated_add (heads : Nat) (X P Q : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyMul (polyAdd P Q) X))
      (polyAdd (partialHaarHeads heads (polyMul P X))
        (partialHaarHeads heads (polyMul Q X))) := by
  rw [polyMul_add_left_exact, partialHaarHeads_add]
  exact RatPolyCoeffEqv.refl _

private theorem integrated_neg (heads : Nat) (X P : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyMul (polyNeg P) X))
      (polyNeg (partialHaarHeads heads (polyMul P X))) := by
  have h : RatPolyCoeffEqv (polyMul (polyNeg P) X) (polyNeg (polyMul P X)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => P | _ => X)
  exact (partialHaarHeads_congr heads h).trans (partialHaarHeads_neg heads _)

/-- The three actual upper-block paired generators integrate to the
existing (+,-,+) paired score of the two original transfer outputs. -/
theorem paired_score_integral_pin (w : Q') (K width s : Nat) (i : Fin 3)
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (pairedDerivativeAt (N width+s) i (lastStepAction w K width))
        (lastStepPairedResidual w K width a c)))
      (pairedScorePlus s (transferStep w K width a) (transferStep w K width c) i) := by
  let X := lastStepPairedResidual w K width a c
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    subst i
    change RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (polyAdd
          (angularDerivative (4*(N width+s)+0) (4*(N width+s)+1) (lastStepAction w K width))
          (angularDerivative (4*(N width+s)+2) (4*(N width+s)+3) (lastStepAction w K width))) X))
      (polyAdd (conditionalScore (4*s+0) (4*s+1) (transferStep w K width a)
          (transferStep w K width c))
        (conditionalScore (4*s+2) (4*s+3) (transferStep w K width a)
          (transferStep w K width c)))
    simpa only [Nat.mul_add, Nat.add_assoc] using
      (integrated_add (N width) X _ _).trans
        ((plane_score_integral_pin w K width s 0 1 (by decide) (by decide) ha hc).add
          (plane_score_integral_pin w K width s 2 3 (by decide) (by decide) ha hc))
  · by_cases h1 : i.val = 1
    · have hi : i = 1 := Fin.ext h1
      subst i
      change RatPolyCoeffEqv
        (partialHaarHeads (N width) (polyMul
          (polyAdd
            (angularDerivative (4*(N width+s)+0) (4*(N width+s)+2) (lastStepAction w K width))
            (polyNeg (angularDerivative (4*(N width+s)+1) (4*(N width+s)+3)
              (lastStepAction w K width)))) X))
        (polyAdd (conditionalScore (4*s+0) (4*s+2) (transferStep w K width a)
            (transferStep w K width c))
          (polyNeg (conditionalScore (4*s+1) (4*s+3) (transferStep w K width a)
            (transferStep w K width c))))
      simpa only [Nat.mul_add, Nat.add_assoc] using
        (integrated_add (N width) X _ _).trans
          ((plane_score_integral_pin w K width s 0 2 (by decide) (by decide) ha hc).add
            ((integrated_neg (N width) X _).trans
              (RatPolyCoeffEqv.neg
                (plane_score_integral_pin w K width s 1 3 (by decide) (by decide) ha hc))))
    · have hi : i = 2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      change RatPolyCoeffEqv
        (partialHaarHeads (N width) (polyMul
          (polyAdd
            (angularDerivative (4*(N width+s)+0) (4*(N width+s)+3) (lastStepAction w K width))
            (angularDerivative (4*(N width+s)+1) (4*(N width+s)+2) (lastStepAction w K width))) X))
        (polyAdd (conditionalScore (4*s+0) (4*s+3) (transferStep w K width a)
            (transferStep w K width c))
          (conditionalScore (4*s+1) (4*s+2) (transferStep w K width a)
            (transferStep w K width c)))
      simpa only [Nat.mul_add, Nat.add_assoc] using
        (integrated_add (N width) X _ _).trans
          ((plane_score_integral_pin w K width s 0 3 (by decide) (by decide) ha hc).add
            (plane_score_integral_pin w K width s 1 2 (by decide) (by decide) ha hc))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin.lastStepAction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin.action_integral_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin.plane_score_integral_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin.paired_score_integral_pin
