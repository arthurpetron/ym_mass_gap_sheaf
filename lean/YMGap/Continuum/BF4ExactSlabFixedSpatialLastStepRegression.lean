/-
# Exact conditional regression split of the ORIGINAL last-step square

The paired residual is NOT identified with a lone conditional variance.
Clearing U=T(a^2) gives U*J=A^2*(U*H-C^2)+(U*b-A*C)^2. The Gram term
has an actual full-slice shared-tail two-copy certificate; the other term
is the explicit conditional-mean mismatch. No inverse, stationary message,
positive signed source or SAME surviving-norm estimate is assumed.
The last-step residual/budget is exactly invariant under c -> c+lambda*a;
this does not assert mean-shift invariance of the complete signed cost.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
import YMGap.Continuum.SU2QuaternionMultiHeadConditionalGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionMultiHeadConditionalGram
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- Actual two-input Gram determinant after the SAME complete original step. -/
def lastStepRegressionGram (w : Q') (K width : Nat) (a c : RatPoly) : RatPoly :=
  let U := transferStep w K width (polyMul a a)
  let H := transferStep w K width (polyMul c c)
  let C := transferStep w K width (polyMul a c)
  polyAdd (polyMul U H) (polyNeg (polyMul C C))

/-- The actual output ratio and the least-squares conditional center need
not agree. Their mismatch is retained without dividing by U or A. -/
def lastStepRegressionMismatch (w : Q') (K width : Nat) (a c : RatPoly) : RatPoly :=
  let U := transferStep w K width (polyMul a a)
  let C := transferStep w K width (polyMul a c)
  polyAdd (polyMul U (transferStep w K width c))
    (polyNeg (polyMul (transferStep w K width a) C))

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

/-- Full-slice two-copy producer: positivity of a,c is NOT a premise. -/
def lastStepRegressionGram_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    Certificate (N width) (lastStepRegressionGram w K width a c) := by
  let W := stepWeight w K width
  have hW : SupportedQuaternionBlocks (N width+N width) W :=
    supported_polyMul (kineticWeight_supported w K width)
      (support_mono (spatialWeight_supported w K width) (by omega))
  have P := conditionalGram_certificate (N width) (N width) W a c hW
    (support_mono ha (by omega)) (support_mono hc (by omega))
    (stepWeightCertificate hw0 hw1 K width hK)
  have pin (p : RatPoly) : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul W p)) (transferStep w K width p) :=
    (transferStep_kernelMap w K width p).symm
  exact Certificate.ofCoeff
    (((pin (polyMul a a)).mul (pin (polyMul c c))).add
      (RatPolyCoeffEqv.neg ((pin (polyMul a c)).mul (pin (polyMul a c))))).symm P

/-- Exact division-free regression decomposition of the budget. M=T1 is
retained, and the mean-mismatch square is NOT silently discarded. -/
theorem lastStepScoreBudget_regression_pin (w : Q') (K width : Nat) (a c : RatPoly) :
    let A := transferStep w K width a
    let U := transferStep w K width (polyMul a a)
    let E := lastStepRegressionMismatch w K width a c
    RatPolyCoeffEqv (polyMul U (lastStepScoreBudget w K width a c))
      (polyMul (transferStep w K width polyOne)
        (polyAdd (polyMul (polyMul A A) (lastStepRegressionGram w K width a c))
          (polyMul E E))) := by
  dsimp only
  have h := ((lastStepPairedResidual_square_pin w K width a c).mul_left
    (transferStep w K width polyOne)).mul_left (transferStep w K width (polyMul a a))
  refine h.trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 2) (.mul (.var 5)
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 4))
        (.add (.neg (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
          (.mul (.mul (.var 0) (.var 1)) (.var 3))))
          (.mul (.mul (.var 1) (.var 1)) (.var 2))))))
    (.mul (.var 5)
      (.add (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.var 2) (.var 4)) (.neg (.mul (.var 3) (.var 3)))))
        (.mul (.add (.mul (.var 2) (.var 1)) (.neg (.mul (.var 0) (.var 3))))
          (.add (.mul (.var 2) (.var 1)) (.neg (.mul (.var 0) (.var 3)))))))
    (by decide) (fun
      | 0 => transferStep w K width a
      | 1 => transferStep w K width c
      | 2 => transferStep w K width (polyMul a a)
      | 3 => transferStep w K width (polyMul a c)
      | 4 => transferStep w K width (polyMul c c)
      | _ => transferStep w K width polyOne)

/-- Addition of the incoming vacuum direction cancels in the actual paired
residual, by original transfer linearity. -/
theorem lastStepPairedResidual_shift (w : Q') (K width : Nat) (a c : RatPoly) (s : Q') :
    RatPolyCoeffEqv
      (lastStepPairedResidual w K width a (polyAdd c (polySmul s a)))
      (lastStepPairedResidual w K width a c) := by
  have hT := (transferStep_add w K width c (polySmul s a)).trans
    ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width s a))
  have hL := lift_coeff (N width) hT
  dsimp only [lastStepPairedResidual]
  refine ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (hL.mul_right a))).trans ?_
  rw [lift_add, lift_smul]
  refine (((RatPolyCoeffEqv.refl _).mul
    ((RatPolyCoeffEqv.refl c).add (cap_mul_left s a).symm)).add
    (RatPolyCoeffEqv.neg (((RatPolyCoeffEqv.refl _).add
      (cap_mul_left s _).symm).mul_right a))).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.var 1) (.mul (.var 4) (.var 2))))
      (.neg (.mul (.add (.var 3) (.mul (.var 4) (.var 0))) (.var 2))))
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 3) (.var 2))))
    (by decide) (fun
      | 0 => liftBoundary (N width) (transferStep w K width a)
      | 1 => c | 2 => a
      | 3 => liftBoundary (N width) (transferStep w K width c)
      | _ => cap s)

/-- Only the leading paired budget is center-independent. This does not
erase the finite reciprocal correction or drift in the COMPLETE cost. -/
theorem lastStepScoreBudget_shift (w : Q') (K width : Nat) (a c : RatPoly) (s : Q') :
    RatPolyCoeffEqv
      (lastStepScoreBudget w K width a (polyAdd c (polySmul s a)))
      (lastStepScoreBudget w K width a c) := by
  have h := lastStepPairedResidual_shift w K width a c s
  exact (partialHaarHeads_congr (N width) ((h.mul h).mul_left _)).mul_left _

#print axioms lastStepRegressionGram
#print axioms lastStepRegressionMismatch
#print axioms lastStepRegressionGram_certificate
#print axioms lastStepScoreBudget_regression_pin
#print axioms lastStepPairedResidual_shift
#print axioms lastStepScoreBudget_shift

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression
