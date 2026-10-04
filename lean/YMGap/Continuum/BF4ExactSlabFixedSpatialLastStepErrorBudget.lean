/-
# Original last-step paired budget of a reconstruction error

For arbitrary signed supported a,e, let M=T1,A=Ta,U=T(a^2),E=T(e^2).
The actual paired budget J(a,e) has the constructed polynomial ceiling
  J(a,e) <= P(a)*E,  P(a)=2*M*(A^2+M*U).
The difference is the sum of a full original K*V plus-pair square and
2*M*U times the actual one-step Schur gap M*E-(Te)^2.

This controls an incoming reciprocal reconstruction error; it does not
bound the leading ratio-noise or complete signed cost by a surviving norm.
Every transfer and two-slice weight remains the original fixed-spatial one.
No positivity of the signed inputs, inverse, or family estimate is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
  (lastStepScoreBudget lastStepPairedResidual_square_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression
  (lastStepRegressionGram lastStepRegressionGram_certificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative (partialHaarHeads_add)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- Computed positive multiplier; no amplitude or source norm is inverted. -/
def lastStepErrorBudgetMultiplier (w : Q') (K width : Nat) (a : RatPoly) : RatPoly :=
  let M := transferStep w K width polyOne
  let A := transferStep w K width a
  let U := transferStep w K width (polyMul a a)
  polyMul (cap 2) (polyMul M (polyAdd (polyMul A A) (polyMul M U)))

theorem lastStepErrorBudgetMultiplier_supported (w : Q') (K width : Nat)
    {a : RatPoly} (ha : SupportedQuaternionBlocks (N width) a) :
    SupportedQuaternionBlocks (N width) (lastStepErrorBudgetMultiplier w K width a) := by
  have hM := transferStep_supported w K width (supported_one (N width))
  have hA := transferStep_supported w K width ha
  have hU := transferStep_supported w K width (supported_polyMul ha ha)
  have htwo : SupportedQuaternionBlocks (N width) (cap 2) := by
    intro term ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact supported_one (N width) s hs
  exact supported_polyMul htwo
    (supported_polyMul hM (supported_add (supported_polyMul hA hA)
      (supported_polyMul hM hU)))

/-- The multiplier is positive even when a is signed. -/
def lastStepErrorBudgetMultiplier_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) :
    Certificate (N width) (lastStepErrorBudgetMultiplier w K width a) := by
  let PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  let PU := transferStep_certificate hw0 hw1 K width hK
    (supported_polyMul ha ha) (Certificate.square a ha)
  exact (Certificate.constant (N width) 2 (by decide)).mul
    (PM.mul ((Certificate.square (transferStep w K width a)
      (transferStep_supported w K width ha)).add (PM.mul PU)))

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem plus_pair_pin (w : Q') (K width : Nat) (a e : RatPoly) :
    let A := transferStep w K width a
    let b := transferStep w K width e
    let X := polyAdd (polyMul (liftBoundary (N width) A) e)
      (polyMul (liftBoundary (N width) b) a)
    let C := polyMul (polyMul A b) (transferStep w K width (polyMul a e))
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (stepWeight w K width) (polyMul X X)))
      (polyAdd (polyMul (polyMul A A) (transferStep w K width (polyMul e e)))
        (polyAdd (polyAdd C C)
          (polyMul (polyMul b b) (transferStep w K width (polyMul a a))))) := by
  dsimp only
  let W := stepWeight w K width
  let A := transferStep w K width a
  let b := transferStep w K width e
  let X := polyAdd (polyMul (liftBoundary (N width) A) e)
    (polyMul (liftBoundary (N width) b) a)
  let cross := polyMul (polyMul W (polyMul a e))
    (liftBoundary (N width) (polyMul A b))
  have he : RatPolyCoeffEqv (polyMul W (polyMul X X))
      (polyAdd
        (polyMul (polyMul W (polyMul e e)) (liftBoundary (N width) (polyMul A A)))
        (polyAdd (polyAdd cross cross)
          (polyMul (polyMul W (polyMul a a)) (liftBoundary (N width) (polyMul b b))))) := by
    dsimp only [X, cross]
    rw [lift_product, lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))))
      (.add (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 1) (.var 1)))
        (.add (.add
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 2))) (.mul (.var 1) (.var 3)))
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 2))) (.mul (.var 1) (.var 3))))
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 4))) (.mul (.var 3) (.var 3)))))
      (by decide) (fun
        | 0 => W
        | 1 => liftBoundary (N width) A
        | 2 => e
        | 3 => liftBoundary (N width) b
        | _ => a)
  have pin (p R : RatPoly) : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (polyMul W p) (liftBoundary (N width) R)))
      (polyMul R (transferStep w K width p)) :=
    (partialHaarHeads_mul_lift (N width) (polyMul W p) R).trans
      (((transferStep_kernelMap w K width p).symm.mul_right R).trans
        (RatPolyCoeffEqv.mul_comm _ R))
  have h := partialHaarHeads_congr (N width) he
  rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add] at h
  exact h.trans ((pin (polyMul e e) (polyMul A A)).add
    (((pin (polyMul a e) (polyMul A b)).add
      (pin (polyMul a e) (polyMul A b))).add
      (pin (polyMul a a) (polyMul b b))))

/-- Exact polynomial ceiling of the old paired-residual error budget.
The full original K*V weight is positive; a and e need not be positive. -/
def lastStepScoreBudget_error_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {a e : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (he : SupportedQuaternionBlocks (N width) e) :
    Certificate (N width) (polyAdd
      (polyMul (lastStepErrorBudgetMultiplier w K width a)
        (transferStep w K width (polyMul e e)))
      (polyNeg (lastStepScoreBudget w K width a e))) := by
  let M := transferStep w K width polyOne
  let A := transferStep w K width a
  let b := transferStep w K width e
  let U := transferStep w K width (polyMul a a)
  let E := transferStep w K width (polyMul e e)
  let C := polyMul (polyMul A b) (transferStep w K width (polyMul a e))
  let X := polyAdd (polyMul (liftBoundary (N width) A) e)
    (polyMul (liftBoundary (N width) b) a)
  have hX : SupportedQuaternionBlocks (N width+N width) X :=
    supported_add
      (supported_polyMul (lift_supported (transferStep_supported w K width ha) (N width))
        (support_mono he (by omega)))
      (supported_polyMul (lift_supported (transferStep_supported w K width he) (N width))
        (support_mono ha (by omega)))
  let PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  let PU := transferStep_certificate hw0 hw1 K width hK
    (supported_polyMul ha ha) (Certificate.square a ha)
  let Pplus := partialHaarHeads_certificate (N width) (N width)
    ((stepWeightCertificate hw0 hw1 K width hK).mul (Certificate.square X hX))
  have PN : Certificate (N width) (polyAdd (polyMul M E) (polyNeg (polyMul b b))) := by
    have hM := transfer_congr w K width (RatPolyCoeffEqv.one_mul polyOne)
    have hb := transfer_congr w K width (RatPolyCoeffEqv.one_mul e)
    exact Certificate.ofCoeff
      ((hM.mul (RatPolyCoeffEqv.refl E)).add (RatPolyCoeffEqv.neg (hb.mul hb))).symm
      (lastStepRegressionGram_certificate hw0 hw1 K width hK (supported_one (N width)) he)
  have PP : Certificate (N width)
      (polyMul M (polyAdd (polyMul (polyMul A A) E)
        (polyAdd (polyAdd C C) (polyMul (polyMul b b) U)))) :=
    PM.mul (Certificate.ofCoeff (plus_pair_pin w K width a e).symm Pplus)
  have PS := ((Certificate.constant (N width) 2 (by decide)).mul (PM.mul PU)).mul PN
  have hJ := (lastStepPairedResidual_square_pin w K width a e).mul_left M
  refine Certificate.ofCoeff
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hJ)).trans ?_) (PP.add PS)
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.const 2) (.mul (.var 0)
      (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 2))))) (.var 3))
      (.neg (.mul (.var 0) (.add (.mul (.mul (.var 1) (.var 1)) (.var 3))
        (.add (.neg (.add (.var 5) (.var 5))) (.mul (.mul (.var 4) (.var 4)) (.var 2)))))))
    (.add (.mul (.var 0) (.add (.mul (.mul (.var 1) (.var 1)) (.var 3))
      (.add (.add (.var 5) (.var 5)) (.mul (.mul (.var 4) (.var 4)) (.var 2)))))
      (.mul (.mul (.const 2) (.mul (.var 0) (.var 2)))
        (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 4) (.var 4))))))
    (by decide) (fun
      | 0 => M
      | 1 => A
      | 2 => U
      | 3 => E
      | 4 => b
      | _ => C)

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepScoreBudget_error_certificate
