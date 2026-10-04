/-
# Original last-step prediction residual and energy payment

For a=g_d, A=T a and b=T(a*phi), the literal prediction residual
R=T(a*phi^2)-2*phi*b+A*phi^2 is the conditional integral of
K*V*a*(phi_lower-phi_upper)^2. Thus R has a constructed certificate.
The exact identity A*R=N+(b-A*phi)^2 retains the positive innovation
and prediction error. Weighted symmetry gives ell(a*R)=2*energy(a,phi).
The actual gap-one terminal upper bracket then pays BOTH squares by
2*U*energy, with no extra norm debt or source/variance inverse.

All original action factors and the supplied signed phi are retained.
No small energy, relative survival, changing-family uniformity, physical
scaling or continuum/QFT statement is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
  (stepWeight stepWeightCertificate transferStep_kernelMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison (filteredTerminalBracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy jump jump_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative (partialHaarHeads_add partialHaarHeads_neg)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration (partialHaarHeads_certificate)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks weightedMass terminalMessage kineticWeight spatialWeight

/-- Two identical negative cross terms represent the literal factor -2. -/
def lastStepPredictionResidual (w : Q') (K width d : Nat) (phi : RatPoly) : RatPoly :=
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let b := transferStep w K width (polyMul a phi)
  let H := transferStep w K width (polyMul a (polyMul phi phi))
  let cross := polyMul phi b
  polyAdd H (polyAdd (polyNeg cross) (polyAdd (polyNeg cross) (polyMul A (polyMul phi phi))))

/-- Prediction is made in the SAME original incoming source coordinates. -/
def lastStepPredictionError (w : Q') (K width d : Nat) (phi : RatPoly) : RatPoly :=
  let a := terminalMessage w K width d
  polyAdd (transferStep w K width (polyMul a phi))
    (polyNeg (polyMul (transferStep w K width a) phi))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem lastStepPredictionError_supported (w : Q') (K width d : Nat)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    SupportedQuaternionBlocks (N width) (lastStepPredictionError w K width d phi) :=
  supported_add
    (transferStep_supported w K width (supported_polyMul
      (terminalMessage_supported w K width d) hphi))
    (support_neg (supported_polyMul
      (transferStep_supported w K width (terminalMessage_supported w K width d)) hphi))

private theorem prediction_integral_pin (w : Q') (K width d : Nat) (phi : RatPoly) :
    let a := terminalMessage w K width d
    let W := polyMul (stepWeight w K width) a
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul W (polyMul (jump width phi) (jump width phi))))
      (lastStepPredictionResidual w K width d phi) := by
  dsimp only
  let a := terminalMessage w K width d
  let W := polyMul (stepWeight w K width) a
  let cross := polyMul (polyMul W phi) (liftBoundary (N width) phi)
  have he : RatPolyCoeffEqv (polyMul W (polyMul (jump width phi) (jump width phi)))
      (polyAdd (polyMul W (polyMul phi phi))
        (polyAdd (polyNeg cross) (polyAdd (polyNeg cross)
          (polyMul W (liftBoundary (N width) (polyMul phi phi)))))) := by
    dsimp only [jump, cross]
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 2)))))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))
          (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))
            (.mul (.var 0) (.mul (.var 2) (.var 2))))))
      (by decide) (fun
        | 0 => W
        | 1 => phi
        | _ => liftBoundary (N width) phi)
  have lower (p : RatPoly) : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul W p))
      (transferStep w K width (polyMul a p)) :=
    (partialHaarHeads_congr (N width) (RatPolyCoeffEqv.mul_assoc (stepWeight w K width) a p)).trans
      (transferStep_kernelMap w K width (polyMul a p)).symm
  have hm : RatPolyCoeffEqv (partialHaarHeads (N width) W) (transferStep w K width a) :=
    (transferStep_kernelMap w K width a).symm
  have hc : RatPolyCoeffEqv (partialHaarHeads (N width) cross)
      (polyMul phi (transferStep w K width (polyMul a phi))) :=
    (partialHaarHeads_mul_lift (N width) (polyMul W phi) phi).trans
      (((lower phi).mul_right phi).trans (RatPolyCoeffEqv.mul_comm _ phi))
  have ht : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul W (liftBoundary (N width) (polyMul phi phi))))
      (polyMul (transferStep w K width a) (polyMul phi phi)) :=
    (partialHaarHeads_mul_lift (N width) W (polyMul phi phi)).trans (hm.mul_right _)
  have h := partialHaarHeads_congr (N width) he
  rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add] at h
  exact h.trans ((lower (polyMul phi phi)).add
    (((partialHaarHeads_neg (N width) cross).trans (RatPolyCoeffEqv.neg hc)).add
      (((partialHaarHeads_neg (N width) cross).trans (RatPolyCoeffEqv.neg hc)).add ht)))

/-- Positivity comes from the ORIGINAL K*V*a square, not from a supplied
prediction bound, a normalized conditional law or an inverse terminal. -/
def lastStepPredictionResidual_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (d : Nat) {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    Certificate (N width) (lastStepPredictionResidual w K width d phi) := by
  let PW := (stepWeightCertificate hw0 hw1 K width hK).mul
    (certificate_extend (N width) (terminalMessage_supported w K width d)
      (terminalMessage_certificate hw0 hw1 K width hK d))
  let P := partialHaarHeads_certificate (N width) (N width)
    (PW.mul (Certificate.square (jump width phi) (jump_supported width hphi)))
  exact Certificate.ofCoeff (prediction_integral_pin w K width d phi).symm P

/-- Exact conditional innovation PLUS squared prediction error. -/
theorem lastStepPredictionResidual_pin (w : Q') (K width d : Nat) (phi : RatPoly) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let q := lastStepPredictionError w K width d phi
    RatPolyCoeffEqv (polyMul A (lastStepPredictionResidual w K width d phi))
      (polyAdd (lastStepRatioNoise w K width d phi) (polyMul q q)) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let b := transferStep w K width (polyMul a phi)
  let H := transferStep w K width (polyMul a (polyMul phi phi))
  have he : RatPolyCoeffEqv (polyMul A (lastStepPredictionResidual w K width d phi))
      (polyAdd (polyAdd (polyMul A H) (polyNeg (polyMul b b)))
        (polyMul (lastStepPredictionError w K width d phi) (lastStepPredictionError w K width d phi))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1)
        (.add (.neg (.mul (.var 3) (.var 2)))
          (.add (.neg (.mul (.var 3) (.var 2))) (.mul (.var 0) (.mul (.var 3) (.var 3)))))))
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
        (.mul (.add (.var 2) (.neg (.mul (.var 0) (.var 3))))
          (.add (.var 2) (.neg (.mul (.var 0) (.var 3))))))
      (by decide) (fun
        | 0 => A
        | 1 => H
        | 2 => b
        | _ => phi)
  exact he.trans ((lastStepRatioNoise_pin w K width d phi).symm.add (.refl _))

private theorem mass_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -weightedMass w K width p :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

private theorem mass_difference (w : Q') (K width : Nat) (p q : RatPoly) :
    weightedMass w K width (polyAdd p (polyNeg q)) ≈
      weightedMass w K width p + -weightedMass w K width q :=
  Q'.eqv_trans _ _ _ (weightedMass_add w K width p (polyNeg q))
    (Q'.add_eqv_congr_left _ _ _ (mass_neg w K width q))

/-- Actual original edge energy, with diagonal V*a*T a and no recentering. -/
theorem lastStepPredictionResidual_energy_pin (w : Q') (K width d : Nat)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    weightedMass w K width (polyMul (terminalMessage w K width d)
      (lastStepPredictionResidual w K width d phi)) ≈
      (2 : Q')*energy w K width (terminalMessage w K width d) phi := by
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let b := transferStep w K width (polyMul a phi)
  let H := transferStep w K width (polyMul a (polyMul phi phi))
  let diag := polyMul (polyMul a A) (polyMul phi phi)
  let mix := polyMul (polyMul a phi) b
  have hsym := transferStep_weighted_symmetric w K width
    (supported_polyMul (terminalMessage_supported w K width d) (supported_polyMul hphi hphi))
    (terminalMessage_supported w K width d)
  have hreorder : RatPolyCoeffEqv (polyMul (polyMul a (polyMul phi phi)) A) diag :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
      (by decide) (fun
        | 0 => a
        | 1 => phi
        | _ => A)
  have hdiag : weightedMass w K width (polyMul a H) ≈ weightedMass w K width diag :=
    Q'.eqv_trans _ _ _ hsym (weightedMass_congr w K width hreorder)
  have he : RatPolyCoeffEqv (polyMul a (lastStepPredictionResidual w K width d phi))
      (polyAdd (polyMul a H) (polyAdd (polyNeg mix) (polyAdd (polyNeg mix) diag))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1)
        (.add (.neg (.mul (.var 2) (.var 3)))
          (.add (.neg (.mul (.var 2) (.var 3))) (.mul (.var 4) (.mul (.var 2) (.var 2)))))))
      (.add (.mul (.var 0) (.var 1))
        (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3)))
          (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3)))
            (.mul (.mul (.var 0) (.var 4)) (.mul (.var 2) (.var 2))))))
      (by decide) (fun
        | 0 => a
        | 1 => H
        | 2 => phi
        | 3 => b
        | _ => A)
  have hsum := Q'.eqv_trans _ _ _ (weightedMass_congr w K width he)
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' hdiag
        (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
          (Q'.add_eqv_congr' (mass_neg w K width mix)
            (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
              (Q'.add_eqv_congr_right _ _ _ (mass_neg w K width mix)))))))
  exact Q'.eqv_trans _ _ _ hsum
    (poly_identity_of_normal_eq
      (.add (.var 0) (.add (.neg (.var 1)) (.add (.neg (.var 1)) (.var 0))))
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun
        | 0 => weightedMass w K width diag
        | _ => weightedMass w K width mix))

/-- The CONSTRUCTED terminal upper comparison pays innovation and prediction
error by the literal energy. No norm debt, stationarity or small-energy premise. -/
theorem lastStepNoise_prediction_energy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (d : Nat) (hdepth : 1 ≤ d) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) :
    let U := (filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth).upper
    let q := lastStepPredictionError w K width d phi
    weightedMass w K width (lastStepRatioNoise w K width d phi)+
      weightedMass w K width (polyMul q q) ≤
      (2*U)*energy w K width (terminalMessage w K width d) phi := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let R := lastStepPredictionResidual w K width d phi
  let q := lastStepPredictionError w K width d phi
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth
  have Pupper : Certificate (N width) (polyAdd (polySmul J.upper a) (polyNeg A)) := by
    have hA : A = terminalMessage w K width (d+1) := terminalMessage_next w K width d
    rw [hA]
    exact Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add (neg_smul _)) J.upperCertificate
  have he : RatPolyCoeffEqv (polyMul (polyAdd (polySmul J.upper a) (polyNeg A)) R)
      (polyAdd (polySmul J.upper (polyMul a R)) (polyNeg (polyMul A R))) :=
    (((cap_mul_left J.upper a).symm.add (.refl _)).mul (.refl R)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.var 2))) (.var 3))
        (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.neg (.mul (.var 2) (.var 3))))
        (by decide) (fun
          | 0 => polySmul J.upper polyOne
          | 1 => a
          | 2 => A
          | _ => R)).trans ((cap_mul_left J.upper _).add (.refl _)))
  have hn := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.ofCoeff he.symm (Pupper.mul
      (lastStepPredictionResidual_certificate hw0 hw1 K width hK d hphi)))
  have horder := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn
    (Q'.le_of_eqv (mass_difference w K width (polySmul J.upper (polyMul a R)) (polyMul A R))))
  have hleft : weightedMass w K width (polyMul A R) ≈
      weightedMass w K width (lastStepRatioNoise w K width d phi)+
        weightedMass w K width (polyMul q q) :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width (lastStepPredictionResidual_pin w K width d phi))
      (weightedMass_add w K width _ _)
  have hright : weightedMass w K width (polySmul J.upper (polyMul a R)) ≈
      (2*J.upper)*energy w K width a phi :=
    Q'.eqv_trans _ _ _ (weightedMass_smul w K width J.upper (polyMul a R))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left J.upper _ _ (lastStepPredictionResidual_energy_pin w K width d hphi))
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 2) (.var 1)))
          (.mul (.mul (.const 2) (.var 0)) (.var 1)) (by decide)
          (fun
            | 0 => J.upper
            | _ => energy w K width a phi)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ horder (Q'.le_of_eqv hright))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lastStepPredictionResidual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lastStepPredictionError
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lastStepPredictionError_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lastStepPredictionResidual_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lastStepPredictionResidual_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lastStepPredictionResidual_energy_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lastStepNoise_prediction_energy_le
