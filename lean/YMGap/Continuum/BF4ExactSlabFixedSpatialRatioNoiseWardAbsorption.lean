/-
# Actual one-plane reciprocal Ward absorption of the ratio-noise source jet

The ORIGINAL terminal marginal, projected spatial weight and successor
reciprocal are retained. A produced conditional square absorbs the
phi-gradient cross term with coefficient one. Both signed derivatives of
the complete incoming density and the outgoing spatial weight remain.
This is not their sign/smallness estimate, a surviving-norm bound or scaling.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
import YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign
import YMGap.Continuum.SU2QuaternionConditionalGrussSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticFloor_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
open YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative
open YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productMap productMap_independent_of_not_mem)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
  (familyProject_mean familyProject_mul_of_independent)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative (partialHaarHeads_add)
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign
open YMGap.Continuum.SU2QuaternionConditionalGrussSquare
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder (kineticCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap_positive headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (SquareBound)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- The density derivative retains the FULL original V*a, not V alone. -/
def ratioNoiseDensityMoment (w : Q') (K width s i j : Nat) (a phi : RatPoly) : RatPoly :=
  let X := matchedNoiseResidual w K width a phi
  partialHaarHeads (N width) (polyMul (kineticWeight w K width)
    (polyMul (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) a))
      (polyMul X X)))

/-- Exact split of the actual cleared noise derivative into density and
twice the literal mixed source moment. No positivity or support is used. -/
theorem noiseDerivativeIncoming_moment_pin (w : Q') (K width s i j : Nat) (a phi : RatPoly) :
    let A := transferStep w K width a
    let M := ratioNoiseGradientMoment w K width s i j a phi
    RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
      (noiseDerivativeIncoming w K width s i j a phi)))
      (polyAdd (ratioNoiseDensityMoment w K width s i j a phi)
        (polyAdd (polyMul A M) (polyMul A M))) := by
  dsimp only
  let P := kineticWeight w K width
  let g := polyMul (spatialWeight w K width) a
  let A := transferStep w K width a
  let X := matchedNoiseResidual w K width a phi
  let t := angularDerivative (4*s+i) (4*s+j) phi
  let z := polyMul (polyMul g X) t
  let densityInput := polyMul (angularDerivative (4*s+i) (4*s+j) g) (polyMul X X)
  let mixedInput := polyMul (polyMul (polyMul g (liftBoundary (N width) A)) X) t
  have hm : RatPolyCoeffEqv (polyMul P (polyMul (polyMul (polyMul g (liftBoundary (N width) A)) X) t))
      (polyMul (polyMul P z) (liftBoundary (N width) A)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.var 4)))
      (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.var 4))) (.var 2))
      (by decide) (fun
        | 0 => P
        | 1 => g
        | 2 => liftBoundary (N width) A
        | 3 => X
        | _ => t)
  have hpull := (partialHaarHeads_congr (N width) hm).trans
    ((partialHaarHeads_mul_lift (N width) (polyMul P z) A).trans
      (RatPolyCoeffEqv.mul_comm _ A))
  have hdist := (RatPolyCoeffEqv.mul_add_right P densityInput (polyAdd mixedInput mixedInput)).trans
    ((RatPolyCoeffEqv.refl (polyMul P densityInput)).add
      (RatPolyCoeffEqv.mul_add_right P mixedInput mixedInput))
  have h := partialHaarHeads_congr (N width) hdist
  rw [partialHaarHeads_add, partialHaarHeads_add] at h
  exact h.trans ((RatPolyCoeffEqv.refl _).add (hpull.add hpull))

private theorem haar_add (n : Nat) (p q : RatPoly) :
    quaternionHaar n (polyAdd p q) ≈ quaternionHaar n p+quaternionHaar n q :=
  quaternionHaar_append n p q

private theorem haar_neg (n : Nat) (r p : RatPoly) :
    quaternionHaar n (polyMul r (polyNeg p)) ≈ -quaternionHaar n (polyMul r p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((neg_smul p).mul_left r))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (-1) r p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

/-- Shared original Ward calculation BEFORE selecting an absorption payment.
The literal mixed source moment and both signed corrections are retained. -/
private theorem original_ratioNoise_ward_signed_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (k : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let noise := matchedNoise w K width a phi
    let F := polyMul (polyMul V V) noise
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
    let J := angularDerivative (4*s+i) (4*s+j)
    let R := polyMul (polyMul V V) (polyMul G G)
    let density := polyMul (polyMul R (J A)) (ratioNoiseDensityMoment w K width s i j a phi)
    let spatial := polyMul (polyMul (polyMul (polyMul A (polyMul G G)) (J A)) V)
      (polyMul (J V) noise)
    quaternionHaar (N width) (polyMul (polyMul F (polyMul G G))
      (polyAdd (polyMul A (J (J A))) (polyNeg (polyMul (J A) (J A))))) ≤
      (quaternionHaar (N width) (polyMul R (polyNeg (polyAdd
        (polyMul noise (polyMul (J A) (J A)))
        (polyMul (polyAdd (polyMul A (J A)) (polyMul A (J A)))
          (ratioNoiseGradientMoment w K width s i j a phi))))) +
        -quaternionHaar (N width) density) +
      -(quaternionHaar (N width) spatial+quaternionHaar (N width) spatial) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let noise := matchedNoise w K width a phi
  let F := polyMul (polyMul V V) noise
  let G := reciprocal A (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
  let J := angularDerivative (4*s+i) (4*s+j)
  let D := J A
  let R := polyMul (polyMul V V) (polyMul G G)
  let M := ratioNoiseGradientMoment w K width s i j a phi
  let Q := ratioNoiseDensityMoment w K width s i j a phi
  let L0 := polyAdd (polyMul noise (polyMul D D))
    (polyMul (polyAdd (polyMul A D) (polyMul A D)) M)
  let density := polyMul (polyMul R D) Q
  let spatial := polyMul (polyMul (polyMul (polyMul A (polyMul G G)) D) V) (polyMul (J V) noise)
  let correction := polyMul (polyMul (polyMul A (polyMul G G)) D) (J F)
  have ha := terminalMessage_supported w K width d
  have hA := transferStep_supported w K width ha
  have hV := spatialFringeMass_supported w K width
  let PN : Certificate (N width) noise := lastStepRatioNoise_certificate hw0 hw1 K width hK d hphi
  let PF := (Certificate.square V hV).mul PN
  have hnext : A = terminalMessage w K width (d+1) := terminalMessage_next w K width d
  have PU : Certificate (N width) (polyAdd (cap (blockWindowUpper w K width d 1)) (polyNeg A)) := by
    rw [hnext]
    exact (blockWindowCertificates hw0 hw1 K width hK d 1 (by omega)).2
  have hward := finite_reciprocal_hessian_ibp_le hs hi hj
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) hA PF PU k
  have hder := weightedNoise_derivative_carrier w K width s i j hs hi hj ha hphi V
  have hsplit := noiseDerivativeIncoming_moment_pin w K width s i j a phi
  have hraw : RatPolyCoeffEqv correction (polyMul (polyMul (polyMul G G) D) (polyMul A (J F))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2)) (.var 3))
      (.mul (.mul (.mul (.var 1) (.var 1)) (.var 2)) (.mul (.var 0) (.var 3)))
      (by decide) (fun
        | 0 => A
        | 1 => G
        | 2 => D
        | _ => J F)
  have hsub := (HaarCarrierEqv.add (HaarCarrierEqv.refl (N width)
    (polyAdd (polyMul F D) (polyAdd
      (polyMul (polyMul (polyMul A V) (J V)) noise)
      (polyMul (polyMul (polyMul A V) (J V)) noise))))
    (RatPolyCoeffEqv.haarCarrier (hsplit.mul_left (polyMul V V)))).mul_left
      (polyMul (polyMul G G) D)
  have hring : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul G G) D)
        (polyAdd (polyAdd (polyMul F D)
          (polyAdd (polyMul (polyMul (polyMul A V) (J V)) noise)
            (polyMul (polyMul (polyMul A V) (J V)) noise)))
          (polyMul (polyMul V V) (polyAdd Q (polyAdd (polyMul A M) (polyMul A M))))))
      (polyAdd (polyAdd (polyMul R L0) density) (polyAdd spatial spatial)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 2) (.var 2)) (.var 3))
        (.add (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 4)) (.var 3))
          (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 7)) (.var 4))
            (.mul (.mul (.mul (.var 0) (.var 1)) (.var 7)) (.var 4))))
          (.mul (.mul (.var 1) (.var 1)) (.add (.var 6)
            (.add (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 5)))))))
      (.add (.add
        (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))
          (.add (.mul (.var 4) (.mul (.var 3) (.var 3)))
            (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 3))) (.var 5))))
        (.mul (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.var 3)) (.var 6)))
        (.add
          (.mul (.mul (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 3)) (.var 1))
            (.mul (.var 7) (.var 4)))
          (.mul (.mul (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 3)) (.var 1))
            (.mul (.var 7) (.var 4)))))
      (by decide) (fun
        | 0 => A
        | 1 => V
        | 2 => G
        | 3 => D
        | 4 => noise
        | 5 => M
        | 6 => Q
        | _ => J V)
  have hcorr : quaternionHaar (N width) correction ≈
      (quaternionHaar (N width) (polyMul R L0)+quaternionHaar (N width) density)+
        (quaternionHaar (N width) spatial+quaternionHaar (N width) spatial) := by
    have hcar := (RatPolyCoeffEqv.haarCarrier hraw).trans
      ((hder.mul_left (polyMul (polyMul G G) D)).trans
        (hsub.trans (RatPolyCoeffEqv.haarCarrier hring)))
    exact Q'.eqv_trans _ _ _ (haar_of_carrier hcar)
      (Q'.eqv_trans _ _ _ (haar_add (N width) _ _)
        (Q'.add_eqv_congr' (haar_add (N width) _ _) (haar_add (N width) _ _)))
  have hcorrNeg : -quaternionHaar (N width) correction ≈
      (quaternionHaar (N width) (polyMul R (polyNeg L0)) + -quaternionHaar (N width) density)+
        -(quaternionHaar (N width) spatial+quaternionHaar (N width) spatial) :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hcorr)
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.neg (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 2))))
        (.add (.add (.neg (.var 0)) (.neg (.var 1))) (.neg (.add (.var 2) (.var 2))))
        (by decide) (fun
          | 0 => quaternionHaar (N width) (polyMul R L0)
          | 1 => quaternionHaar (N width) density
          | _ => quaternionHaar (N width) spatial))
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (haar_neg (N width) R L0)))))
  exact Q'.le_trans' _ _ _ hward (Q'.le_of_eqv hcorrNeg)

/-- SAME original one-plane Ward bound. The source-gradient cross is paid,
but neither signed spatial/density response is discarded or assigned a sign.
The outgoing reciprocal degree is the arbitrary successor k+1. -/
theorem original_ratioNoise_ward_absorption_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (k : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let noise := matchedNoise w K width a phi
    let F := polyMul (polyMul V V) noise
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
    let J := angularDerivative (4*s+i) (4*s+j)
    let R := polyMul (polyMul V V) (polyMul G G)
    let density := polyMul (polyMul R (J A)) (ratioNoiseDensityMoment w K width s i j a phi)
    let spatial := polyMul (polyMul (polyMul (polyMul A (polyMul G G)) (J A)) V)
      (polyMul (J V) noise)
    quaternionHaar (N width) (polyMul (polyMul F (polyMul G G))
      (polyAdd (polyMul A (J (J A))) (polyNeg (polyMul (J A) (J A))))) ≤
      (quaternionHaar (N width) (polyMul R (polyMul (polyMul (polyMul A A) A)
        (ratioNoiseGradientEnergy w K width s i j a phi))) + -quaternionHaar (N width) density) +
      -(quaternionHaar (N width) spatial+quaternionHaar (N width) spatial) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let G := reciprocal A (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
  have hA := transferStep_supported w K width (terminalMessage_supported w K width d)
  have hG := reciprocal_supported hA (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
  let PR := (Certificate.square V (spatialFringeMass_supported w K width)).mul
    (Certificate.square G hG)
  exact Q'.le_trans' _ _ _
    (original_ratioNoise_ward_signed_le hw0 hw1 K width hK d s i j hs hi hj hphi k)
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _
      (original_ratioNoise_phiGradient_absorption_le hw0 hw1 K width hK d s i j
        hs hi hj hphi PR)))

/-- Centering the ACTUAL absorption square removes the predictable incoming
gradient. The positive payment is its conditional NOISE, not its full second
moment. Both signed original density/spatial corrections keep every factor. -/
theorem original_ratioNoise_ward_noiseGradient_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (k : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let noise := matchedNoise w K width a phi
    let F := polyMul (polyMul V V) noise
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
    let J := angularDerivative (4*s+i) (4*s+j)
    let R := polyMul (polyMul V V) (polyMul G G)
    let density := polyMul (polyMul R (J A)) (ratioNoiseDensityMoment w K width s i j a phi)
    let spatial := polyMul (polyMul (polyMul (polyMul A (polyMul G G)) (J A)) V)
      (polyMul (J V) noise)
    quaternionHaar (N width) (polyMul (polyMul F (polyMul G G))
      (polyAdd (polyMul A (J (J A))) (polyNeg (polyMul (J A) (J A))))) ≤
      (quaternionHaar (N width) (polyMul R (polyMul (polyMul A A)
        (matchedNoise w K width a (J phi)))) + -quaternionHaar (N width) density) +
      -(quaternionHaar (N width) spatial+quaternionHaar (N width) spatial) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let G := reciprocal A (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
  have hA := transferStep_supported w K width (terminalMessage_supported w K width d)
  have hG := reciprocal_supported hA (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
  let PR := (Certificate.square V (spatialFringeMass_supported w K width)).mul
    (Certificate.square G hG)
  exact Q'.le_trans' _ _ _
    (original_ratioNoise_ward_signed_le hw0 hw1 K width hK d s i j hs hi hj hphi k)
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _
      (original_ratioNoise_phiGradient_noise_absorption_le hw0 hw1 K width hK d s i j
        hs hi hj hphi PR)))

/-- The produced finite multiplier cap removes G only from the POSITIVE
gradient payment, with coefficient one for every degree and no floor loss.
The original interacting incoming derivative energy is retained. -/
theorem original_ratioNoise_gradientPayment_unit_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (k : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) k
    let E := ratioNoiseGradientEnergy w K width s i j a phi
    quaternionHaar (N width) (polyMul (polyMul (polyMul V V) (polyMul G G))
      (polyMul (polyMul (polyMul A A) A) E)) ≤
      quaternionHaar (N width) (polyMul (polyMul V V) (polyMul A E)) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let G := reciprocal A (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) k
  let t := angularDerivative (4*s+i) (4*s+j) phi
  let E := ratioNoiseGradientEnergy w K width s i j a phi
  let bare := polyMul (polyMul V V) (polyMul A E)
  let payment := polyMul (polyMul (polyMul V V) (polyMul G G))
    (polyMul (polyMul (polyMul A A) A) E)
  have ha := terminalMessage_supported w K width d
  have hA := transferStep_supported w K width ha
  have ht := angularDerivative_supported_at (by omega : 4*s+i < 4*N width)
    (by omega : 4*s+j < 4*N width) hphi
  let Pa := terminalMessage_certificate hw0 hw1 K width hK d
  let PA : Certificate (N width) A := transferStep_certificate hw0 hw1 K width hK ha Pa
  let PE : Certificate (N width) E := transferStep_certificate hw0 hw1 K width hK
    (supported_polyMul ha (supported_polyMul ht ht)) (Pa.mul (Certificate.square t ht))
  have hnext : A = terminalMessage w K width (d+1) := terminalMessage_next w K width d
  let bands := blockWindowCertificates hw0 hw1 K width hK d 1 (by omega)
  have hle : blockWindowLower w K width d 1 ≤ blockWindowUpper w K width d 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (d+1-1)))
  let Pcap := multiplierSquareCertificate hA
    (blockWindowLower_positive hw0 hw1 K width hK d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) hle
    (show Certificate (N width) (polyAdd A (polyNeg (cap (blockWindowLower w K width d 1)))) by
      rw [hnext]; exact bands.1)
    (show Certificate (N width) (polyAdd (cap (blockWindowUpper w K width d 1)) (polyNeg A)) by
      rw [hnext]; exact bands.2) k
  let Pbase := ((Certificate.square V (spatialFringeMass_supported w K width)).mul PA).mul PE
  have hgap : RatPolyCoeffEqv (polyAdd bare (polyNeg payment))
      (polyMul (polyMul (polyMul (polyMul V V) A) E)
        (polyAdd polyOne (polyNeg (polyMul (polyMul A G) (polyMul A G))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))
          (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 2)))))
      (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2))
        (.add (.const 1) (.neg (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3))))))
      (by decide) (fun | 0 => V | 1 => A | 2 => E | _ => G)
  have hpos := (Certificate.ofCoeff hgap (Pbase.mul Pcap)).haar_nonnegative
  have hneg : quaternionHaar (N width) (polyNeg payment) ≈
      -quaternionHaar (N width) payment :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul payment))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (-1) payment)
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (haar_add (N width) bare (polyNeg payment))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hneg))))

/-- Actual Ward consumer with a reciprocal-free positive payment. BOTH
signed original density/spatial responses keep their successor reciprocal.
No comparison with surviving variance or sign for those responses is used. -/
theorem original_ratioNoise_ward_unitGradient_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (k : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let noise := matchedNoise w K width a phi
    let F := polyMul (polyMul V V) noise
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
    let J := angularDerivative (4*s+i) (4*s+j)
    let R := polyMul (polyMul V V) (polyMul G G)
    let density := polyMul (polyMul R (J A)) (ratioNoiseDensityMoment w K width s i j a phi)
    let spatial := polyMul (polyMul (polyMul (polyMul A (polyMul G G)) (J A)) V)
      (polyMul (J V) noise)
    quaternionHaar (N width) (polyMul (polyMul F (polyMul G G))
      (polyAdd (polyMul A (J (J A))) (polyNeg (polyMul (J A) (J A))))) ≤
      (quaternionHaar (N width) (polyMul (polyMul V V)
        (polyMul A (ratioNoiseGradientEnergy w K width s i j a phi))) +
        -quaternionHaar (N width) density) +
      -(quaternionHaar (N width) spatial+quaternionHaar (N width) spatial) := by
  exact Q'.le_trans' _ _ _
    (original_ratioNoise_ward_absorption_le hw0 hw1 K width hK d s i j hs hi hj hphi k)
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _
      (original_ratioNoise_gradientPayment_unit_le hw0 hw1 K width hK d s i j
        hs hi hj hphi (k+1))))

/-- The produced multiplier-square cap removes the outgoing reciprocal from
the centered gradient payment. Positivity is the ACTUAL conditional noise
certificate, not an assumed sign for either original correction. Degree zero
and zero source/noise are retained. -/
theorem original_ratioNoise_noiseGradientPayment_unit_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (k : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) k
    let t := angularDerivative (4*s+i) (4*s+j) phi
    quaternionHaar (N width) (polyMul (polyMul (polyMul V V) (polyMul G G))
      (polyMul (polyMul A A) (matchedNoise w K width a t))) ≤
      quaternionHaar (N width) (polyMul (polyMul V V) (matchedNoise w K width a t)) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let G := reciprocal A (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) k
  let t := angularDerivative (4*s+i) (4*s+j) phi
  let noise := matchedNoise w K width a t
  let bare := polyMul (polyMul V V) noise
  let payment := polyMul (polyMul (polyMul V V) (polyMul G G))
    (polyMul (polyMul A A) noise)
  have ha := terminalMessage_supported w K width d
  have hA := transferStep_supported w K width ha
  have ht := angularDerivative_supported_at (by omega : 4*s+i < 4*N width)
    (by omega : 4*s+j < 4*N width) hphi
  let PN : Certificate (N width) noise := lastStepRatioNoise_certificate hw0 hw1 K width hK d ht
  have hnext : A = terminalMessage w K width (d+1) := terminalMessage_next w K width d
  let bands := blockWindowCertificates hw0 hw1 K width hK d 1 (by omega)
  have hle : blockWindowLower w K width d 1 ≤ blockWindowUpper w K width d 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (d+1-1)))
  let Pcap := multiplierSquareCertificate hA
    (blockWindowLower_positive hw0 hw1 K width hK d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) hle
    (show Certificate (N width) (polyAdd A (polyNeg (cap (blockWindowLower w K width d 1)))) by
      rw [hnext]; exact bands.1)
    (show Certificate (N width) (polyAdd (cap (blockWindowUpper w K width d 1)) (polyNeg A)) by
      rw [hnext]; exact bands.2) k
  let Pbase := (Certificate.square V (spatialFringeMass_supported w K width)).mul PN
  have hgap : RatPolyCoeffEqv (polyAdd bare (polyNeg payment))
      (polyMul bare (polyAdd polyOne (polyNeg (polyMul (polyMul A G) (polyMul A G))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.neg (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))
          (.mul (.mul (.var 1) (.var 1)) (.var 2)))))
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.add (.const 1) (.neg (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3))))))
      (by decide) (fun | 0 => V | 1 => A | 2 => noise | _ => G)
  have hpos := (Certificate.ofCoeff hgap (Pbase.mul Pcap)).haar_nonnegative
  have hneg : quaternionHaar (N width) (polyNeg payment) ≈
      -quaternionHaar (N width) payment :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul payment))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (-1) payment)
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (haar_add (N width) bare (polyNeg payment))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hneg))))

/-- Reciprocal-free positive payment is now only the original conditional
variance of Jphi. The SAME signed density and spatial corrections remain;
this is not a relative bound on their sum or a changing-family estimate. -/
theorem original_ratioNoise_ward_unitNoiseGradient_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (k : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let noise := matchedNoise w K width a phi
    let F := polyMul (polyMul V V) noise
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
    let J := angularDerivative (4*s+i) (4*s+j)
    let R := polyMul (polyMul V V) (polyMul G G)
    let density := polyMul (polyMul R (J A)) (ratioNoiseDensityMoment w K width s i j a phi)
    let spatial := polyMul (polyMul (polyMul (polyMul A (polyMul G G)) (J A)) V)
      (polyMul (J V) noise)
    quaternionHaar (N width) (polyMul (polyMul F (polyMul G G))
      (polyAdd (polyMul A (J (J A))) (polyNeg (polyMul (J A) (J A))))) ≤
      (quaternionHaar (N width) (polyMul (polyMul V V)
        (matchedNoise w K width a (J phi))) + -quaternionHaar (N width) density) +
      -(quaternionHaar (N width) spatial+quaternionHaar (N width) spatial) := by
  exact Q'.le_trans' _ _ _
    (original_ratioNoise_ward_noiseGradient_le hw0 hw1 K width hK d s i j hs hi hj hphi k)
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _
      (original_ratioNoise_noiseGradientPayment_unit_le hw0 hw1 K width hK d s i j
        hs hi hj hphi (k+1))))

private theorem transfer_fringe_independent (w : Q') (K width : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (b : Nat)
    (hb : b ∈ fringeBlocks width) :
    QuaternionBlockIndependent b (transferStep w K width p) := by
  have hproduct : transferStep w K width p = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) p) := by
    unfold transferStep step productMap kernelMap
    rw [kineticWeight_eq_indexedProduct]
    rfl
  rw [hproduct]
  exact productMap_independent_of_not_mem (N width) w K (activeBlocks width)
    (activeBlocks_lt width) b (fringeBlocks_lt width b hb)
    (((fringeBlocks_mem_iff width b).mp hb).2) _
    (supported_polyMul (spatialWeight_supported w K width) hp)

/-- Exact pullback of the positive Ward payment to ORIGINAL incoming
coordinates. The transferred factor is T(Vbar*Ta), NOT Ta or T^2a.
This pin does not equate an angular square with finite-step jump energy. -/
theorem original_ratioNoise_gradientPayment_weighted_pin (w : Q') (K width : Nat)
    (d s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let t := angularDerivative (4*s+i) (4*s+j) phi
    quaternionHaar (N width) (polyMul (polyMul V V)
      (polyMul A (ratioNoiseGradientEnergy w K width s i j a phi))) ≈
      weightedMass w K width (polyMul (polyMul a (polyMul t t))
        (transferStep w K width (polyMul V A))) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let t := angularDerivative (4*s+i) (4*s+j) phi
  let x := polyMul a (polyMul t t)
  let E := transferStep w K width x
  let r := polyMul V A
  let p := polyMul r E
  have ha := terminalMessage_supported w K width d
  have hA := transferStep_supported w K width ha
  have ht := angularDerivative_supported_at (by omega : 4*s+i < 4*N width)
    (by omega : 4*s+j < 4*N width) hphi
  have hx := supported_polyMul ha (supported_polyMul ht ht)
  have hr := supported_polyMul (spatialFringeMass_supported w K width) hA
  have hind : ∀ b, b ∈ fringeBlocks width → QuaternionBlockIndependent b p := by
    intro b hb
    have hAI : QuaternionBlockIndependent b A := by
      rw [show A = terminalMessage w K width (d+1) from terminalMessage_next w K width d]
      exact terminal_fringe_independent w K width (d+1) b hb
    exact quaternionBlockIndependent_polyMul
      (quaternionBlockIndependent_polyMul (spatialFringeMass_independent w K width b hb) hAI)
      (transfer_fringe_independent w K width hx b hb)
  have hproject := familyProject_mul_of_independent (fringeBlocks width) p
    (spatialWeight w K width) hind
  have hmean := familyProject_mean (N width) (fringeBlocks width)
    (fringeBlocks_lt width) (polyMul p (spatialWeight w K width))
  have hring : RatPolyCoeffEqv (polyMul p V)
      (polyMul (polyMul V V) (polyMul A E)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 0))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => V | 1 => A | _ => E)
  have hweighted : weightedMass w K width p ≈
      quaternionHaar (N width) (polyMul (polyMul V V) (polyMul A E)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ p))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hmean)
        (Q'.eqv_trans _ _ _ (haar_of_coeff hproject) (haar_of_coeff hring)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hweighted)
    (transferStep_weighted_symmetric w K width hx hr)

/-- Exact original-law pullback of the smaller payment. It subtracts the
ACTUAL transmitted incoming-gradient square and still keeps T(Vbar*Ta).
No stationary measure, independent gradient mean or spectral pin is used. -/
theorem original_ratioNoise_noiseGradientPayment_weighted_pin (w : Q') (K width : Nat)
    (d s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let t := angularDerivative (4*s+i) (4*s+j) phi
    let m := transferStep w K width (polyMul a t)
    quaternionHaar (N width) (polyMul (polyMul V V) (matchedNoise w K width a t)) ≈
      weightedMass w K width (polyMul (polyMul a (polyMul t t))
        (transferStep w K width (polyMul V A))) +
      -quaternionHaar (N width) (polyMul (polyMul V V) (polyMul m m)) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let t := angularDerivative (4*s+i) (4*s+j) phi
  let E := ratioNoiseGradientEnergy w K width s i j a phi
  let m := transferStep w K width (polyMul a t)
  let predicted := polyMul (polyMul V V) (polyMul m m)
  have hpoly : RatPolyCoeffEqv
      (polyMul (polyMul V V) (matchedNoise w K width a t))
      (polyAdd (polyMul (polyMul V V) (polyMul A E)) (polyNeg predicted)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 3)))))
      (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))))
      (by decide) (fun | 0 => V | 1 => A | 2 => E | _ => m)
  have hneg : quaternionHaar (N width) (polyNeg predicted) ≈
      -quaternionHaar (N width) predicted :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul predicted))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (-1) predicted)
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
    (Q'.eqv_trans _ _ _ (haar_add (N width) _ _)
      (Q'.add_eqv_congr'
        (original_ratioNoise_gradientPayment_weighted_pin w K width d s i j hs hi hj hphi) hneg))

private theorem densityMoment_input_pin (w : Q') (K width : Nat) (a p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads (N width)
      (polyMul (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) a)) p))
      (transferStep w K width (polyMul a p)) :=
  partialHaarHeads_congr (N width)
    ((RatPolyCoeffEqv.mul_assoc (kineticWeight w K width)
      (polyMul (spatialWeight w K width) a) p).trans
      ((RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) a p).mul_left _))

private theorem densityMoment_mean_carrier (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) :
    HaarCarrierEqv (N width)
      (angularDerivative (4*s+i) (4*s+j) (transferStep w K width a))
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
        (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) a)))) := by
  rw [transferStep_eq_productMap, kineticWeight_eq_indexedProduct]
  exact productMap_angular_carrier (N width) s i j hs hi hj w K
    (activeBlocks width) (activeBlocks_lt width) _
    (supported_polyMul (spatialWeight_supported w K width) ha)

/-- The ACTUAL density correction has a produced centered-covariance square
budget. Both the mean-derivative square and the residual-noise square are
retained. The explicit nome-dependent local cutoff covers an active physical
link, not an arbitrary fringe direction. No mass/noise inverse or conditional
variance premise is used; the bound alone is not a changing-family payment. -/
def original_ratioNoise_densityCovariance_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : endpointRelativeCutoff w ≤ K) (d : Nat)
    (selected : ClusterCount4DProgress.Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {phi : RatPoly} {C : Q'}
    (hphi : SupportedQuaternionBlocks (N width) phi)
    (Pphi : Certificate (N width) (polyAdd (cap (C*C)) (polyNeg (polyMul phi phi)))) :
    let s := (baseLinks width).idxOf selected
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let noise := matchedNoise w K width a phi
    let D := angularDerivative (4*s+i) (4*s+j) A
    let Q := ratioNoiseDensityMoment w K width s i j a phi
    let centered := polyAdd Q (polyNeg (polyMul noise D))
    let L := endpointRelativeCap w
    let coefficient := polyAdd (polyMul (cap (L*L)) (polyMul A A))
      (polyNeg (polyMul D D))
    let fourth := polyAdd
      (polyMul (polyMul (cap (4*(C*C))) (polyMul (polyMul A A) (polyMul A A))) noise)
      (polyNeg (polyMul (polyMul A A) (polyMul noise noise)))
    Certificate (N width) (polyAdd (polyMul coefficient fourth)
      (polyNeg (polyMul (polyMul A A) (polyMul centered centered)))) := by
  dsimp only
  let s := (baseLinks width).idxOf selected
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let g := polyMul (spatialWeight w K width) a
  let P := kineticWeight w K width
  let W := polyMul P g
  let J := angularDerivative (4*s+i) (4*s+j)
  let tilt := polyMul P (J g)
  let D0 := partialHaarHeads (N width) tilt
  let X := matchedNoiseResidual w K width a phi
  let noise := matchedNoise w K width a phi
  let L := endpointRelativeCap w
  let coefficient := centeredRelativeCoefficient (N width) W tilt L
  let fourth := polyAdd
    (polyMul (polyMul (cap (4*(C*C))) (polyMul (polyMul A A) (polyMul A A))) noise)
    (polyNeg (polyMul (polyMul A A) (polyMul noise noise)))
  let Q := ratioNoiseDensityMoment w K width s i j a phi
  let centered := polyAdd Q (polyNeg (polyMul noise D0))
  have hidx : s < N width := List.idxOf_lt_length_of_mem hl
  have hhead : headCutoff w ≤ K := Nat.le_trans
    (Nat.le_trans (headCutoff_le_relativeCutoff w 4096) (Nat.le_max_left _ _)) hK
  have ha := terminalMessage_supported w K width d
  have hg := supported_polyMul (spatialWeight_supported w K width) ha
  have hJg := angularDerivative_supported_at
    (by omega : 4*s+i < 4*N width) (by omega : 4*s+j < 4*N width) hg
  have extend {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
      SupportedQuaternionBlocks (N width+N width) p := fun t ht =>
    Nat.le_trans (hp t ht) (by omega)
  have support_neg {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
      SupportedQuaternionBlocks blocks (polyNeg p) := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    exact hp r hr
  have hW := supported_polyMul (kineticWeight_supported w K width) (extend hg)
  have htilt := supported_polyMul (kineticWeight_supported w K width) (extend hJg)
  have hA := transferStep_supported w K width ha
  have hb := transferStep_supported w K width (supported_polyMul ha hphi)
  have hX := supported_add (supported_polyMul (lift_supported hA (N width)) (extend hphi))
    (support_neg (lift_supported hb (N width)))
  let relative := endpointSourceRelativeBound hw0 hw1 K width hK d selected hl hs hi hj
  let PK := kineticCertificate hw0 hw1 K width hhead
  let PW := PK.mul (certificate_extend (N width) hg relative.positive)
  have hplus := supported_add (supported_polyMul (SquareBound.constant (N width) L).support hg) hJg
  have hminus := supported_add (supported_polyMul (SquareBound.constant (N width) L).support hg)
    (support_neg hJg)
  let Pplus : Certificate (N width+N width) (polyAdd (polyMul (cap L) W) tilt) :=
    Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => cap L | 1 => P | 2 => g | _ => J g))
      (PK.mul (certificate_extend (N width) hplus relative.lower))
  let Pminus : Certificate (N width+N width) (polyAdd (polyMul (cap L) W) (polyNeg tilt)) :=
    Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.neg (.var 3))))
        (by decide) (fun | 0 => cap L | 1 => P | 2 => g | _ => J g))
      (PK.mul (certificate_extend (N width) hminus relative.upper))
  have hL : (0 : Q') < L := Q'.pos_of_lt_of_le
    (Q'.mul_pos (by decide : (0 : Q') < 6)
      (relativeCap_positive hw0 (by decide : (0 : Q') ≤ 4096)))
    (Q'.add_le_self_of_nonneg _ _
      (Q'.le_of_lt (relativeCap_positive hw0 (by decide : (0 : Q') ≤ 32))))
  have hcap := supported_add (SquareBound.constant (N width) (C*C)).support
    (support_neg (supported_polyMul hphi hphi))
  let Pcap := certificate_extend (N width) hcap Pphi
  let nu := determinant (N width) W phi
  let X0 := polyAdd (polyMul (liftBoundary (N width) A) phi)
    (polyNeg (liftBoundary (N width) (partialHaarHeads (N width) (polyMul W phi))))
  have hnu : RatPolyCoeffEqv nu noise :=
    ((RatPolyCoeffEqv.refl A).mul (densityMoment_input_pin w K width a (polyMul phi phi))).add
      (RatPolyCoeffEqv.neg ((densityMoment_input_pin w K width a phi).mul
        (densityMoment_input_pin w K width a phi)))
  have hX0 : RatPolyCoeffEqv X0 X := (RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.neg (lift_coeff (N width) (densityMoment_input_pin w K width a phi)))
  have hXX := hX0.mul hX0
  have hmoment := partialHaarHeads_congr (N width) (hXX.mul_left W)
  have hmean : RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul W (polyMul X X)))
      (polyMul A noise) := hmoment.symm.trans
    ((residual_square_pin (N width) W phi).trans (hnu.mul_left A))
  have hdet : RatPolyCoeffEqv (determinant (N width) W (polyMul X0 X0))
      (determinant (N width) W (polyMul X X)) :=
    ((RatPolyCoeffEqv.refl A).mul (partialHaarHeads_congr (N width)
      ((hXX.mul hXX).mul_left W))).add (RatPolyCoeffEqv.neg (hmoment.mul hmoment))
  let Pvariance := squaredResidualVariance_certificate (N width) (N width) W phi C
    hW (extend hphi) PW Pcap
  have hvariance : RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul (polyMul (cap (4*(C*C))) (polyMul (polyMul A A) (polyMul A A))) nu)
          (polyNeg (polyMul (polyMul A A) (polyMul nu nu))))
        (polyNeg (determinant (N width) W (polyMul X0 X0))))
      (polyAdd fourth (polyNeg (determinant (N width) W (polyMul X X)))) :=
    (((hnu.mul_left _).add (RatPolyCoeffEqv.neg ((hnu.mul hnu).mul_left _))).add
      (RatPolyCoeffEqv.neg hdet))
  let PV := Certificate.ofCoeff hvariance.symm Pvariance
  let PC := centeredRelativeCoefficient_certificate (N width) (N width) W tilt L Pplus Pminus
  let PG := conditionalGrussSquare_certificate (N width) (N width) W tilt (polyMul X X)
    L hL hW htilt (supported_polyMul hX hX) Pplus Pminus
  have hQ : RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul tilt (polyMul X X))) Q :=
    partialHaarHeads_congr (N width) (RatPolyCoeffEqv.mul_assoc P (J g) (polyMul X X))
  have hscore : RatPolyCoeffEqv
      (polyAdd (polyMul A (partialHaarHeads (N width) (polyMul tilt (polyMul X X)))) (polyNeg
        (polyMul (partialHaarHeads (N width) (polyMul W (polyMul X X))) D0)))
      (polyMul A centered) :=
    ((hQ.mul_left A).add (RatPolyCoeffEqv.neg (hmean.mul_right D0))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3))))
        (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 2) (.var 3)))))
        (by decide) (fun | 0 => A | 1 => Q | 2 => noise | _ => D0))
  have hpaid : RatPolyCoeffEqv
      (polyAdd
        (polyMul coefficient (polyAdd fourth (polyNeg (determinant (N width) W (polyMul X X)))))
        (polyAdd (polyMul coefficient (determinant (N width) W (polyMul X X)))
          (polyNeg (polyMul (polyMul A centered) (polyMul A centered)))))
      (polyAdd (polyMul coefficient fourth)
        (polyNeg (polyMul (polyMul A A) (polyMul centered centered)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4)))))
      (by decide) (fun
        | 0 => coefficient
        | 1 => fourth
        | 2 => determinant (N width) W (polyMul X X)
        | 3 => A
        | _ => centered)
  let Pcentered := Certificate.ofCoeff hpaid.symm
    ((PC.mul PV).add (Certificate.ofCoeff
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (hscore.mul hscore))).symm PG))
  have hD : HaarCarrierEqv (N width) D0 (J A) :=
    (densityMoment_mean_carrier w K width s i j hidx hi hj ha).symm
  have hcoefficient : HaarCarrierEqv (N width) coefficient
      (polyAdd (polyMul (cap (L*L)) (polyMul A A)) (polyNeg (polyMul (J A) (J A)))) :=
    HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hD hD))
  have hcentered : HaarCarrierEqv (N width) centered
      (polyAdd Q (polyNeg (polyMul noise (J A)))) :=
    HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) hD))
  exact Certificate.transport
    (HaarCarrierEqv.add (HaarCarrierEqv.mul hcoefficient (HaarCarrierEqv.refl _ _))
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
        (HaarCarrierEqv.mul hcentered hcentered)))).symm Pcentered

/-- Literal OWN-centered padded-square conditional source. Its cap17,
support, full original signed tilts and both subtracted squares are produced;
incoming precision is arbitrary, independent of the Ward reciprocal degree. -/
def ownPaddedSquareRatio_densityCovariance_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : endpointRelativeCutoff w ≤ K) (n t scale : Nat)
    (hdepth : 1 ≤ n+t) (hwidth : BF4DyadicWilsonSquare.side scale < width)
    (selected : ClusterCount4DProgress.Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) (k : Nat) :=
  let hhead := Nat.le_trans
    (Nat.le_trans (headCutoff_le_relativeCutoff w 4096) (Nat.le_max_left _ _)) hK
  original_ratioNoise_densityCovariance_certificate hw0 hw1 K width hK (n+t)
    selected hl hs hi hj
    (blockConditionalRatio_supported hw0 hw1 K width hhead n t
      (ownPaddedSquareInterval hw0 hw1 K width hhead n scale hwidth).support k)
    (ownPaddedSquareRatio_squareCertificate hw0 hw1 K width hhead n t scale hdepth hwidth k)

/-- Computed precision onset for the favorable reciprocal credit of the
literal ORIGINAL terminal/noise weight. The source phi is held fixed as
the outgoing reciprocal degree grows; no incoming degree is identified
with it. This is fixed-window precision, not a changing-family bound. -/
def originalRatioNoiseCreditCutoff {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (phi : RatPoly)
    (epsilon : Q') : Nat :=
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let F := polyMul (polyMul V V) (matchedNoise w K width a phi)
  favorableCreditCutoff (N width) s i j F A
    (blockWindowLower w K width d 1) (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) epsilon

/-- The produced favorable Ward reciprocal credit vanishes with an explicit
all-later onset on the SAME original finite law. No stationarity, noise
inverse, source-norm floor or relative reserve is assumed. In particular,
its nonnegative sign alone cannot supply a persistent positive reserve as
outgoing precision increases. The absorption square and signed original
density/spatial payments are not estimated by this theorem. -/
theorem original_ratioNoise_reciprocal_credit_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : originalRatioNoiseCreditCutoff hw0 hw1 K width hK d s i j phi epsilon ≤ k) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let F := polyMul (polyMul V V) (matchedNoise w K width a phi)
    let G := reciprocal A (blockWindowUpper w K width d 1)
      (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
    let J := angularDerivative (4*s+i) (4*s+j)
    quaternionHaar (N width) (polyMul (polyMul (polyMul F G) (J A))
      (J (polyMul A G))) ≤ epsilon := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let V := spatialFringeMass w K width
  let noise := matchedNoise w K width a phi
  let F := polyMul (polyMul V V) noise
  have ha := terminalMessage_supported w K width d
  have hA := transferStep_supported w K width ha
  let PN : Certificate (N width) noise :=
    lastStepRatioNoise_certificate hw0 hw1 K width hK d hphi
  let PF : Certificate (N width) F :=
    (Certificate.square V (spatialFringeMass_supported w K width)).mul PN
  have hnext : A = terminalMessage w K width (d+1) :=
    terminalMessage_next w K width d
  let bands := blockWindowCertificates hw0 hw1 K width hK d 1 (by omega)
  have hle : blockWindowLower w K width d 1 ≤ blockWindowUpper w K width d 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (d+1-1)))
  exact finite_reciprocal_favorable_tolerance hs hi hj
    (blockWindowLower_positive hw0 hw1 K width hK d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) hle hA PF
    (show Certificate (N width) (polyAdd A (polyNeg (cap (blockWindowLower w K width d 1)))) by
      rw [hnext]; exact bands.1)
    (show Certificate (N width) (polyAdd (cap (blockWindowUpper w K width d 1)) (polyNeg A)) by
      rw [hnext]; exact bands.2)
    hepsilon k hk

/-- No positive eventual floor can be funded by the finite reciprocal
credit alone at this fixed ORIGINAL terminal/source. This does not refute
retention from the complete signed cost or a coordinated scaling family. -/
theorem original_ratioNoise_reciprocal_credit_no_eventual_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi)
    (delta : Q') (hdelta : (0 : Q') < delta) (onset : Nat) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let V := spatialFringeMass w K width
    let F := polyMul (polyMul V V) (matchedNoise w K width a phi)
    let J := angularDerivative (4*s+i) (4*s+j)
    ¬ (∀ k : Nat, onset ≤ k →
      let G := reciprocal A (blockWindowUpper w K width d 1)
        (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
      delta ≤ quaternionHaar (N width) (polyMul (polyMul (polyMul F G) (J A))
        (J (polyMul A G)))) := by
  dsimp only
  intro hfloor
  let epsilon := delta*HalfPow.half
  have he : (0 : Q') < epsilon := Q'.mul_pos hdelta (by decide)
  let cut := originalRatioNoiseCreditCutoff hw0 hw1 K width hK d s i j phi epsilon
  let k := max onset cut
  have hsmall := original_ratioNoise_reciprocal_credit_tolerance
    hw0 hw1 K width hK d s i j hs hi hj hphi epsilon he k
    (Nat.le_max_right onset cut)
  have hstrict : epsilon < delta := YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (Q'.mul_lt_mul_of_pos_left hdelta (by decide : HalfPow.half < (1 : Q')))
    (Q'.le_of_eqv (Q'.mul_one_eqv delta))
  exact (Int.lt_irrefl (delta.num*(delta.den : Int)))
    (Q'.lt_of_le_of_lt
      (Q'.le_trans' _ _ _ (hfloor k (Nat.le_max_left onset cut)) hsmall) hstrict)

end YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.ratioNoiseDensityMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.noiseDerivativeIncoming_moment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_ward_absorption_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_gradientPayment_unit_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_ward_unitGradient_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_gradientPayment_weighted_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.originalRatioNoiseCreditCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_reciprocal_credit_tolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_reciprocal_credit_no_eventual_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_ward_noiseGradient_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_noiseGradientPayment_unit_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_ward_unitNoiseGradient_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_noiseGradientPayment_weighted_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_densityCovariance_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.ownPaddedSquareRatio_densityCovariance_certificate
