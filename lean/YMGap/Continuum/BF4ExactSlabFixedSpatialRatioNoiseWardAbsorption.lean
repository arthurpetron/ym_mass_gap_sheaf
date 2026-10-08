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
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
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
  have hG := reciprocal_supported hA (blockWindowUpper w K width d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) (k+1)
  let PN : Certificate (N width) noise := lastStepRatioNoise_certificate hw0 hw1 K width hK d hphi
  let PF := (Certificate.square V hV).mul PN
  let PR := (Certificate.square V hV).mul (Certificate.square G hG)
  have hnext : A = terminalMessage w K width (d+1) := terminalMessage_next w K width d
  have PU : Certificate (N width) (polyAdd (cap (blockWindowUpper w K width d 1)) (polyNeg A)) := by
    rw [hnext]
    exact (blockWindowCertificates hw0 hw1 K width hK d 1 (by omega)).2
  have hward := finite_reciprocal_hessian_ibp_le hs hi hj
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) hA PF PU k
  have habs := original_ratioNoise_phiGradient_absorption_le hw0 hw1 K width hK d s i j
    hs hi hj hphi PR
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
  exact Q'.le_trans' _ _ _ hward
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcorrNeg)
      (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ habs)))

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
