/-
# Coefficient-one absorption of the ORIGINAL ratio-noise source gradient

A single actual conditional square pays the phi-gradient cross term by
A^3*T(a*(J phi)^2). The terminal window cancels its positive A multiplier
only in Haar order, with every certified output insertion retained.
No noise inverse, source quotient, density replacement or N positivity
premise is used. Spatial-action derivatives and the full signed/scaling
budget remain unestimated.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
import YMGap.Continuum.SU2QuaternionAngularSupport

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
  (partialHaarHeads partialHaarHeads_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticFloor_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative (partialHaarHeads_add)
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact hp source hs

/-- Literal mixed incoming moment M=I[K*(Va)*X*Jphi]. -/
def ratioNoiseGradientMoment (w : Q') (K width s i j : Nat) (a phi : RatPoly) : RatPoly :=
  partialHaarHeads (N width) (polyMul (kineticWeight w K width)
    (polyMul (polyMul (polyMul (spatialWeight w K width) a)
      (matchedNoiseResidual w K width a phi)) (angularDerivative (4*s+i) (4*s+j) phi)))

/-- Literal incoming derivative energy E=I[K*(Va)*(Jphi)^2]. -/
def ratioNoiseGradientEnergy (w : Q') (K width s i j : Nat) (a phi : RatPoly) : RatPoly :=
  transferStep w K width (polyMul a
    (polyMul (angularDerivative (4*s+i) (4*s+j) phi)
      (angularDerivative (4*s+i) (4*s+j) phi)))

private theorem integrate_three (heads : Nat) (p q r u v z : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyAdd (polyAdd
        (polyMul p (liftBoundary heads u)) (polyMul q (liftBoundary heads v)))
        (polyMul r (liftBoundary heads z))))
      (polyAdd (polyAdd (polyMul (partialHaarHeads heads p) u)
        (polyMul (partialHaarHeads heads q) v)) (polyMul (partialHaarHeads heads r) z)) := by
  rw [partialHaarHeads_add, partialHaarHeads_add]
  exact ((partialHaarHeads_mul_lift heads p u).add
    (partialHaarHeads_mul_lift heads q v)).add (partialHaarHeads_mul_lift heads r z)

private theorem haar_neg (n : Nat) (r p : RatPoly) :
    quaternionHaar n (polyMul r (polyNeg p)) ≈ -quaternionHaar n (polyMul r p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((neg_smul p).mul_left r))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (-1) r p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

private theorem residual_square_pin (heads : Nat) (W phi A b U : RatPoly)
    (hA : RatPolyCoeffEqv (partialHaarHeads heads W) A)
    (hb : RatPolyCoeffEqv (partialHaarHeads heads (polyMul W phi)) b)
    (hU : RatPolyCoeffEqv (partialHaarHeads heads (polyMul W (polyMul phi phi))) U) :
    let X := polyAdd (polyMul (liftBoundary heads A) phi) (polyNeg (liftBoundary heads b))
    RatPolyCoeffEqv (partialHaarHeads heads (polyMul W (polyMul X X)))
      (polyMul A (polyAdd (polyMul A U) (polyNeg (polyMul b b)))) := by
  dsimp only
  have hex : RatPolyCoeffEqv
      (polyMul W (polyMul
        (polyAdd (polyMul (liftBoundary heads A) phi) (polyNeg (liftBoundary heads b)))
        (polyAdd (polyMul (liftBoundary heads A) phi) (polyNeg (liftBoundary heads b)))))
      (polyAdd (polyAdd
        (polyMul (polyMul W (polyMul phi phi)) (liftBoundary heads (polyMul A A)))
        (polyMul (polyMul W phi) (liftBoundary heads (polyNeg
          (polyAdd (polyMul A b) (polyMul A b))))))
        (polyMul W (liftBoundary heads (polyMul b b)))) := by
    simp only [lift_product, lift_neg, lift_add]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.mul (.var 2) (.var 1)) (.neg (.var 3)))
        (.add (.mul (.var 2) (.var 1)) (.neg (.var 3)))))
      (.add (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
        (.mul (.mul (.var 0) (.var 1)) (.neg (.add (.mul (.var 2) (.var 3))
          (.mul (.var 2) (.var 3)))))) (.mul (.var 0) (.mul (.var 3) (.var 3))))
      (by decide) (fun
        | 0 => W
        | 1 => phi
        | 2 => liftBoundary heads A
        | _ => liftBoundary heads b)
  have hmeans := ((hU.mul_right (polyMul A A)).add
    (hb.mul_right (polyNeg (polyAdd (polyMul A b) (polyMul A b))))).add
    (hA.mul_right (polyMul b b))
  exact (partialHaarHeads_congr heads hex).trans
    ((integrate_three heads _ _ _ _ _ _).trans
      (hmeans.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.var 2) (.mul (.var 0) (.var 0)))
          (.mul (.var 1) (.neg (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))))
          (.mul (.var 0) (.mul (.var 1) (.var 1))))
        (.mul (.var 0) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
        (by decide) (fun
          | 0 => A
          | 1 => b
          | _ => U))))

private theorem absorption_square_pin (heads : Nat) (W X t A D N0 : RatPoly)
    (hX : RatPolyCoeffEqv (partialHaarHeads heads (polyMul W (polyMul X X))) (polyMul A N0)) :
    let M := partialHaarHeads heads (polyMul W (polyMul X t))
    let E := partialHaarHeads heads (polyMul W (polyMul t t))
    let Y := polyAdd (polyMul (liftBoundary heads D) X)
      (polyMul (liftBoundary heads (polyMul A A)) t)
    RatPolyCoeffEqv (partialHaarHeads heads (polyMul W (polyMul Y Y)))
      (polyMul A (polyAdd (polyAdd (polyMul N0 (polyMul D D))
        (polyMul (polyAdd (polyMul A D) (polyMul A D)) M))
        (polyMul (polyMul (polyMul A A) A) E))) := by
  dsimp only
  have hex : RatPolyCoeffEqv (polyMul W (polyMul
      (polyAdd (polyMul (liftBoundary heads D) X) (polyMul (liftBoundary heads (polyMul A A)) t))
      (polyAdd (polyMul (liftBoundary heads D) X) (polyMul (liftBoundary heads (polyMul A A)) t))))
      (polyAdd (polyAdd
        (polyMul (polyMul W (polyMul X X)) (liftBoundary heads (polyMul D D)))
        (polyMul (polyMul W (polyMul X t)) (liftBoundary heads
          (polyAdd (polyMul D (polyMul A A)) (polyMul D (polyMul A A))))))
        (polyMul (polyMul W (polyMul t t)) (liftBoundary heads (polyMul (polyMul A A) (polyMul A A))))) := by
    simp only [lift_product, lift_add]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.mul (.var 3) (.var 1)) (.mul (.mul (.var 4) (.var 4)) (.var 2)))
        (.add (.mul (.var 3) (.var 1)) (.mul (.mul (.var 4) (.var 4)) (.var 2)))))
      (.add (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 3) (.var 3)))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.add (.mul (.var 3) (.mul (.var 4) (.var 4))) (.mul (.var 3) (.mul (.var 4) (.var 4))))))
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2)))
          (.mul (.mul (.var 4) (.var 4)) (.mul (.var 4) (.var 4)))))
      (by decide) (fun
        | 0 => W
        | 1 => X
        | 2 => t
        | 3 => liftBoundary heads D
        | _ => liftBoundary heads A)
  exact (partialHaarHeads_congr heads hex).trans
    ((integrate_three heads _ _ _ _ _ _).trans
      ((((hX.mul_right _).add (.refl _)).add (.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
            (.mul (.var 3) (.add (.mul (.var 1) (.mul (.var 0) (.var 0)))
              (.mul (.var 1) (.mul (.var 0) (.var 0))))))
            (.mul (.var 4) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))))
          (.mul (.var 0) (.add (.add (.mul (.var 2) (.mul (.var 1) (.var 1)))
            (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 3)))
            (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 4))))
          (by decide) (fun
            | 0 => A
            | 1 => D
            | 2 => N0
            | 3 => partialHaarHeads heads (polyMul W (polyMul X t))
            | _ => partialHaarHeads heads (polyMul W (polyMul t t))))))

/-- Actual terminal source; the favorable noise square absorbs ONLY the
phi-gradient cross with coefficient one, at every certified output insertion. -/
theorem original_ratioNoise_phiGradient_absorption_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (d s i j : Nat) (hs : s < N width)
    (hi : i < 4) (hj : j < 4) {phi R : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) (PR : Certificate (N width) R) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let D := angularDerivative (4*s+i) (4*s+j) A
    let N0 := matchedNoise w K width a phi
    let M := ratioNoiseGradientMoment w K width s i j a phi
    let E := ratioNoiseGradientEnergy w K width s i j a phi
    quaternionHaar (N width) (polyMul R (polyNeg (polyAdd
      (polyMul N0 (polyMul D D)) (polyMul (polyAdd (polyMul A D) (polyMul A D)) M)))) ≤
      quaternionHaar (N width) (polyMul R (polyMul (polyMul (polyMul A A) A) E)) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let b := transferStep w K width (polyMul a phi)
  let U := transferStep w K width (polyMul a (polyMul phi phi))
  let D := angularDerivative (4*s+i) (4*s+j) A
  let t := angularDerivative (4*s+i) (4*s+j) phi
  let W := polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) a)
  let X := matchedNoiseResidual w K width a phi
  let M := partialHaarHeads (N width) (polyMul W (polyMul X t))
  let E := partialHaarHeads (N width) (polyMul W (polyMul t t))
  let L0 := polyAdd (polyMul (matchedNoise w K width a phi) (polyMul D D))
    (polyMul (polyAdd (polyMul A D) (polyMul A D)) M)
  let B0 := polyMul (polyMul (polyMul A A) A) E
  have ha := terminalMessage_supported w K width d
  have hA := transferStep_supported w K width ha
  have hb := transferStep_supported w K width (supported_polyMul ha hphi)
  have hU := transferStep_supported w K width (supported_polyMul ha (supported_polyMul hphi hphi))
  have ht := angularDerivative_supported_at (by omega : 4*s+i < 4*N width)
    (by omega : 4*s+j < 4*N width) hphi
  have hD := angularDerivative_supported_at (by omega : 4*s+i < 4*N width)
    (by omega : 4*s+j < 4*N width) hA
  have extend {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
      SupportedQuaternionBlocks (N width+N width) p := fun v hv =>
    Nat.le_trans (hp v hv) (by omega)
  have hW := supported_polyMul (kineticWeight_supported w K width)
    (supported_polyMul (extend (spatialWeight_supported w K width)) (extend ha))
  have hX := supported_add (supported_polyMul (lift_supported hA (N width)) (extend hphi))
    (supported_neg (lift_supported hb (N width)))
  have hM := partialHaarHeads_supported (N width) (N width) _
    (supported_polyMul hW (supported_polyMul hX (extend ht)))
  have hE := partialHaarHeads_supported (N width) (N width) _
    (supported_polyMul hW (supported_polyMul (extend ht) (extend ht)))
  have mean_pin (f : RatPoly) : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul W f)) (transferStep w K width (polyMul a f)) :=
    partialHaarHeads_congr (N width)
      ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
        ((RatPolyCoeffEqv.mul_assoc _ _ _).mul_left (kineticWeight w K width)))
  have hres := residual_square_pin (N width) W phi A b U (.refl _) (mean_pin phi)
    (mean_pin (polyMul phi phi))
  have hpin := absorption_square_pin (N width) W X t A D (matchedNoise w K width a phi) hres
  let Y := polyAdd (polyMul (liftBoundary (N width) D) X)
    (polyMul (liftBoundary (N width) (polyMul A A)) t)
  have hY := supported_add (supported_polyMul (lift_supported hD (N width)) hX)
    (supported_polyMul (lift_supported (supported_polyMul hA hA) (N width)) (extend ht))
  let PW : Certificate (N width+N width) W := Certificate.ofCoeff
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm ((stepWeightCertificate hw0 hw1 K width hK).mul
      (certificate_extend (N width) ha (terminalMessage_certificate hw0 hw1 K width hK d)))
  let PS := partialHaarHeads_certificate (N width) (N width) (PW.mul (Certificate.square Y hY))
  let PAQ : Certificate (N width) (polyMul A (polyAdd L0 B0)) := Certificate.ofCoeff hpin.symm PS
  have hN := supported_add (supported_polyMul hA hU) (supported_neg (supported_polyMul hb hb))
  have hQ := supported_add (supported_add (supported_polyMul hN (supported_polyMul hD hD))
    (supported_polyMul (supported_add (supported_polyMul hA hD) (supported_polyMul hA hD)) hM))
    (supported_polyMul (supported_polyMul (supported_polyMul hA hA) hA) hE)
  have hnext : A = terminalMessage w K width (d+1) := terminalMessage_next w K width d
  let bands := blockWindowCertificates hw0 hw1 K width hK d 1 (by omega)
  have hle : blockWindowLower w K width d 1 ≤ blockWindowUpper w K width d 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (d+1-1)))
  have hn := haar_nonnegative_of_positive_multiplier hA hQ
    (blockWindowLower_positive hw0 hw1 K width hK d 1)
    (blockWindowUpper_positive hw0 hw1 K width hK d 1) hle
    (show Certificate (N width) (polyAdd A (polyNeg (cap (blockWindowLower w K width d 1)))) by
      rw [hnext]; exact bands.1)
    (show Certificate (N width) (polyAdd (cap (blockWindowUpper w K width d 1)) (polyNeg A)) by
      rw [hnext]; exact bands.2) PR PAQ
  have hout : (0 : Q') ≤ quaternionHaar (N width) (polyMul R L0)+
      quaternionHaar (N width) (polyMul R B0) :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)) (quaternionHaar_append (N width) _ _)))
  have hneg := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hout
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.var 1)) (.add (.var 1) (.neg (.neg (.var 0))))
      (by decide) (fun
        | 0 => quaternionHaar (N width) (polyMul R L0)
        | _ => quaternionHaar (N width) (polyMul R B0)))))
  have hm : RatPolyCoeffEqv (ratioNoiseGradientMoment w K width s i j a phi) M :=
    partialHaarHeads_congr (N width)
      (((RatPolyCoeffEqv.mul_assoc (polyMul (spatialWeight w K width) a) X t).mul_left
        (kineticWeight w K width)).trans
        (RatPolyCoeffEqv.mul_assoc (kineticWeight w K width)
          (polyMul (spatialWeight w K width) a) (polyMul X t)).symm)
  have he : RatPolyCoeffEqv (ratioNoiseGradientEnergy w K width s i j a phi) E :=
    (mean_pin (polyMul t t)).symm
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.neg
        ((RatPolyCoeffEqv.refl _).add (hm.mul_left _))).mul_left R))
      (haar_neg (N width) R L0)))
    (Q'.le_trans' _ _ _ hneg (Q'.ge_of_eqv (haar_of_coeff ((he.mul_left _).mul_left R))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.ratioNoiseGradientMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.ratioNoiseGradientEnergy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.original_ratioNoise_phiGradient_absorption_le
