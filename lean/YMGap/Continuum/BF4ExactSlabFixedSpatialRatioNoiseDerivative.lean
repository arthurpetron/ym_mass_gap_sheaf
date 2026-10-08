/-
# Cleared differentiation of the actual matched one-step noise

The derivative is transported to the COMPLETE incoming spatial source V*a.
All output moments are retained on the same carrier. Twice the mixed term
is written as its sum with itself. No source quotient, positivity, exact
inverse, stationary terminal law or estimate is asserted.

Consumer: the literal noise derivative in the finite reciprocal Ward term.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (angularDerivative_neg)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise (lastStepRatioNoise)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

def matchedNoise (w : Q') (K width : Nat) (a phi : RatPoly) : RatPoly :=
  let A := transferStep w K width a
  let b := transferStep w K width (polyMul a phi)
  let U := transferStep w K width (polyMul a (polyMul phi phi))
  polyAdd (polyMul A U) (polyNeg (polyMul b b))

theorem matchedNoise_eq_blockNoise (w : Q') (K width : Nat) (a phi : RatPoly) :
    matchedNoise w K width a phi = blockNoise w K width 1 a phi := rfl

theorem matchedNoise_eq_lastStepRatioNoise (w : Q') (K width d : Nat) (phi : RatPoly) :
    matchedNoise w K width (terminalMessage w K width d) phi =
      lastStepRatioNoise w K width d phi := rfl

def matchedNoiseResidual (w : Q') (K width : Nat) (a phi : RatPoly) : RatPoly :=
  polyAdd (polyMul (liftBoundary (N width) (transferStep w K width a)) phi)
    (polyNeg (liftBoundary (N width) (transferStep w K width (polyMul a phi))))

def noiseDerivativeIncoming (w : Q') (K width s i j : Nat) (a phi : RatPoly) : RatPoly :=
  let g := polyMul (spatialWeight w K width) a
  let A := transferStep w K width a
  let X := matchedNoiseResidual w K width a phi
  let J := angularDerivative (4*s+i) (4*s+j)
  let mixed := polyMul (polyMul (polyMul g (liftBoundary (N width) A)) X) (J phi)
  polyAdd (polyMul (J g) (polyMul X X)) (polyAdd mixed mixed)

private theorem incoming_expansion (heads i j : Nat) (P g phi A b : RatPoly) :
    let J := angularDerivative i j
    let LA := liftBoundary heads A
    let LB := liftBoundary heads b
    let X := polyAdd (polyMul LA phi) (polyNeg LB)
    let mixed := polyMul (polyMul (polyMul g LA) X) (J phi)
    RatPolyCoeffEqv
      (polyMul P (polyAdd (polyMul (J g) (polyMul X X)) (polyAdd mixed mixed)))
      (polyAdd
        (polyAdd
          (polyMul (polyMul P (J (polyMul g (polyMul phi phi))))
            (liftBoundary heads (polyMul A A)))
          (polyNeg (polyAdd
            (polyMul (polyMul P (J (polyMul g phi))) (liftBoundary heads (polyMul A b)))
            (polyMul (polyMul P (J (polyMul g phi))) (liftBoundary heads (polyMul A b))))))
        (polyMul (polyMul P (J g)) (liftBoundary heads (polyMul b b)))) := by
  dsimp only
  simp only [lift_product]
  have hd1 := angularDerivative_mul i j g phi
  have hd2 := (angularDerivative_mul i j g (polyMul phi phi)).trans
    ((RatPolyCoeffEqv.refl _).add ((angularDerivative_mul i j phi phi).mul_left g))
  have hright :=
    (((hd2.mul_left P).mul_right
      (polyMul (liftBoundary heads A) (liftBoundary heads A))).add
      (RatPolyCoeffEqv.neg
        (((hd1.mul_left P).mul_right
          (polyMul (liftBoundary heads A) (liftBoundary heads b))).add
          ((hd1.mul_left P).mul_right
            (polyMul (liftBoundary heads A) (liftBoundary heads b)))))).add
      (RatPolyCoeffEqv.refl (polyMul (polyMul P (angularDerivative i j g))
        (polyMul (liftBoundary heads b) (liftBoundary heads b))))
  refine (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add
      (.mul (.var 5) (.mul (.add (.mul (.var 3) (.var 2)) (.neg (.var 4)))
        (.add (.mul (.var 3) (.var 2)) (.neg (.var 4)))))
      (.add
        (.mul (.mul (.mul (.var 1) (.var 3))
          (.add (.mul (.var 3) (.var 2)) (.neg (.var 4)))) (.var 6))
        (.mul (.mul (.mul (.var 1) (.var 3))
          (.add (.mul (.var 3) (.var 2)) (.neg (.var 4)))) (.var 6)))))
    (.add (.add
      (.mul (.mul (.var 0) (.add (.mul (.var 5) (.mul (.var 2) (.var 2)))
        (.mul (.var 1) (.add (.mul (.var 6) (.var 2)) (.mul (.var 2) (.var 6))))))
        (.mul (.var 3) (.var 3)))
      (.neg (.add
        (.mul (.mul (.var 0) (.add (.mul (.var 5) (.var 2)) (.mul (.var 1) (.var 6))))
          (.mul (.var 3) (.var 4)))
        (.mul (.mul (.var 0) (.add (.mul (.var 5) (.var 2)) (.mul (.var 1) (.var 6))))
          (.mul (.var 3) (.var 4))))))
      (.mul (.mul (.var 0) (.var 5)) (.mul (.var 4) (.var 4))))
    (by decide) (fun
      | 0 => P
      | 1 => g
      | 2 => phi
      | 3 => liftBoundary heads A
      | 4 => liftBoundary heads b
      | 5 => angularDerivative i j g
      | _ => angularDerivative i j phi)).trans hright.symm

private theorem pull_three (heads : Nat) (h0 h1 h2 A b : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyAdd
        (polyAdd (polyMul h2 (liftBoundary heads (polyMul A A)))
          (polyNeg (polyAdd (polyMul h1 (liftBoundary heads (polyMul A b)))
            (polyMul h1 (liftBoundary heads (polyMul A b))))))
        (polyMul h0 (liftBoundary heads (polyMul b b)))))
      (polyAdd
        (polyAdd (polyMul (polyMul A A) (partialHaarHeads heads h2))
          (polyNeg (polyAdd (polyMul (polyMul A b) (partialHaarHeads heads h1))
            (polyMul (polyMul A b) (partialHaarHeads heads h1)))))
        (polyMul (polyMul b b) (partialHaarHeads heads h0))) := by
  rw [partialHaarHeads_add, partialHaarHeads_add]
  have pull (h z : RatPoly) :=
    (partialHaarHeads_mul_lift heads h z).trans (RatPolyCoeffEqv.mul_comm _ z)
  exact ((pull h2 (polyMul A A)).add
    ((partialHaarHeads_neg heads _).trans
      (RatPolyCoeffEqv.neg (by
        rw [partialHaarHeads_add]
        exact (pull h1 (polyMul A b)).add (pull h1 (polyMul A b)))))).add
    (pull h0 (polyMul b b))

private theorem derivative_transfer (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    HaarCarrierEqv (N width)
      (angularDerivative (4*s+i) (4*s+j) (transferStep w K width p))
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
        (angularDerivative (4*s+i) (4*s+j) (polyMul (spatialWeight w K width) p)))) := by
  rw [transferStep_eq_productMap, kineticWeight_eq_indexedProduct]
  exact productMap_angular_carrier (N width) s i j hs hi hj w K
    (activeBlocks width) (activeBlocks_lt width) _
    (supported_polyMul (spatialWeight_supported w K width) hp)

/-- The cleared derivative of matched noise is two literal signed incoming
moments. This equality retains every surviving Haar insertion. -/
theorem ratioNoise_derivative_carrier (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a phi : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hphi : SupportedQuaternionBlocks (N width) phi) :
    let A := transferStep w K width a
    let J := angularDerivative (4*s+i) (4*s+j)
    let noise := matchedNoise w K width a phi
    HaarCarrierEqv (N width)
      (polyAdd (polyMul A (J noise)) (polyNeg (polyMul noise (J A))))
      (partialHaarHeads (N width) (polyMul (kineticWeight w K width)
        (noiseDerivativeIncoming w K width s i j a phi))) := by
  dsimp only
  let A := transferStep w K width a
  let b := transferStep w K width (polyMul a phi)
  let U := transferStep w K width (polyMul a (polyMul phi phi))
  let J := angularDerivative (4*s+i) (4*s+j)
  let P := kineticWeight w K width
  let g := polyMul (spatialWeight w K width) a
  let h0 := partialHaarHeads (N width) (polyMul P (J g))
  let h1 := partialHaarHeads (N width) (polyMul P (J (polyMul g phi)))
  let h2 := partialHaarHeads (N width) (polyMul P (J (polyMul g (polyMul phi phi))))
  have hA : HaarCarrierEqv (N width) (J A) h0 :=
    derivative_transfer w K width s i j hs hi hj ha
  have hb0 := derivative_transfer w K width s i j hs hi hj (supported_polyMul ha hphi)
  have hU0 := derivative_transfer w K width s i j hs hi hj
    (supported_polyMul ha (supported_polyMul hphi hphi))
  have hb : HaarCarrierEqv (N width) (J b) h1 := hb0.trans
    (RatPolyCoeffEqv.haarCarrier (partialHaarHeads_congr (N width)
      ((angularDerivative_congr (4*s+i) (4*s+j)
        (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) a phi).symm).mul_left P)))
  have hU : HaarCarrierEqv (N width) (J U) h2 := hU0.trans
    (RatPolyCoeffEqv.haarCarrier (partialHaarHeads_congr (N width)
      ((angularDerivative_congr (4*s+i) (4*s+j)
        (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) a (polyMul phi phi)).symm).mul_left P)))
  have hn := (angularDerivative_add (4*s+i) (4*s+j) (polyMul A U) (polyNeg (polyMul b b))).trans
    ((angularDerivative_mul (4*s+i) (4*s+j) A U).add
      ((angularDerivative_neg (4*s+i) (4*s+j) (polyMul b b)).trans
        (RatPolyCoeffEqv.neg (angularDerivative_mul (4*s+i) (4*s+j) b b))))
  have hcalc := ((hn.mul_left A).add
    (RatPolyCoeffEqv.refl (polyNeg (polyMul
      (polyAdd (polyMul A U) (polyNeg (polyMul b b))) (J A))))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add
        (.add (.mul (.var 3) (.var 2)) (.mul (.var 0) (.var 5)))
        (.neg (.add (.mul (.var 4) (.var 1)) (.mul (.var 1) (.var 4))))))
        (.neg (.mul (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))) (.var 3))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 5))
        (.neg (.add (.mul (.mul (.var 0) (.var 1)) (.var 4))
          (.mul (.mul (.var 0) (.var 1)) (.var 4)))))
        (.mul (.mul (.var 1) (.var 1)) (.var 3)))
      (by decide) (fun
        | 0 => A
        | 1 => b
        | 2 => U
        | 3 => J A
        | 4 => J b
        | _ => J U))
  have hsub := HaarCarrierEqv.add
    (HaarCarrierEqv.add (HaarCarrierEqv.mul_left (polyMul A A) hU)
      (HaarCarrierEqv.neg (HaarCarrierEqv.add
        (HaarCarrierEqv.mul_left (polyMul A b) hb)
        (HaarCarrierEqv.mul_left (polyMul A b) hb))))
    (HaarCarrierEqv.mul_left (polyMul b b) hA)
  have hint := (partialHaarHeads_congr (N width)
    (incoming_expansion (N width) (4*s+i) (4*s+j) P g phi A b)).trans
    (pull_three (N width) (polyMul P (J g)) (polyMul P (J (polyMul g phi)))
      (polyMul P (J (polyMul g (polyMul phi phi)))) A b)
  exact (RatPolyCoeffEqv.haarCarrier hcalc).trans
    (hsub.trans (RatPolyCoeffEqv.haarCarrier hint.symm))

/-- Literal cleared input to the weighted Ward term. V is arbitrary; its
derivative is retained, and no inverse or sign is used to clear A. -/
theorem weightedNoise_derivative_carrier (w : Q') (K width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) {a phi : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hphi : SupportedQuaternionBlocks (N width) phi) (V : RatPoly) :
    let A := transferStep w K width a
    let J := angularDerivative (4*s+i) (4*s+j)
    let noise := matchedNoise w K width a phi
    let F := polyMul (polyMul V V) noise
    let cross := polyMul (polyMul (polyMul A V) (J V)) noise
    let Q := partialHaarHeads (N width) (polyMul (kineticWeight w K width)
      (noiseDerivativeIncoming w K width s i j a phi))
    HaarCarrierEqv (N width) (polyMul A (J F))
      (polyAdd (polyAdd (polyMul F (J A)) (polyAdd cross cross))
        (polyMul (polyMul V V) Q)) := by
  dsimp only
  let A := transferStep w K width a
  let J := angularDerivative (4*s+i) (4*s+j)
  let noise := matchedNoise w K width a phi
  have hDF := (angularDerivative_mul (4*s+i) (4*s+j) (polyMul V V) noise).trans
    (((angularDerivative_mul (4*s+i) (4*s+j) V V).mul_right noise).add
      (RatPolyCoeffEqv.refl (polyMul (polyMul V V) (J noise))))
  have hsplit := (hDF.mul_left A).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add
        (.mul (.add (.mul (.var 4) (.var 1)) (.mul (.var 1) (.var 4))) (.var 2))
        (.mul (.mul (.var 1) (.var 1)) (.var 5))))
      (.add (.add
        (.mul (.mul (.mul (.var 1) (.var 1)) (.var 2)) (.var 3))
        (.add
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 4)) (.var 2))
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 4)) (.var 2))))
        (.mul (.mul (.var 1) (.var 1))
          (.add (.mul (.var 0) (.var 5)) (.neg (.mul (.var 2) (.var 3))))))
      (by decide) (fun
        | 0 => A
        | 1 => V
        | 2 => noise
        | 3 => J A
        | 4 => J V
        | _ => J noise))
  exact (RatPolyCoeffEqv.haarCarrier hsplit).trans
    (HaarCarrierEqv.add (HaarCarrierEqv.refl (N width) _)
      (HaarCarrierEqv.mul_left (polyMul V V)
        (ratioNoise_derivative_carrier w K width s i j hs hi hj ha hphi)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative.matchedNoise
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative.matchedNoise_eq_blockNoise
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative.matchedNoise_eq_lastStepRatioNoise
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative.matchedNoiseResidual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative.noiseDerivativeIncoming
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative.ratioNoise_derivative_carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRatioNoiseDerivative.weightedNoise_derivative_carrier
