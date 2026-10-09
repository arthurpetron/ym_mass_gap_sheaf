/-
The literal selected-link paired gradient of a spatial plaquette scalar.
The one-link six-plane identity is reused at arbitrary Haar insertion strength;
the character-one factor 2 is removed by an exact quarter rescaling.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular
import YMGap.Continuum.QuaternionHaarPairedHessianTrace

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteGradient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAdjacentFullAngular (incident_square)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_smul)
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (blockGamma)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_smul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarPairedHessianTrace (paired_gradient_square_pin)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

private theorem six_congr {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, RatPolyCoeffEqv (f i j) (g i j)) :
    RatPolyCoeffEqv (six f) (six g) := by
  unfold six
  exact (h 0 1).add ((h 0 2).add ((h 0 3).add
    ((h 1 2).add ((h 1 3).add (h 2 3)))))

private theorem neg_scale (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c p)) (polySmul c (polyNeg p)) :=
  (neg_smul (polySmul c p)).trans
    ((RatPolyCoeffEqv.smul_assoc (-1) c p).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) c) p).trans
        ((RatPolyCoeffEqv.smul_assoc c (-1) p).symm.trans
          ((neg_smul p).symm.smul c))))

private theorem blockGamma_twice (s : Nat) (x : RatPoly) :
    RatPolyCoeffEqv (blockGamma s (polySmul 2 x) (polySmul 2 x))
      (polySmul 4 (blockGamma s x x)) := by
  have hcell (i j : Nat) : RatPolyCoeffEqv
      (polyMul (blockAngularDerivative s i j (polySmul 2 x))
        (blockAngularDerivative s i j (polySmul 2 x)))
      (polySmul 4 (polyMul (blockAngularDerivative s i j x)
        (blockAngularDerivative s i j x))) := by
    let D := blockAngularDerivative s i j x
    have hd : RatPolyCoeffEqv (blockAngularDerivative s i j (polySmul 2 x))
        (polySmul 2 D) := angularDerivative_smul (4*s+i) (4*s+j) 2 x
    exact (hd.mul hd).trans
      ((RatPolyCoeffEqv.polyMul_smul_left 2 D (polySmul 2 D)).trans
        (((RatPolyCoeffEqv.polyMul_smul_right 2 D D).smul 2).trans
          (twice_twice_smul (polyMul D D))))
  exact (six_congr hcell).trans (six_smul 4 _)

private theorem quarter_four (p : RatPoly) :
    RatPolyCoeffEqv (polySmul quarter (polySmul 4 p)) p :=
  (RatPolyCoeffEqv.smul_assoc quarter 4 p).trans
    ((RatPolyCoeffEqv.smul_coefficient
      (by decide : Q'.eqv (quarter * 4) 1) p).trans (RatPolyCoeffEqv.one_smul p))

/-- At an actual incident original link, the three paired first jets of the
literal scalar X have squared length 1-X², with every Haar insertion retained. -/
theorem plaquette_paired_gradient_square (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face) :
    let X := (plaquette width face).scalar
    HaarCarrierEqv (N width)
      (threeSquare (fun i => pairedDerivativeAt ((baseLinks width).idxOf l) i X))
      (polyAdd polyOne (polyNeg (polyMul X X))) := by
  dsimp only
  let X := (plaquette width face).scalar
  let s := (baseLinks width).idxOf l
  let G := threeSquare (fun i => pairedDerivativeAt s i X)
  let gapX := polyAdd polyOne (polyNeg (polyMul X X))
  have hp : RatPolyCoeffEqv G (blockGamma s X X) := by
    exact paired_gradient_square_pin s X
  have hi : HaarCarrierEqv (N width)
      (blockGamma s (polySmul 2 X) (polySmul 2 X))
      (polyAdd (cap 4)
        (polyNeg (polyMul (polySmul 2 X) (polySmul 2 X)))) := by
    have h := incident_square width face hf l hl
    change HaarCarrierEqv (N width)
      (blockGamma s (polySmul 2 X) (polySmul 2 X))
      (polyAdd (cap 4)
        (polyNeg (polyMul (polySmul 2 X) (polySmul 2 X)))) at h
    exact h
  have htwice : RatPolyCoeffEqv
      (polyMul (polySmul 2 X) (polySmul 2 X)) (polySmul 4 (polyMul X X)) :=
    (RatPolyCoeffEqv.polyMul_smul_left 2 X (polySmul 2 X)).trans
      (((RatPolyCoeffEqv.polyMul_smul_right 2 X X).smul 2).trans
        (twice_twice_smul (polyMul X X)))
  have hgap : RatPolyCoeffEqv
      (polyAdd (cap 4) (polyNeg (polyMul (polySmul 2 X) (polySmul 2 X))))
      (polySmul 4 gapX) :=
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg htwice)).trans
      (((RatPolyCoeffEqv.refl _).add (neg_scale 4 (polyMul X X))).trans
        (RatPolyCoeffEqv.smul_add 4 polyOne (polyNeg (polyMul X X))).symm)
  have hfour : HaarCarrierEqv (N width) (polySmul 4 G) (polySmul 4 gapX) :=
    (RatPolyCoeffEqv.haarCarrier ((hp.smul 4).trans (blockGamma_twice s X).symm)).trans
      (hi.trans (RatPolyCoeffEqv.haarCarrier hgap))
  exact (RatPolyCoeffEqv.haarCarrier (quarter_four G).symm).trans
    ((HaarCarrierEqv.smul quarter hfour).trans
      (RatPolyCoeffEqv.haarCarrier (quarter_four gapX)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteGradient

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteGradient.plaquette_paired_gradient_square
