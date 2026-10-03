/-
# Actual angular Bochner curvature certificate

Gamma2 is DEFINED by the original six-field Laplacian and mixed angular
energy, not by a replacement Hessian. Actual Casimir centrality identifies
it with the full ordered second-derivative square. The curvature margin
Gamma2-Gamma has an explicit symmetric-Hessian square certificate on the
same supported Haar carrier, retaining arbitrary shared spectators.

This is a local SU(2) curvature statement. Conditional heat-flow variance,
the complete signed-window budget on a justified scaling family, nonzero
continuum survival, and the Clay target remain open.
-/

import YMGap.Continuum.SU2QuaternionAngularCasimirCentrality
import YMGap.Continuum.SU2QuaternionAngularHessianSquares

namespace YMGap.Continuum.SU2QuaternionAngularBochner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy (angularLaplacian_square)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionAngularCasimirCentrality
open YMGap.Continuum.SU2QuaternionAngularHessianSquares

attribute [local irreducible] angularDerivative

/-- Polarized energy of the SAME six original rotations. -/
def mixedGamma (p q : RatPoly) : RatPoly :=
  six fun i j => polyMul (angularDerivative i j p) (angularDerivative i j q)

/-- Actual iterated carré du champ for the ORIGINAL Laplacian. -/
def gamma2 (p : RatPoly) : RatPoly :=
  polyAdd (polySmul HalfPow.half (angularLaplacian (angularSquare p)))
    (polyNeg (mixedGamma p (angularLaplacian p)))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem hessian_transpose_coeff (p : RatPoly) :
    RatPolyCoeffEqv
      (six fun i j => angularSquare (angularDerivative i j p))
      (hessianSquare p) := by
  unfold six angularSquare hessianSquare
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 0) (.var 0)) (.add (.mul (.var 6) (.var 6)) (.add (.mul (.var 12) (.var 12)) (.add (.mul (.var 18) (.var 18)) (.add (.mul (.var 24) (.var 24)) (.mul (.var 30) (.var 30))))))) (.add (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 7) (.var 7)) (.add (.mul (.var 13) (.var 13)) (.add (.mul (.var 19) (.var 19)) (.add (.mul (.var 25) (.var 25)) (.mul (.var 31) (.var 31))))))) (.add (.add (.mul (.var 2) (.var 2)) (.add (.mul (.var 8) (.var 8)) (.add (.mul (.var 14) (.var 14)) (.add (.mul (.var 20) (.var 20)) (.add (.mul (.var 26) (.var 26)) (.mul (.var 32) (.var 32))))))) (.add (.add (.mul (.var 3) (.var 3)) (.add (.mul (.var 9) (.var 9)) (.add (.mul (.var 15) (.var 15)) (.add (.mul (.var 21) (.var 21)) (.add (.mul (.var 27) (.var 27)) (.mul (.var 33) (.var 33))))))) (.add (.add (.mul (.var 4) (.var 4)) (.add (.mul (.var 10) (.var 10)) (.add (.mul (.var 16) (.var 16)) (.add (.mul (.var 22) (.var 22)) (.add (.mul (.var 28) (.var 28)) (.mul (.var 34) (.var 34))))))) (.add (.mul (.var 5) (.var 5)) (.add (.mul (.var 11) (.var 11)) (.add (.mul (.var 17) (.var 17)) (.add (.mul (.var 23) (.var 23)) (.add (.mul (.var 29) (.var 29)) (.mul (.var 35) (.var 35))))))))))))
    (.add (.add (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 2) (.var 2)) (.add (.mul (.var 3) (.var 3)) (.add (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5))))))) (.add (.add (.mul (.var 6) (.var 6)) (.add (.mul (.var 7) (.var 7)) (.add (.mul (.var 8) (.var 8)) (.add (.mul (.var 9) (.var 9)) (.add (.mul (.var 10) (.var 10)) (.mul (.var 11) (.var 11))))))) (.add (.add (.mul (.var 12) (.var 12)) (.add (.mul (.var 13) (.var 13)) (.add (.mul (.var 14) (.var 14)) (.add (.mul (.var 15) (.var 15)) (.add (.mul (.var 16) (.var 16)) (.mul (.var 17) (.var 17))))))) (.add (.add (.mul (.var 18) (.var 18)) (.add (.mul (.var 19) (.var 19)) (.add (.mul (.var 20) (.var 20)) (.add (.mul (.var 21) (.var 21)) (.add (.mul (.var 22) (.var 22)) (.mul (.var 23) (.var 23))))))) (.add (.add (.mul (.var 24) (.var 24)) (.add (.mul (.var 25) (.var 25)) (.add (.mul (.var 26) (.var 26)) (.add (.mul (.var 27) (.var 27)) (.add (.mul (.var 28) (.var 28)) (.mul (.var 29) (.var 29))))))) (.add (.mul (.var 30) (.var 30)) (.add (.mul (.var 31) (.var 31)) (.add (.mul (.var 32) (.var 32)) (.add (.mul (.var 33) (.var 33)) (.add (.mul (.var 34) (.var 34)) (.mul (.var 35) (.var 35))))))))))))
    (by decide) (fun a => field (a/6) (field (a%6) p))

private theorem laplacian_energy_carrier {blocks : Nat} (hb : 0 < blocks)
    (p : RatPoly) :
    HaarCarrierEqv blocks (angularLaplacian (angularSquare p))
      (polyAdd (polySmul 2 (hessianSquare p))
        (polySmul 2 (mixedGamma p (angularLaplacian p)))) := by
  have hs (i j : Nat) (hi : i<4) (hj : j<4) :
      HaarCarrierEqv blocks
        (angularLaplacian (polyMul (angularDerivative i j p) (angularDerivative i j p)))
        (polyAdd (polySmul 2 (angularSquare (angularDerivative i j p)))
          (polySmul 2 (polyMul (angularDerivative i j p)
            (angularDerivative i j (angularLaplacian p))))) :=
    (RatPolyCoeffEqv.haarCarrier (angularLaplacian_square (angularDerivative i j p))).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _)
        (HaarCarrierEqv.smul 2 (HaarCarrierEqv.mul
          (HaarCarrierEqv.refl blocks _)
          (angularLaplacian_angularDerivative_carrier hb hi hj p))))
  have hc : RatPolyCoeffEqv
      (six fun i j =>
        polyAdd (polySmul 2 (angularSquare (angularDerivative i j p)))
          (polySmul 2 (polyMul (angularDerivative i j p)
            (angularDerivative i j (angularLaplacian p)))))
      (polyAdd (polySmul 2 (hessianSquare p))
        (polySmul 2 (mixedGamma p (angularLaplacian p)))) :=
    (six_add _ _).trans
      (((six_smul 2 _).trans
        (RatPolyCoeffEqv.smul 2 (hessian_transpose_coeff p))).add (six_smul 2 _))
  exact (RatPolyCoeffEqv.haarCarrier (angularLaplacian_six _)).trans
    ((six_carrier hs).trans (RatPolyCoeffEqv.haarCarrier hc))

private theorem half_twice (p : RatPoly) :
    RatPolyCoeffEqv (polySmul HalfPow.half (polySmul 2 p)) p :=
  (RatPolyCoeffEqv.smul_assoc HalfPow.half 2 p).trans
    ((RatPolyCoeffEqv.smul_coefficient
      (by decide : Q'.eqv (HalfPow.half*2) 1) p).trans (RatPolyCoeffEqv.one_smul p))

/-- Genuine Gamma2-to-Hessian identity under EVERY original Haar insertion.
No centrality, Bochner, or positivity bound is supplied as a premise. -/
theorem gamma2_hessian_carrier {blocks : Nat} (hb : 0 < blocks) (p : RatPoly) :
    HaarCarrierEqv blocks (gamma2 p) (hessianSquare p) := by
  have h : HaarCarrierEqv blocks (gamma2 p)
      (polyAdd
        (polySmul HalfPow.half
          (polyAdd (polySmul 2 (hessianSquare p))
            (polySmul 2 (mixedGamma p (angularLaplacian p)))))
        (polyNeg (mixedGamma p (angularLaplacian p)))) :=
    HaarCarrierEqv.add (HaarCarrierEqv.smul HalfPow.half (laplacian_energy_carrier hb p))
      (HaarCarrierEqv.refl blocks _)
  have hc := (((RatPolyCoeffEqv.smul_add HalfPow.half _ _).trans
    ((half_twice _).add (half_twice _))).add
      (RatPolyCoeffEqv.refl (polyNeg (mixedGamma p (angularLaplacian p))))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => hessianSquare p | _ => mixedGamma p (angularLaplacian p)))
  exact h.trans (RatPolyCoeffEqv.haarCarrier hc)

/-- Constructed local curvature ONE, on the SAME supported carrier. -/
def bochner_curvature_certificate {blocks : Nat} (hb : 0 < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    Certificate blocks (polyAdd (gamma2 p) (polyNeg (angularSquare p))) :=
  .transport
    (HaarCarrierEqv.add (gamma2_hessian_carrier hb p) (HaarCarrierEqv.refl blocks _))
    (hessian_curvature_certificate hb hp)

/-- Any already-constructed positive ORIGINAL output weight retains the
Bochner margin; overlapping spectator variables are not separated. -/
theorem weighted_bochner_nonnegative {blocks : Nat} (hb : 0 < blocks)
    {p W : RatPoly} (hp : SupportedQuaternionBlocks blocks p)
    (C : Certificate blocks W) :
    (0 : Q') ≤ quaternionHaar blocks
      (polyMul W (polyAdd (gamma2 p) (polyNeg (angularSquare p)))) :=
  (Certificate.mul C (bochner_curvature_certificate hb hp)).haar_nonnegative

end YMGap.Continuum.SU2QuaternionAngularBochner

#print axioms YMGap.Continuum.SU2QuaternionAngularBochner.gamma2_hessian_carrier
#print axioms YMGap.Continuum.SU2QuaternionAngularBochner.bochner_curvature_certificate
#print axioms YMGap.Continuum.SU2QuaternionAngularBochner.weighted_bochner_nonnegative
