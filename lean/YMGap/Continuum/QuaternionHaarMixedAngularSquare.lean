/-
# A mixed angular square from two first-order identities

The head Laplacian converts the two identities Gamma(f)=4-f^2 and
sum(g_ij^2)=4-f^2 into sum(Gamma(g_ij))=8+f^2, provided f and each g_ij
are head-linear. No mixed partials are expanded and no positivity or
weight comparison is assumed. The physical application takes g_ij to
be the angular derivatives at a different edge of the SAME plaquette.
-/

import YMGap.Continuum.QuaternionHaarAngularLaplacianLinear

namespace YMGap.Continuum.QuaternionHaarMixedAngularSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarExposedHeatCasimir
open YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

attribute [local irreducible] angularLaplacian angularSquare

/-- The squared polynomial has angular Laplacian 2 Gamma(f)-6 f^2
whenever f is head-linear, with every Haar insertion retained. -/
theorem linear_square_laplacian {blocks : Nat} (hb : 0 < blocks)
    (f : RatPoly) (hf : HasQuaternionBlockDegree 0 1 f) :
    HaarCarrierEqv blocks (angularLaplacian (polyMul f f))
      (polyAdd (polySmul 2 (angularSquare f))
        (polySmul (-6) (polyMul f f))) := by
  have he := linear_angularLaplacian hb f hf
  exact (RatPolyCoeffEqv.haarCarrier (angularLaplacian_square f)).trans
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      ((HaarCarrierEqv.smul 2 (HaarCarrierEqv.mul_left f he)).trans
        (RatPolyCoeffEqv.haarCarrier
          (((cap_mul_left 2 _).symm.trans
            ((RatPolyCoeffEqv.refl _).mul
              ((RatPolyCoeffEqv.refl f).mul (cap_mul_left (-3) f).symm))).trans
            ((coeffEvalExpr_eqv_of_normalize_eq
              (.mul (.const 2) (.mul (.var 0) (.mul (.const (-3)) (.var 0))))
              (.mul (.const (-6)) (.mul (.var 0) (.var 0)))
              (by decide) (fun _ => f)).trans (cap_mul_left (-6) _))))))

private theorem laplacian_cap (c : Q') :
    RatPolyCoeffEqv (angularLaplacian (cap c)) polyZero := by
  exact (angularLaplacian_smul c polyOne).trans
    ((angularLaplacian_one.smul c).trans (RatPolyCoeffEqv.smul_zero c))

/-- A second-order square identity obtained by differentiating first-order
identities, not by estimating or dropping signed cross terms. -/
theorem mixed_square_of_linear_identities {blocks : Nat} (hb : 0 < blocks)
    (f : RatPoly) (g : Nat → Nat → RatPoly)
    (hf : HasQuaternionBlockDegree 0 1 f)
    (hg : ∀ i j, i < 4 → j < 4 → HasQuaternionBlockDegree 0 1 (g i j))
    (hfSquare : HaarCarrierEqv blocks (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))))
    (hgSquare : HaarCarrierEqv blocks (six (fun i j => polyMul (g i j) (g i j)))
      (polyAdd (cap 4) (polyNeg (polyMul f f)))) :
    HaarCarrierEqv blocks (six (fun i j => angularSquare (g i j)))
      (polyAdd (cap 8) (polyMul f f)) := by
  let F := polyMul f f
  let S := six (fun i j => polyMul (g i j) (g i j))
  let E := six (fun i j => angularSquare (g i j))
  let G := polyAdd (cap 4) (polyNeg F)
  have hsum : HaarCarrierEqv blocks (angularLaplacian S)
      (polyAdd (polySmul 2 E) (polySmul (-6) S)) := by
    exact (RatPolyCoeffEqv.haarCarrier (angularLaplacian_six _)).trans
      ((six_carrier (fun i j hi hj => linear_square_laplacian hb (g i j) (hg i j hi hj))).trans
        (RatPolyCoeffEqv.haarCarrier ((six_add _ _).trans
          ((six_smul 2 _).add (six_smul (-6) _)))))
  have hlinear : HaarCarrierEqv blocks (angularLaplacian F)
      (polyAdd (polySmul 2 G) (polySmul (-6) F)) :=
    (linear_square_laplacian hb f hf).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.smul 2 hfSquare) (HaarCarrierEqv.refl _ _))
  have hneg : HaarCarrierEqv blocks (angularLaplacian (polyNeg F))
      (polySmul (-1) (polyAdd (polySmul 2 G) (polySmul (-6) F))) :=
    (QuaternionHaarExposedHeatCasimir.angularLaplacian_carrier hb
      (RatPolyCoeffEqv.haarCarrier (neg_smul F))).trans
      ((RatPolyCoeffEqv.haarCarrier (angularLaplacian_smul (-1) F)).trans
        (HaarCarrierEqv.smul (-1) hlinear))
  have hright : HaarCarrierEqv blocks (angularLaplacian G)
      (polyAdd (cap (-8)) (polySmul 8 F)) := by
    have hn : RatPolyCoeffEqv
        (polySmul (-1) (polyAdd (polySmul 2 G) (polySmul (-6) F)))
        (polyAdd (cap (-8)) (polySmul 8 F)) :=
      ((cap_mul_left (-1) _).symm.trans
        ((RatPolyCoeffEqv.refl _).mul
          ((cap_mul_left 2 _).symm.add (cap_mul_left (-6) _).symm))).trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.const (-1)) (.add (.mul (.const 2) (.add (.const 4) (.neg (.var 0))))
            (.mul (.const (-6)) (.var 0))))
          (.add (.const (-8)) (.mul (.const 8) (.var 0)))
          (by decide) (fun _ => F)).trans
          ((RatPolyCoeffEqv.refl _).add (cap_mul_left 8 F)))
    exact (RatPolyCoeffEqv.haarCarrier (angularLaplacian_add _ _)).trans
      ((HaarCarrierEqv.add (RatPolyCoeffEqv.haarCarrier (laplacian_cap 4)) hneg).trans
        (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.zero_add _).trans hn)))
  have hmain : HaarCarrierEqv blocks
      (polyAdd (polySmul 2 E) (polySmul (-6) G))
      (polyAdd (cap (-8)) (polySmul 8 F)) :=
    (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.smul (-6) hgSquare.symm)).trans
      (hsum.symm.trans ((QuaternionHaarExposedHeatCasimir.angularLaplacian_carrier hb hgSquare).trans hright))
  have hadd := HaarCarrierEqv.add hmain (HaarCarrierEqv.refl blocks (polySmul 6 G))
  have hl : RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul 2 E) (polySmul (-6) G)) (polySmul 6 G))
      (polySmul 2 E) :=
    (((cap_mul_left 2 E).symm.add (cap_mul_left (-6) G).symm).add
      (cap_mul_left 6 G).symm).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const (-6)) (.var 1)))
          (.mul (.const 6) (.var 1)))
        (.mul (.const 2) (.var 0)) (by decide) (fun | 0 => E | _ => G)).trans
        (cap_mul_left 2 E))
  have hr : RatPolyCoeffEqv
      (polyAdd (polyAdd (cap (-8)) (polySmul 8 F)) (polySmul 6 G))
      (polySmul 2 (polyAdd (cap 8) F)) :=
    (((RatPolyCoeffEqv.refl _).add (cap_mul_left 8 F).symm).add
      (cap_mul_left 6 G).symm).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.const (-8)) (.mul (.const 8) (.var 0)))
          (.mul (.const 6) (.add (.const 4) (.neg (.var 0)))))
        (.mul (.const 2) (.add (.const 8) (.var 0)))
        (by decide) (fun _ => F)).trans (cap_mul_left 2 _))
  have htwice := (RatPolyCoeffEqv.haarCarrier hl.symm).trans
    (hadd.trans (RatPolyCoeffEqv.haarCarrier hr))
  have hcancel (p : RatPoly) : RatPolyCoeffEqv
      (polySmul HalfPow.half (polySmul 2 p)) p :=
    ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv (HalfPow.half * 2) 1) p)).trans
      (RatPolyCoeffEqv.one_smul p)
  exact (RatPolyCoeffEqv.haarCarrier (hcancel E).symm).trans
    ((HaarCarrierEqv.smul HalfPow.half htwice).trans
      (RatPolyCoeffEqv.haarCarrier (hcancel _)))

#print axioms linear_square_laplacian
#print axioms mixed_square_of_linear_identities

end YMGap.Continuum.QuaternionHaarMixedAngularSquare
