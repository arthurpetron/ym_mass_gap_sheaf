/-
# Exact Pythagoras for the division-free weighted conditional residual

With m=P_i(a), M=P_i(a*f), and r=m*f-M, the SAME original Haar
functional satisfies

  H[a*(m*f)^2] = H[a*r^2] + H[m*M^2].

The identity uses conditional pull-through and the existing exact
weightedResidual_quadratic. When a has a supplied positive square
certificate, its selected conditional projection has a constructed
certificate too; the correction is therefore nonnegative. No inverse,
normalization, dimension factor, or analytic estimate is assumed.

The consumer is the actual finite seed norm estimate. This generic
conditional norm reduction does not establish a stable sum of residuals,
an interacting temporal gap, or an OS/continuum identification.
-/

import YMGap.Continuum.SU2QuaternionWeightedBlockCentering
import YMGap.Continuum.SU2QuaternionHaarBlockCertificate

namespace YMGap.Continuum.SU2QuaternionWeightedResidualNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate (project_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem projected_pythagoras (i : Nat) (a f : RatPoly) :
    let m := project i a
    let M := project i (polyMul a f)
    let r := weightedResidual i a f
    RatPolyCoeffEqv
      (project i (polyMul a (polyMul (polyMul m f) (polyMul m f))))
      (polyAdd (project i (polyMul a (polyMul r r))) (polyMul m (polyMul M M))) := by
  let m := project i a
  let M := project i (polyMul a f)
  let S := project i (polyMul a (polyMul f f))
  have hrearrange : RatPolyCoeffEqv
      (polyMul a (polyMul (polyMul m f) (polyMul m f)))
      (polyMul (polyMul m m) (polyMul a (polyMul f f))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => a | 1 => m | _ => f)
  have hp : RatPolyCoeffEqv
      (project i (polyMul a (polyMul (polyMul m f) (polyMul m f))))
      (polyMul (polyMul m m) S) :=
    (project_congr i hrearrange).trans
      (project_mul_of_independent i (polyMul m m) (polyMul a (polyMul f f))
        (quaternionBlockIndependent_polyMul (project_independent i a) (project_independent i a)))
  have halg : RatPolyCoeffEqv (polyMul (polyMul m m) S)
      (polyAdd (polyMul m (polyAdd (polyMul m S) (polyNeg (polyMul M M))))
        (polyMul m (polyMul M M))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.add
        (.mul (.var 0) (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2)))))
        (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => m | 1 => S | _ => M)
  exact hp.trans (halg.trans
    ((weightedResidual_quadratic i a f).symm.add (RatPolyCoeffEqv.refl _)))

/-- Exact division-free weighted Pythagoras. Neither support nor positivity
is needed for the identity itself; the selected block is in the Haar carrier. -/
theorem weightedResidual_pythagoras (blocks i : Nat) (hi : i < blocks) (a f : RatPoly) :
    quaternionHaar blocks
      (polyMul a (polyMul (polyMul (project i a) f) (polyMul (project i a) f))) ≈
      quaternionHaar blocks
        (polyMul a (polyMul (weightedResidual i a f) (weightedResidual i a f))) +
      quaternionHaar blocks
        (polyMul (project i a) (polyMul (project i (polyMul a f)) (project i (polyMul a f)))) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (project_mean blocks i hi _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (projected_pythagoras i a f))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (project_mean blocks i hi _) (Q'.eqv_refl _))))

/-- The positive conditional correction supplies coefficient-one norm
reduction, with an explicit certificate for the original weight. -/
theorem weightedResidual_square_le (blocks i : Nat) (hi : i < blocks) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks blocks a) (hf : SupportedQuaternionBlocks blocks f)
    (P : Certificate blocks a) :
    quaternionHaar blocks
      (polyMul a (polyMul (weightedResidual i a f) (weightedResidual i a f))) ≤
      quaternionHaar blocks
        (polyMul a (polyMul (polyMul (project i a) f) (polyMul (project i a) f))) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (((project_certificate blocks i hi ha P).mul
        (Certificate.square (project i (polyMul a f))
          (project_supported i (supported_polyMul ha hf)))).haar_nonnegative))
    (Q'.ge_of_eqv (weightedResidual_pythagoras blocks i hi a f))

#print axioms weightedResidual_pythagoras
#print axioms weightedResidual_square_le

end YMGap.Continuum.SU2QuaternionWeightedResidualNorm
