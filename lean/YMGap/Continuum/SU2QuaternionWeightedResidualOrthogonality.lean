/-
# Exact orthogonality of weighted residuals to independent tests

The division-free weighted residual is conditionally centered against its
original weight.  Hence its weighted Haar pairing with any polynomial that is
independent of the selected block vanishes exactly, and subtracting any
rational multiple of such a polynomial does not change an arbitrary pairing.

These are finite algebraic identities.  They assume no positivity or support,
and provide no stable decomposition, uniform estimate, or continuum claim.
-/

import YMGap.Continuum.SU2QuaternionWeightedBlockCentering
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.SU2QuaternionWeightedResidualOrthogonality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Exact original-weight orthogonality to a selected-block-independent test. -/
theorem weightedResidual_pair_independent_zero
    (blocks i : Nat) (hi : i < blocks) (a f h : RatPoly)
    (hh : QuaternionBlockIndependent i h) :
    weightedPair blocks a (weightedResidual i a f) h ≈ 0 := by
  let r := weightedResidual i a f
  have hcenter : RatPolyCoeffEqv (project i (polyMul a r)) polyZero := by
    dsimp only [r]
    exact project_weightedResidual_zero i a f
  have hreorder : RatPolyCoeffEqv (polyMul (polyMul r h) a)
      (polyMul h (polyMul a r)) :=
    (RatPolyCoeffEqv.mul_comm (polyMul r h) a).trans
      ((RatPolyCoeffEqv.mul_assoc a r h).symm.trans
        (RatPolyCoeffEqv.mul_comm (polyMul a r) h))
  have hproject : RatPolyCoeffEqv (project i (polyMul (polyMul r h) a)) polyZero :=
    (project_congr i hreorder).trans
      ((project_mul_of_independent i h (polyMul a r) hh).trans
        ((hcenter.mul_left h).trans (RatPolyCoeffEqv.mul_zero_right h)))
  unfold weightedPair
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (project_mean blocks i hi (polyMul (polyMul r h) a)))
    (haar_of_coeff hproject)

/-- Subtracting an independent component from the second test leaves the
weighted residual pairing unchanged. -/
theorem weightedResidual_pair_sub_independent
    (blocks i : Nat) (hi : i < blocks) (a f F h : RatPoly) (c : Q')
    (hh : QuaternionBlockIndependent i h) :
    weightedPair blocks a (weightedResidual i a f)
        (polyAdd F (polySmul (-c) h)) ≈
      weightedPair blocks a (weightedResidual i a f) F := by
  let r := weightedResidual i a f
  have hzero : weightedPair blocks a r h ≈ 0 := by
    dsimp only [r]
    exact weightedResidual_pair_independent_zero blocks i hi a f h hh
  have hscaled : weightedPair blocks a (polySmul (-c) h) r ≈ 0 :=
    Q'.eqv_trans _ _ _ (weighted_smul_left blocks a (-c) h r)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (-c) _ _
          (Q'.eqv_trans _ _ _ (weighted_symm blocks a h r) hzero))
        (QPoly.q_mul_zero (-c)))
  exact Q'.eqv_trans _ _ _
    (weighted_symm blocks a r (polyAdd F (polySmul (-c) h)))
    (Q'.eqv_trans _ _ _ (weighted_add_left blocks a F (polySmul (-c) h) r)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (weighted_symm blocks a F r) hscaled)
        (Q'.eqv_of_eq (Q'.add_zero' _))))

end YMGap.Continuum.SU2QuaternionWeightedResidualOrthogonality

#print axioms YMGap.Continuum.SU2QuaternionWeightedResidualOrthogonality.weightedResidual_pair_independent_zero
#print axioms YMGap.Continuum.SU2QuaternionWeightedResidualOrthogonality.weightedResidual_pair_sub_independent
