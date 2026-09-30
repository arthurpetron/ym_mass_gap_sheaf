/-
# Original-weight angular energy controlled by head-independent prediction

This is the kinematics-free part of the original relative Ward argument.
The signed angular energy of any supported head-linear polynomial is bounded
by the prediction error against any supported head-independent polynomial.
It uses the SAME original weight and relative derivative certificates; it
does not require the fundamental-plaquette identity or a partition bound.
-/

import YMGap.Continuum.QuaternionHaarRelativePredictionFloor

namespace YMGap.Continuum.QuaternionHaarRelativePredictionEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarGeneralizedLinearWard
open YMGap.Continuum.QuaternionHaarRelativePredictionFloor (weighted_square_young)
open YMGap.Continuum.RationalRelativeWardPrediction

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The explicit, input-independent coefficient in the signed energy bound. -/
def energyPredictionFactor (C : Q') : Q' := 24 + 36*(C*C)

theorem energyPredictionFactor_positive (C : Q') :
    (0 : Q') < energyPredictionFactor C := by
  have hC : (0 : Q') ≤ C*C := SumOfSquares.q_mul_self_nonneg C
  have hterm : (0 : Q') ≤ 36*(C*C) := Q'.mul_nonneg _ _ (by decide) hC
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 24)
    (Q'.add_le_self_of_nonneg 24 (36*(C*C)) hterm)

/-- General original-action energy--prediction inequality. No kinematic
identity, specific plaquette, positivity of a global partition, or volume
comparison enters. -/
theorem angular_energy_le_prediction {tail : Nat} {W f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hlinear : HasQuaternionBlockDegree 0 1 f)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hfree : HasQuaternionBlockDegree 0 0 q) :
    H (tail+1) (polyMul W (angularSquare f)) ≤
      energyPredictionFactor C * H (tail+1)
        (polyMul W (polyMul (polyAdd f (polySmul (-1) q))
          (polyAdd f (polySmul (-1) q)))) := by
  let g := polyAdd f (polySmul (-1) q)
  let E := H (tail+1) (polyMul W (angularSquare f))
  let F := H (tail+1) (polyMul W (polyMul f f))
  let A := H (tail+1) (polyMul W (polyMul g g))
  let B := H (tail+1) (polyMul W (polyMul g f))
  let Rf := generalizedResidual tail W f f
  let Rg := generalizedResidual tail W g f
  have hg : SupportedQuaternionBlocks (tail+1) g :=
    supported_add hf (polySmul_supported hq (-1))
  have hwf : E+Rf ≈ 3*F := Q'.eqv_trans _ _ _ (self_ward tail W f hlinear)
    (Q'.mul_eqv_congr_left 3 _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W f f)))
  have hFE : 3*F ≤ 2*(1+C*C)*E := square_le_energy C E F Rf hC hwf
    (residual_upper_scaled hC R hf hf (2*(C*C)))
  have hwg : E+Rg ≈ 3*B := Q'.eqv_trans _ _ _
    (independent_shift_ward tail W f q hlinear hfree)
    (Q'.mul_eqv_congr_left 3 _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W g f)))
  have hy : -(2*Rg) ≤ 6*(C*C)*A+E := by
    have hh := residual_lower_scaled hC R hg hf 1
    have hl : -(2*Rg) ≈ -(2*1*Rg) := Q'.neg_eqv_congr _ _
      (Q'.eqv_symm (Q'.mul_eqv_congr_right _ _ Rg (Q'.mul_one_eqv 2)))
    have hr : 6*(C*C)*A+(1*1)*E ≈ 6*(C*C)*A+E :=
      Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ E (by decide)) (Q'.one_mul_eqv E))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv hr))
  have hc := weighted_square_young (R 0 1 (by decide) (by decide)).positive
    hg hf (4*(1+C*C))
  exact energy_le_prediction C E F A B Rg hFE hwg hy hc

#print axioms energyPredictionFactor
#print axioms energyPredictionFactor_positive
#print axioms angular_energy_le_prediction

end YMGap.Continuum.QuaternionHaarRelativePredictionEnergy
