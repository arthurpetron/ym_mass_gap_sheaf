/-
# Original relative energy for every head-affine polynomial

Split by literal head degree, use the negative constant sector as the
predictor, and retain the whole polynomial on the right. No incident-face
decomposition or fundamental-plaquette kinematic identity is needed. This
is the reusable estimate required after differentiating another link.
-/

import YMGap.Continuum.QuaternionHaarHeadAffineSplit
import YMGap.Continuum.QuaternionHaarRelativePredictionEnergy

namespace YMGap.Continuum.QuaternionHaarAffineRelativeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.QuaternionHaarHeadAffineSplit
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativePredictionEnergy
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The head-independent sector contributes no angular derivative, including
when its literal representation contains zero-coefficient terms. -/
theorem angularDerivative_linearPart {i j : Nat} (hi : i < 4) (hj : j < 4)
    (p : RatPoly) (hp : DegreeLE 0 1 p) :
    RatPolyCoeffEqv (angularDerivative i j p)
      (angularDerivative i j (linearPart p)) :=
  (angularDerivative_congr i j (headAffine_split p hp)).trans
    ((angularDerivative_add i j (linearPart p) (constantPart p)).trans
      (((RatPolyCoeffEqv.refl _).add
        (angularDerivative_independent_zero hi hj _ (constantPart_degree p))).trans
        (RatPolyCoeffEqv.add_zero _)))

theorem angularSquare_linearPart (p : RatPoly) (hp : DegreeLE 0 1 p) :
    RatPolyCoeffEqv (angularSquare p) (angularSquare (linearPart p)) := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) :=
    (angularDerivative_linearPart hi hj p hp).mul (angularDerivative_linearPart hi hj p hp)
  unfold angularSquare six
  exact (h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add (h 2 3 (by decide) (by decide))))))

/-- Uniform over all supported head-affine polynomials, with the original
weight and explicit relative derivative cost retained. This is not a
physical-time transfer estimate. -/
theorem angular_energy_le_square {tail : Nat} {W p : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hdegree : DegreeLE 0 1 p) :
    H (tail+1) (polyMul W (angularSquare p)) ≤
      energyPredictionFactor C * H (tail+1) (polyMul W (polyMul p p)) := by
  let f := linearPart p
  let q := polySmul (-1) (constantPart p)
  let g := polyAdd f (polySmul (-1) q)
  have hdouble : RatPolyCoeffEqv
      (polySmul (-1) (polySmul (-1) (constantPart p))) (constantPart p) :=
    (RatPolyCoeffEqv.smul_assoc (-1) (-1) _).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (by decide : ((-1 : Q') * (-1)) ≈ 1) _).trans (RatPolyCoeffEqv.one_smul _))
  have hg : RatPolyCoeffEqv g p :=
    ((RatPolyCoeffEqv.refl f).add hdouble).trans (headAffine_split p hdegree).symm
  have hmain := angular_energy_le_prediction hC R
    (linearPart_supported hp) (linearPart_degree p) q
    (polySmul_supported (constantPart_supported hp) (-1))
    ((constantPart_degree p).smul (-1))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((angularSquare_linearPart p hdegree).mul_left W)))
    (Q'.le_trans' _ _ _ hmain
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (haar_of_coeff ((hg.mul hg).mul_left W)))))

#print axioms angularDerivative_linearPart
#print axioms angularSquare_linearPart
#print axioms angular_energy_le_square

end YMGap.Continuum.QuaternionHaarAffineRelativeEnergy
