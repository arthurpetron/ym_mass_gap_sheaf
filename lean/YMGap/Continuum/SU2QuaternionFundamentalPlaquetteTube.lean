/-
# The open fundamental plaquette tube

In temporal-gauge coordinates the four side characters are chi_1(U_i V_i^-1).
Integrating the four lower links with chi_1(U_0 U_1 U_2^-1 U_3^-1) leaves
exactly (1/16) chi_1(V_0 V_1 V_2^-1 V_3^-1). All upper variables remain.

This is the selected fundamental channel of the reduced local tube. It is
NOT a lower bound for the full interacting, centered covariance. In
particular the outward-shifted probe response requires a longer tube and
control of all other signed terms. No original-action positivity input or
canonical frontier field is discharged here.
-/

import YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv

/-- The same ordered, oriented four-link plaquette word on any four blocks. -/
def plaquette (a b c d : Nat) : RatPoly :=
  characterPolynomial (PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
        (PolyQuaternion.coordinateVariable b))
      (PolyQuaternion.conj (PolyQuaternion.coordinateVariable c)))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable d))).scalar 1

/-- Literal fundamental character of the relative lower/upper link. -/
def sideCharacter (lower upper : Nat) : RatPoly :=
  characterPolynomial (PolyQuaternion.mul (PolyQuaternion.coordinateVariable lower)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable upper))).scalar 1

def tubeFactors : List RatPoly :=
  [plaquette 0 1 2 3, sideCharacter 0 4, sideCharacter 1 5,
    sideCharacter 2 6, sideCharacter 3 7]

def bareCoefficient : Q' := Q'.mkPos 1 16 (by decide)

/-- After four integrations the retained upper coordinates are numbered 0..3. -/
def propagatedPlaquette : RatPoly := polySmul bareCoefficient (plaquette 0 1 2 3)

/-- Exact finite coefficient comparison, checked by kernel reduction. -/
theorem tube_contraction_coefficients :
    RatPolyCoeffEqv (factorProduct (partialFactors 4 tubeFactors)) propagatedPlaquette := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem haar_coeff {p q : RatPoly} (h : RatPolyCoeffEqv p q) (blocks : Nat) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  have pin : ∀ r : RatPoly, quaternionHaar blocks r =
      ratWeightedSum (quaternionHaarMono blocks) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih => simp only [quaternionHaar, ratWeightedSum, ih]
  rw [pin, pin]
  exact h _

private theorem append_single_coeff (fs : List RatPoly) (p : RatPoly) :
    RatPolyCoeffEqv (factorProduct (fs ++ [p])) (polyMul (factorProduct fs) p) := by
  induction fs with
  | nil => exact RatPolyCoeffEqv.mul_comm p polyOne
  | cons f fs ih =>
      exact (RatPolyCoeffEqv.mul_left f ih).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm

/-- The conditional tube identity beneath ANY retained boundary polynomial.
Extra spectator coordinates and the remaining Haar block count are arbitrary. -/
theorem tube_boundary_haar (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks + 4)
        (factorProduct (tubeFactors ++ [liftBoundary 4 boundary])) ≈
      quaternionHaar blocks (polyMul propagatedPlaquette boundary) := by
  exact Q'.eqv_trans _ _ _ (partialFactors_boundary_haar 4 blocks tubeFactors boundary)
    (haar_coeff ((append_single_coeff _ boundary).trans
      (tube_contraction_coefficients.mul_right boundary)) blocks)

theorem bareCoefficient_pos : (0 : Q') < bareCoefficient := by decide

/-- The product of the four original fundamental heat coefficients, each 2*w^3. -/
def fourHeatCoefficients (w : Q') : Q' := qpow (coeffW w 1) 4

theorem fourHeatCoefficients_pin (w : Q') :
    fourHeatCoefficients w ≈ 16 * qpow w 12 :=
  poly_identity_of_normal_eq
    (.pow (.mul (.const 2) (.pow (.var 0) 3)) 4)
    (.mul (.const 16) (.pow (.var 0) 12)) (by decide) (fun _ => w)

/-- The Haar normalization cancels the four representation dimensions.
Nome dependence is explicit; this is NOT a coupling-uniform lower bound. -/
theorem weightedCoefficient_pin (w : Q') :
    fourHeatCoefficients w * bareCoefficient ≈ qpow w 12 := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (fourHeatCoefficients_pin w)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (by decide : bareCoefficient * 16 ≈ (1 : Q'))) (Q'.one_mul_eqv _)

/-- The exactly selected four-face heat term transmits the plaquette with
coefficient w^12, beneath every retained boundary polynomial. -/
theorem weighted_tube_boundary_haar (w : Q') (blocks : Nat) (boundary : RatPoly) :
    quaternionHaar (blocks + 4) (polySmul (fourHeatCoefficients w)
        (factorProduct (tubeFactors ++ [liftBoundary 4 boundary]))) ≈
      qpow w 12 * quaternionHaar blocks (polyMul (plaquette 0 1 2 3) boundary) := by
  have hbare : quaternionHaar blocks (polyMul propagatedPlaquette boundary) ≈
      bareCoefficient * quaternionHaar blocks (polyMul (plaquette 0 1 2 3) boundary) :=
    Q'.eqv_trans _ _ _ (haar_coeff
      (RatPolyCoeffEqv.polyMul_smul_left bareCoefficient _ boundary) blocks)
      (quaternionHaar_polySmul blocks bareCoefficient _)
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (tube_boundary_haar blocks boundary) hbare)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _ (weightedCoefficient_pin w))

end YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.plaquette
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.sideCharacter
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.tubeFactors
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.bareCoefficient
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.propagatedPlaquette
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.tube_contraction_coefficients
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.tube_boundary_haar
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.bareCoefficient_pos
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.fourHeatCoefficients
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.fourHeatCoefficients_pin
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.weightedCoefficient_pin
#print axioms YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube.weighted_tube_boundary_haar
