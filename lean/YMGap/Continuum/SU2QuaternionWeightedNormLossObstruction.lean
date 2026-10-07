/-
# A positive nonstationary weight need not give positive heat norm loss

On the literal productMap 1 (1/2) 1 [0], take x=polyVar 0,
h=1+x/2 and f=1-x/4. Their lower floors are constructed from the
original coordinate interval. Direct finite Haar evaluation gives
H[h*f^2]=61/64 and H[h*(P f)^2]=4065/4096, so the weighted square
loss is -161/4096. The literal output also has squared Haar distance
zero from 1-x/32; no heat eigenvalue is supplied as a premise.

Thus a cleared reverse Poincare estimate with this weighted loss on
the right cannot hold for any nonnegative proposed angular cost.
This diagnoses the arbitrary-weight shortcut, NOT the ORIGINAL
interacting K(V input) transfer, a completed OS form or Yang--Mills.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

namespace YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval (coordinateInterval)

local infix:50 " ≈ " => Q'.eqv

def half : Q' := Q'.mkPos 1 2 (by decide)
def quarter : Q' := Q'.mkPos 1 4 (by decide)
def threeQuarter : Q' := Q'.mkPos 3 4 (by decide)
def coordinate : RatPoly := polyVar 0
def weight : RatPoly := polyAdd (cap 1) (polyMul (cap half) coordinate)
def probe : RatPoly := polyAdd (cap 1) (polyNeg (polyMul (cap quarter) coordinate))
def image : RatPoly := productMap 1 half 1 [0] probe
def explicitImage : RatPoly := polyAdd (cap 1)
  (polyNeg (polyMul (cap (Q'.mkPos 1 32 (by decide))) coordinate))
def weightedInputSquare : Q' := quaternionHaar 1 (polyMul weight (polyMul probe probe))
def weightedOutputSquare : Q' := quaternionHaar 1 (polyMul weight (polyMul image image))
def weightedLoss : Q' := weightedInputSquare-weightedOutputSquare

/-- Explicit floor h>=1/2 from the supported sharp coordinate interval. -/
def weight_floor_certificate : Certificate 1 (polyAdd weight (polyNeg (cap half))) :=
  Certificate.ofCoeff
    (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (Certificate.smul half (by decide)
      (coordinateInterval (blocks := 1) (coordinate := 0) (by decide)).lower)

/-- The SAME diagnostic weight has constructed positivity, not an assumed sign. -/
def weight_certificate : Certificate 1 weight :=
  Certificate.ofCoeff
    (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (weight_floor_certificate.add (Certificate.constant 1 half (by decide)))

/-- Explicit floor f>=3/4; the diagnostic does not rely on a signed probe. -/
def probe_floor_certificate : Certificate 1 (polyAdd probe (polyNeg (cap threeQuarter))) :=
  Certificate.ofCoeff
    (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (Certificate.smul quarter (by decide)
      (coordinateInterval (blocks := 1) (coordinate := 0) (by decide)).upper)

/-- The literal degree-one finite-heat output is coefficient-exact. This
single staged computation avoids squaring the expanded kernel expression. -/
theorem literal_output_coeff_pin : RatPolyCoeffEqv image explicitImage :=
  RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- Exact literal finite-heat output, in squared Haar distance. -/
theorem literal_output_square_pin : quaternionHaar 1
    (polyMul (polyAdd image (polyNeg explicitImage))
      (polyAdd image (polyNeg explicitImage))) ≈ 0 := by
  have h := literal_output_coeff_pin.add (RatPolyCoeffEqv.refl (polyNeg explicitImage))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (h.mul h)) (by decide)

theorem weightedInputSquare_pin : weightedInputSquare ≈ Q'.mkPos 61 64 (by decide) := by decide

/-- This evaluates the actual productMap, not a substituted attenuation. -/
theorem weightedOutputSquare_pin : weightedOutputSquare ≈ Q'.mkPos 4065 4096 (by decide) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    ((literal_output_coeff_pin.mul literal_output_coeff_pin).mul_left weight)) (by decide)

theorem weightedLoss_pin : weightedLoss ≈ -(Q'.mkPos 161 4096 (by decide)) :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' weightedInputSquare_pin
    (Q'.neg_eqv_congr _ _ weightedOutputSquare_pin)) (by decide)

theorem weightedLoss_negative : weightedLoss < (0 : Q') :=
  Q'.lt_of_le_of_lt (Q'.le_of_eqv weightedLoss_pin) (by decide)

/-- Regardless of how an angular cost is constructed, its nonnegative value
cannot be bounded by this negative weighted square loss. The coefficients
are exactly those of the cleared reverse Poincare law at nome one half. -/
theorem weighted_reverse_poincare_false (angular : Q') (hangular : (0 : Q') ≤ angular) :
    ¬ (((1 : Q')-half*half)*angular ≤ (half*half)*weightedLoss) := by
  intro h
  have hleft : (0 : Q') ≤ ((1 : Q')-half*half)*angular :=
    Q'.mul_nonneg _ _ (by decide) hangular
  have hright : (half*half)*weightedLoss < (0 : Q') :=
    Q'.lt_of_le_of_lt
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ weightedLoss_pin)) (by decide)
  have hbad : (0 : Q') < 0 := Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hleft h) hright
  exact (by decide : ¬ ((0 : Q') < 0)) hbad

end YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction

#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.weight_floor_certificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.weight_certificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.probe_floor_certificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.literal_output_coeff_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.literal_output_square_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.weightedInputSquare_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.weightedOutputSquare_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.weightedLoss_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.weightedLoss_negative
#print axioms YMGap.Continuum.SU2QuaternionWeightedNormLossObstruction.weighted_reverse_poincare_false
