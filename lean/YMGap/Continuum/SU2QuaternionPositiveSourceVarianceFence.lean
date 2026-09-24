/-
# Positive-source residual sign is not automatic

On the actual one-link product heat, the strictly positive source
q = 1 + (1 + chi_1)^2 has a negative bare-loss comparison defect.
Consequently E/Var is NOT bounded above by the bare fundamental heat loss.
All quantities below are the existing source moments and source energy,
not a replacement finite matrix or an assumed interacting eigenrelation.

This fences a positivity-only shortcut. The source is not asserted to be
an original four-dimensional terminal message, so this is neither a
Yang--Mills counterexample nor a refutation of continuum survival.
-/

import YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence
import YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate

namespace YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence
  (half fundamental fundamental_supported)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c hab)
    (Q'.mul_eqv_congr_left b _ _ hcd)

private theorem positive_of_eqv {a b : Q'} (h : a ≈ b) (hb : (0 : Q') < b) :
    (0 : Q') < a := by
  have hn : ¬ a ≤ (0 : Q') := by
    intro ha
    exact (Int.not_le.mpr hb) (Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) ha)
  exact Int.not_le.mp hn

/-- The complete endpoint source, with an explicit positive constant term. -/
def positiveSource : RatPoly :=
  polyAdd (polySmul 2 polyOne)
    (polyAdd (polySmul 2 fundamental) (polyMul fundamental fundamental))

theorem positiveSource_supported : SupportedQuaternionBlocks 1 positiveSource :=
  supported_add (polySmul_supported (supported_one 1) 2)
    (supported_add (polySmul_supported fundamental_supported 2)
      (supported_polyMul fundamental_supported fundamental_supported))

/-- Positivity is supplied by polynomial-square data, not a sign hypothesis. -/
def positiveSourceCertificate : Certificate 1 positiveSource :=
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.add (.one 1) (.square (polyAdd polyOne fundamental)
      (supported_add (supported_one 1) fundamental_supported)))

/-- The actual two-endpoint heat factor also has a strict quarter floor. -/
def heatKernelQuarterFloor : Certificate 2
    (polyAdd (heatAt 0 1 half 3)
      (polyNeg (QuaternionHaarPolynomialSquareBound.cap (Q'.mkPos 1 4 (by decide))))) :=
  SU2QuaternionHalfHeatThreeCertificate.heatAt_half_three_quarterFloor

def mass : Q' := sourceMoment 1 half 3 [0] positiveSource polyOne
def firstMoment : Q' := sourceMoment 1 half 3 [0] positiveSource fundamental
def secondMoment : Q' :=
  sourceMoment 1 half 3 [0] positiveSource (polyMul fundamental fundamental)
def energy : Q' := sourceEnergy 1 half 3 [0] positiveSource fundamental

/-- The centered numerator uses q*P(q), not the raw q-squared Haar weight. -/
def varianceNumerator : Q' := mass * secondMoment - firstMoment * firstMoment

/-- Bare one-link fundamental transmission, not an interacting eigenvalue. -/
def bareRate : Q' := qpow half 3

/-- The cleared deficit in the proposed bare-loss upper estimate. -/
def clearedResidual : Q' := ((1 : Q') - bareRate) * varianceNumerator - mass * energy

set_option maxRecDepth 100000 in
theorem mass_value : mass ≈ Q'.mkPos 2433 256 (by decide) := by decide

set_option maxRecDepth 100000 in
theorem firstMoment_value : firstMoment ≈ Q'.mkPos 897 128 (by decide) := by decide

set_option maxRecDepth 100000 in
theorem secondMoment_value : secondMoment ≈ Q'.mkPos 3333 256 (by decide) := by decide

set_option maxRecDepth 100000 in
theorem energy_value : energy ≈ Q'.mkPos 229503 32768 (by decide) := by decide

attribute [local irreducible] mass firstMoment secondMoment energy

theorem varianceNumerator_value :
    varianceNumerator ≈ Q'.mkPos 4890753 65536 (by decide) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (mul_eqv mass_value secondMoment_value)
      (Q'.neg_eqv_congr _ _ (mul_eqv firstMoment_value firstMoment_value)))
    (by decide)

attribute [local irreducible] varianceNumerator

theorem clearedResidual_value :
    clearedResidual ≈ -(Q'.mkPos 10616463 8388608 (by decide)) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left ((1 : Q') - bareRate) _ _ varianceNumerator_value)
      (Q'.neg_eqv_congr _ _ (mul_eqv mass_value energy_value)))
    (by decide)

theorem mass_positive : (0 : Q') < mass :=
  positive_of_eqv mass_value (by decide)

theorem varianceNumerator_positive : (0 : Q') < varianceNumerator :=
  positive_of_eqv varianceNumerator_value (by decide)

/-- Both source positivity and a nonzero interacting variance coexist with
the unfavorable sign. No statement about a physical terminal source follows. -/
theorem clearedResidual_negative : clearedResidual < (0 : Q') :=
  Q'.lt_of_le_of_lt (Q'.le_of_eqv clearedResidual_value)
    (by decide : -(Q'.mkPos 10616463 8388608 (by decide)) < (0 : Q'))

/-- Multiplying the proposed normalized bound by Z^2 gives this false bound.
The failure is on the original source moments, with no surrogate variance. -/
theorem bare_loss_variance_bound_false :
    ¬ (mass * energy ≤ ((1 : Q') - bareRate) * varianceNumerator) := by
  intro h
  have he := mul_eqv mass_value energy_value
  have hv := Q'.mul_eqv_congr_left ((1 : Q') - bareRate) _ _ varianceNumerator_value
  have hle := Q'.le_trans' _ _ _ (Q'.le_of_eqv he.symm)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hv))
  exact (by decide : ¬ (Q'.mkPos 2433 256 (by decide) * Q'.mkPos 229503 32768 (by decide) ≤
    ((1 : Q') - bareRate) * Q'.mkPos 4890753 65536 (by decide))) hle

end YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence

#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.positiveSource_supported
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.positiveSourceCertificate
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.heatKernelQuarterFloor
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.mass_value
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.firstMoment_value
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.secondMoment_value
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.energy_value
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.varianceNumerator_value
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.clearedResidual_value
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.mass_positive
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.varianceNumerator_positive
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.clearedResidual_negative
#print axioms YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence.bare_loss_variance_bound_false
