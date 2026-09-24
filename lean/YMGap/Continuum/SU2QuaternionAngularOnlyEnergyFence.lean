/-
# Angular-only source-energy fence

The coefficient-one angular-only estimate for the actual one-link product
heat energy is false, even for a source which is one plus an explicit square.
This is a finite rational counterexample on the original polynomial carrier;
it does not assert anything about the interacting odd marginal or a continuum
limit.
-/

import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

namespace YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- The nome used by the finite counterexample. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The actual fundamental character on the sole original quaternion block. -/
def fundamental : RatPoly :=
  characterPolynomial (PolyQuaternion.coordinateVariable 0).scalar 1

/-- A strictly positive source: `1 + 2 * fundamental^2`. -/
def positiveSource : RatPoly :=
  polyAdd polyOne (polySmul 2 (polyMul fundamental fundamental))

/-- The actual one-link product-heat source energy, with active list `[0]`. -/
def sourceEnergy1 (w : Q') (K : Nat) : Q' :=
  sourceEnergy 1 w K [0] positiveSource fundamental

/-- The actual one-block weighted angular energy. -/
def weightedAngularEnergy0 : Q' :=
  weightedAngularEnergy 0 positiveSource fundamental

theorem fundamental_supported : SupportedQuaternionBlocks 1 fundamental := by
  exact character_supported (coordinate_supported (by omega : 0 < 1) (0 : Fin 4)) 1

theorem positiveSource_supported : SupportedQuaternionBlocks 1 positiveSource :=
  supported_add (supported_one 1)
    (polySmul_supported (supported_polyMul fundamental_supported fundamental_supported) 2)

/-- Witness-bearing positivity certificate for the source itself.  Its first
summand is the positive constant one, rather than a merely nonnegative square. -/
def positiveSourceCertificate : Certificate 1 positiveSource :=
  .add (Certificate.one 1)
    (.smul 2 (by decide) (.square fundamental fundamental_supported))

/-- The chosen cutoff satisfies the same sufficient-cutoff guard used by the
Taylor estimate. -/
theorem cutoff_guard : sufficientCutoff half ≤ 3 := by decide

set_option maxRecDepth 4096 in
/-- Exact angular cost of the strictly positive source and fundamental test. -/
theorem weightedAngularEnergy0_value :
    weightedAngularEnergy0 ≈ (23 : Q') := by decide

set_option maxRecDepth 8192 in
/-- Exact value of the actual one-link source energy. -/
theorem sourceEnergy1_value :
    sourceEnergy1 half 3 ≈ Q'.mkPos 97727 8192 (by decide) := by decide

/-- The proposed coefficient-one angular-only estimate fails on the actual
one-link product heat kernel, despite the explicit positive source. -/
theorem angular_only_energy_bound_false :
    ¬ (sourceEnergy1 half 3 ≤
      ((1 : Q') - half) * weightedAngularEnergy0) := by
  intro h
  have hle : Q'.mkPos 97727 8192 (by decide) ≤
      ((1 : Q') - half) * (23 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm sourceEnergy1_value))
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ weightedAngularEnergy0_value)))
  exact (by decide : ¬ (Q'.mkPos 97727 8192 (by decide) ≤
    ((1 : Q') - half) * (23 : Q'))) hle

end YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence

#print axioms YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence.fundamental_supported
#print axioms YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence.positiveSource_supported
#print axioms YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence.positiveSourceCertificate
#print axioms YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence.cutoff_guard
#print axioms YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence.weightedAngularEnergy0_value
#print axioms YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence.sourceEnergy1_value
#print axioms YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence.angular_only_energy_bound_false
