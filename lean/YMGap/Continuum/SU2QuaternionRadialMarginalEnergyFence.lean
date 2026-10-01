/-
# Radial-marginal source-energy fence on the original one-link heat law

At nome one half and cutoff three, a certified positive source gives an
exact counterexample to the proposed universal coefficient-three radial
replacement. The radial moment is taken in the SAME `q * P q` marginal as
the energy. This says nothing about the special terminal source of the
interacting Yang--Mills slab, nor about a scaling limit.

The concrete cutoff-three heat factor already has a positive polynomial
certificate in `SU2QuaternionHalfHeatThreeCertificate`.
-/

import YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence
import YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate

namespace YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv

/-- Same rational nome as the independently certified positive K=3 kernel. -/
def half : Q' := YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate.half

/-- The fundamental character on the original one-block carrier. -/
def fundamental : RatPoly :=
  characterPolynomial (PolyQuaternion.coordinateVariable 0).scalar 1

def fourth : RatPoly :=
  let square := polyMul fundamental fundamental
  polyMul square square

/-- `1 + fundamental^8`, exhibited as one plus a polynomial square. -/
def positiveSource : RatPoly := polyAdd polyOne (polyMul fourth fourth)

/-- The literal radial insertion `4 - fundamental^2`. -/
def radialTest : RatPoly :=
  polyAdd (polySmul 4 polyOne) (polyNeg (polyMul fundamental fundamental))

def mass1 : Q' := sourceMoment 1 half 3 [0] positiveSource polyOne
def secondMoment1 : Q' :=
  sourceMoment 1 half 3 [0] positiveSource (polyMul fundamental fundamental)
def radialMoment1 : Q' := sourceMoment 1 half 3 [0] positiveSource radialTest
def sourceEnergy1 : Q' := sourceEnergy 1 half 3 [0] positiveSource fundamental

theorem fundamental_supported : SupportedQuaternionBlocks 1 fundamental :=
  character_supported (coordinate_supported (by omega : 0 < 1) (0 : Fin 4)) 1

theorem fourth_supported : SupportedQuaternionBlocks 1 fourth :=
  supported_polyMul
    (supported_polyMul fundamental_supported fundamental_supported)
    (supported_polyMul fundamental_supported fundamental_supported)

theorem positiveSource_supported : SupportedQuaternionBlocks 1 positiveSource :=
  supported_add (supported_one 1) (supported_polyMul fourth_supported fourth_supported)

/-- Constructive positivity of the complete source, with a strict unit
summand. No pointwise sign assumption is added. -/
def positiveSourceCertificate : Certificate 1 positiveSource :=
  .add (Certificate.one 1) (.square fourth fourth_supported)

/-- The exact K=3 kernel is already certified strictly above one quarter. -/
def kernelQuarterFloor : Certificate 2
    (polyAdd (heatAt 0 1 half 3)
      (polyNeg (cap (Q'.mkPos 1 4 (by decide))))) :=
  YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate.heatAt_half_three_quarterFloor

theorem cutoff_guard : sufficientCutoff half ≤ 3 := by decide

set_option maxRecDepth 16384 in
theorem mass1_value : mass1 ≈ Q'.mkPos 3649 16 (by decide) := by decide

set_option maxRecDepth 16384 in
theorem secondMoment1_value : secondMoment1 ≈ Q'.mkPos 41917 64 (by decide) := by decide

set_option maxRecDepth 16384 in
theorem radialMoment1_value : radialMoment1 ≈ Q'.mkPos 16467 64 (by decide) := by decide

set_option maxRecDepth 16384 in
theorem sourceEnergy1_value : sourceEnergy1 ≈ Q'.mkPos 54241 128 (by decide) := by decide

/-- The proposed coefficient three fails in the original one-link marginal.
The exact positive gap is `605/16`. This does not refute a larger finite
coefficient or any statement restricted to the actual terminal source. -/
theorem radial_marginal_bound_three_false :
    ¬ (sourceEnergy1 ≤
      (3 : Q') * ((1 : Q') - half) * radialMoment1) := by
  intro h
  have hle : Q'.mkPos 54241 128 (by decide) ≤
      (3 : Q') * ((1 : Q') - half) * Q'.mkPos 16467 64 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm sourceEnergy1_value))
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ radialMoment1_value)))
  exact (by decide : ¬ (Q'.mkPos 54241 128 (by decide) ≤
    (3 : Q') * ((1 : Q') - half) * Q'.mkPos 16467 64 (by decide))) hle

end YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence

#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.fundamental_supported
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.fourth_supported
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.positiveSource_supported
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.positiveSourceCertificate
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.kernelQuarterFloor
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.cutoff_guard
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.mass1_value
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.secondMoment1_value
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.radialMoment1_value
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.sourceEnergy1_value
#print axioms YMGap.Continuum.SU2QuaternionRadialMarginalEnergyFence.radial_marginal_bound_three_false
