/-
# Posterior variance to the completed vacuum-sector carrier

The matched posterior-variance route already supplies a cofinal finite strict
form gap.  This module attaches that gap directly to the actual completed
vacuum-sector transfer and its same-object autocorrelation.  It is a consumer
bridge only: the cofinal variance fraction, the matched trajectory, and every
continuum/physical calibration input remain explicit producer data.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap

namespace YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceCompletedCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath

/-! ## 1. Completed consumer -/

/-- The cofinal posterior-variance fraction, viewed as a strict contraction
certificate for the actual completed canonical vacuum-sector carrier. -/
def completedStrictContractionData_of_fraction
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat}
    (family : FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  family.toCompletedStrictContractionData hw0 hw1

/-- Every completed vacuum-complement vector inherits geometric squared-norm
decay from the posterior-variance fraction at its displayed rate. -/
theorem transferPower_norm_decay_of_fraction
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat}
    (family : FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w (Q'.le_of_lt hw0) half) (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half n vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 half n vector).1)
      (CReal.RCscale
        ((family.rate * family.rate) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector.1 vector.1)) := by
  exact centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
    (completedStrictContractionData_of_fraction hw0 hw1 family) n vector

/-- The same posterior-variance certificate controls the squared
same-object completed autocorrelation for every completed vector. -/
theorem autocorrelation_sq_decay_of_fraction
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat}
    (family : FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w (Q'.le_of_lt hw0) half) (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          hw0 hw1 half n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          hw0 hw1 half n vector.1))
      (CReal.RCmul
        (CReal.RCscale
          ((family.rate * family.rate) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            hw0 hw1 half vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half vector.1 vector.1)) := by
  exact centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
    (completedStrictContractionData_of_fraction hw0 hw1 family) n vector

end YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceCompletedCarrier

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceCompletedCarrier.completedStrictContractionData_of_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceCompletedCarrier.transferPower_norm_decay_of_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceCompletedCarrier.autocorrelation_sq_decay_of_fraction
