/-
# The constructed finite rate reaches the completed marginal vacuum sector

Use the actual extent-one sector, not the reducible full positive-row
carrier. The explicit schedule max(request,K0(w)) supplies the previously
open cofinal finite-sector input. The existing same-object limit and
positive-form Cauchy--Schwarz then give completed form and norm bounds at
the SAME constructed q(w). No analytic certificate is assumed here.

Scope: SU(2), extent one, each 0<w<=1/2. The rate depends on w. This
marginal conditional-dynamics result does not identify geometric Euclidean
time or establish volume/spacing limits, continuum QFT, or the Clay target.
-/

import YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge

namespace YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

/-- The actual finite-sector frontier is inhabited by the proved head/tail
estimate, with an explicit cofinal schedule and no additional premise. -/
def cofinalSectorGap {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap w (Q'.le_of_lt hw0) 0
      (cutoffUniformRate w (Q'.le_of_lt hw0)) where
  rate_nonnegative := Q'.le_of_lt (cutoffUniformRate_pos w (Q'.le_of_lt hw0))
  rate_lt_one := cutoffUniformRate_lt_one w (Q'.le_of_lt hw0)
  anchor request := max request (headBoundStart w)
  anchor_ge _request := Nat.le_max_left _ _
  sectorGap _request f hcenter :=
    abs_matrix_le_cutoffUniformRate hw0 hw _ (Nat.le_max_right _ _) f hcenter

/-- Strict form data on the SAME completed marginal vacuum complement. -/
def completedSectorFormGap {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hw : w ≤ HalfPow.half) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData hw0 hw1 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictFormGapDataAtRate hw0 hw1 0
    (cofinalSectorGap hw0 hw).toVacuumSectorCenteredStrictGap

theorem completedSectorFormGap_rate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hw : w ≤ HalfPow.half) :
    (completedSectorFormGap hw0 hw1 hw).rate = cutoffUniformRate w (Q'.le_of_lt hw0) := rfl

/-- Completed norm contraction at q(w), using the already proved sharp
positive-Markov-form Cauchy--Schwarz on the actual sector. -/
def completedSectorContraction {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hw : w ≤ HalfPow.half) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData hw0 hw1 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionData_of_formGap
    (centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData hw0 hw1 0)
    (completedSectorFormGap hw0 hw1 hw)

theorem completedSectorContraction_rate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hw : w ≤ HalfPow.half) :
    (completedSectorContraction hw0 hw1 hw).rate = cutoffUniformRate w (Q'.le_of_lt hw0) := rfl

/-- Every actual conditional iterate decays on the completed marginal
vacuum complement, without a supplied gap or a vector-dependent prefactor. -/
theorem completedSector_power_decay {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hw : w ≤ HalfPow.half) (n : Nat)
    (x : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement hw0 hw1 0) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower hw0 hw1 0 n x).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower hw0 hw1 0 n x).1)
      (CReal.RCscale
        ((cutoffUniformRate w (Q'.le_of_lt hw0) * cutoffUniformRate w (Q'.le_of_lt hw0)) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0 x.1 x.1)) :=
  centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
    (completedSectorContraction hw0 hw1 hw) n x

end YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap

#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap.cofinalSectorGap
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap.completedSectorFormGap
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap.completedSectorFormGap_rate
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap.completedSectorContraction
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap.completedSectorContraction_rate
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap.completedSector_power_decay
