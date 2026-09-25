/-
# A fixed-nome dynamic-family witness for the branch obstruction

The source-independent dynamic-family interface is inhabited by the existing
fixed BF4 nome together with any explicit positive spacing schedule tending to
zero.  Every scale therefore carries the same completed physical carrier and
the same strict contraction, while the spacing is allowed to vary.  This is a
deliberate obstruction witness: it supplies the dynamic RC channel and its
nonzero zero-time response, but it does not supply a physical-rate band or a
changing-coupling same-theory family.
-/

import YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
import YMGap.Continuum.BF4WilsonBranchSheafNaturalTransformation

namespace YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
  (completedSectorContraction)
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
  (cutoffUniformRate)
open YMGap.Continuum.PhysicalSeparatorLogRate
  (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration
  (CurrentSpacingSchedule)
open YMGap.Continuum.RCStrictPositivity
  (RCIsPositive)

private theorem nome_le_half : nome ≤ HalfPow.half := by
  decide

/-- Repackage an explicit spacing schedule as the dynamic-family spacing
record.  No coupling or nome is changed. -/
def fixedCarrierSpacing (S : CurrentSpacingSchedule) : PhysicalSpacing where
  spacing := S.a
  spacing_pos := S.a_pos

/-- The schedule's modulus is exactly the `SpacingToZero` modulus consumed by
the dynamic-family interface. -/
def fixedCarrierSpacingToZero (S : CurrentSpacingSchedule) :
    SpacingToZero (fixedCarrierSpacing S) where
  modulus := S.spacingModulus
  spacing_le := S.spacingTendsToZero

/-- A non-vacuous dynamic-family witness with constant nome and constant
completed carrier, but an explicit vanishing-spacing schedule. -/
def fixedCarrierDynamicFamily (S : CurrentSpacingSchedule) :
    DynamicVacuumSectorCompletedFamily 0 where
  nome := fun _ => nome
  nome_pos := fun _ => nome_pos
  nome_lt_one := fun _ => nome_lt_one
  transferSpacing := fixedCarrierSpacing S
  transferSpacingToZero := fixedCarrierSpacingToZero S
  completedGap := fun _ =>
    completedSectorContraction nome_pos nome_lt_one nome_le_half

@[simp] theorem fixedCarrierDynamicFamily_nome
    (S : CurrentSpacingSchedule) (scale : Nat) :
    (fixedCarrierDynamicFamily S).nome scale = nome := rfl

@[simp] theorem fixedCarrierDynamicFamily_spacing
    (S : CurrentSpacingSchedule) (scale : Nat) :
    (fixedCarrierDynamicFamily S).transferSpacing.spacing scale = S.a scale := by
  change (fixedCarrierSpacing S).spacing scale = S.a scale
  rfl

@[simp] theorem fixedCarrierDynamicFamily_rate
    (S : CurrentSpacingSchedule) (scale : Nat) :
    ((fixedCarrierDynamicFamily S).completedGap scale).rate =
      cutoffUniformRate nome (Q'.le_of_lt nome_pos) := rfl

/-- The concrete moving-cube channel is available on the fixed-carrier family
at every scheduled scale. -/
def fixedCarrierMovingCubeChannel (S : CurrentSpacingSchedule) :
    DynamicVacuumSectorSameObjectRCChannel (fixedCarrierDynamicFamily S) :=
  centralPhysicalDynamicMovingCubeRCChannel (fixedCarrierDynamicFamily S)

theorem fixedCarrierMovingCube_zero_isPositive
    (S : CurrentSpacingSchedule) (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        (fixedCarrierMovingCubeChannel S) scale 0) :=
  centralPhysicalDynamicMovingCube_connected_zero_isPositive
    (fixedCarrierDynamicFamily S) scale

theorem fixedCarrierMovingCube_sampled_zero_isPositive
    (S : CurrentSpacingSchedule) (scale : Nat) :
    RCIsPositive
      (sampledConnectedAutocorrelation
        (fixedCarrierMovingCubeChannel S) scale 0) :=
  sampledConnectedAutocorrelation_zero_isPositive
    (fixedCarrierMovingCubeChannel S) scale

theorem fixedCarrierMovingCube_sampled_decay
    (S : CurrentSpacingSchedule) (scale time : Nat) :
    CReal.RCle
      (sampledConnectedAutocorrelationSq
        (fixedCarrierMovingCubeChannel S) scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((fixedCarrierDynamicFamily S).completedGap scale).rate *
              ((fixedCarrierDynamicFamily S).completedGap scale).rate) ^
            (centralPhysicalDynamicRCLatticeSteps
              (fixedCarrierDynamicFamily S) scale time))
          ((fixedCarrierMovingCubeChannel S).normSq scale))
        ((fixedCarrierMovingCubeChannel S).normSq scale)) :=
  sampledConnectedAutocorrelationSq_decay
    (fixedCarrierMovingCubeChannel S) scale time

end YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily

#print axioms YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily.fixedCarrierSpacing
#print axioms YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily.fixedCarrierSpacingToZero
#print axioms YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily.fixedCarrierDynamicFamily
#print axioms YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily.fixedCarrierMovingCubeChannel
#print axioms YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily.fixedCarrierMovingCube_zero_isPositive
#print axioms YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily.fixedCarrierMovingCube_sampled_zero_isPositive
#print axioms YMGap.Continuum.BF4WilsonFixedCarrierDynamicFamily.fixedCarrierMovingCube_sampled_decay
