/-
# Dynamic form-gap certificate and relative loss

The source-independent dynamic family stores completed squared-norm
contraction.  A relative-loss bridge needs the stronger one-step form gap, so
this file factors that missing input into a separate family certificate.  The
fixed-`w = 1/2` geometric staging family inhabits the certificate using its
existing finite marginal form gap.  The literal moving-centered cube channel
then receives a same-object relative-loss inequality at every scale.

The attached spacing still tends to zero while the lattice margin stays
constant; this is therefore a staging result, not a physical-rate band or a
continuum Yang--Mills theorem.
-/

import YMGap.Continuum.BF4PhysicalConcreteSU2RelativeLoss
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFormGapRelativeLoss

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalConcreteSU2RelativeLoss
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

/-! ## 1. Minimal form-level family certificate -/

structure DynamicVacuumSectorCompletedFormGapFamily
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  formGapAt : ∀ scale,
    CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      (family.nome_pos scale) (family.nome_lt_one scale) half

def marginalHalfGeometricCompletedFormGapFamily :
    DynamicVacuumSectorCompletedFormGapFamily
      marginalHalfGeometricCompletedFamily where
  formGapAt := fun _scale => completedSectorFormGap
    (w := HalfPow.half) (by decide) (by decide) (by decide)

theorem marginalHalfGeometricCompletedFormGapFamily_rate (scale : Nat) :
    (marginalHalfGeometricCompletedFormGapFamily.formGapAt scale).rate =
      cutoffUniformRate HalfPow.half (by decide) := by
  rfl

/-! ## 2. Relative loss on any channel selected by the form family -/

theorem channel_relative_loss_of_formGapFamily
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (formFamily : DynamicVacuumSectorCompletedFormGapFamily family)
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    CReal.RCle
      (CReal.RCscale
        (1 - (formFamily.formGapAt scale).rate)
        (channel.normSq scale))
      (CReal.RCsub
        (channel.normSq scale)
        (channel.connectedAutocorrelation scale 1)) := by
  exact sector_relative_loss_of_form_gap
    (formFamily.formGapAt scale) (channel.vectorAt scale)

theorem channel_relative_loss_margin_positive_of_formGapFamily
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (formFamily : DynamicVacuumSectorCompletedFormGapFamily family)
    (scale : Nat) :
    (0 : Q') < 1 - (formFamily.formGapAt scale).rate :=
  HKPos.one_sub_pos (formFamily.formGapAt scale).rate_lt_one

/-! ## 3. The concrete moving-cube staging instance -/

theorem marginalHalfGeometricCompletedFamily_movingCube_relative_loss
    (scale : Nat) :
    CReal.RCle
      (CReal.RCscale
        (1 -
          (marginalHalfGeometricCompletedFormGapFamily.formGapAt scale).rate)
        ((centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily).normSq scale))
      (CReal.RCsub
        ((centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily).normSq scale)
        ((centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily).connectedAutocorrelation
          scale 1)) := by
  exact channel_relative_loss_of_formGapFamily
    marginalHalfGeometricCompletedFormGapFamily
    (centralPhysicalDynamicMovingCubeRCChannel
      marginalHalfGeometricCompletedFamily) scale

theorem marginalHalfGeometricCompletedFamily_movingCube_margin_positive
    (scale : Nat) :
    (0 : Q') < 1 -
      (marginalHalfGeometricCompletedFormGapFamily.formGapAt scale).rate :=
  channel_relative_loss_margin_positive_of_formGapFamily
    marginalHalfGeometricCompletedFormGapFamily scale

#print axioms marginalHalfGeometricCompletedFormGapFamily
#print axioms channel_relative_loss_of_formGapFamily
#print axioms marginalHalfGeometricCompletedFamily_movingCube_relative_loss
#print axioms marginalHalfGeometricCompletedFamily_movingCube_margin_positive

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFormGapRelativeLoss
