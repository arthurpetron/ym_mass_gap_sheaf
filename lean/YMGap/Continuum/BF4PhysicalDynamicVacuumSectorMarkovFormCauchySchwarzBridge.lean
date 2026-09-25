/-
# Dynamic form-to-operator bridge for the completed BF4 sector

The dynamic form-gap family records the completed one-step form estimate, but
the cutoff-removed operator-norm compiler also needs the positive Markov-form
Cauchy--Schwarz law.  This module factors that law into a scale-indexed,
same-family certificate and compiles it together with the form family into the
literal completed squared-norm estimate.

The canonical adaptive producer inhabits the Cauchy--Schwarz family below.
The result is a minimal honest bridge for the next operator/power consumer;
it does not create a rate band, thermodynamic or continuum limit, or a
Yang--Mills mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
import YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

/-! ## 1. The functional-analytic field -/

/-- A scale-indexed family of one-step form-gap witnesses on the same
completed carrier.  This copy deliberately lives in the bridge namespace so
the Markov-form obligation can be consumed without importing the heavier
relative-loss staging module. -/
structure DynamicVacuumSectorCompletedFormGapFamily
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  formGapAt : ∀ scale,
    CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      (family.nome_pos scale) (family.nome_lt_one scale) half

/-- A Markov-form Cauchy--Schwarz witness at every scale of one completed
family.  Its indices are the family's actual nome and completed carrier. -/
structure DynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  cauchySchwarzAt : ∀ scale,
    CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
      (family.nome_pos scale) (family.nome_lt_one scale) half

/-- The existing adaptive completed Markov-form theorem inhabits the
scale-indexed Cauchy--Schwarz family for every dynamic family.  No new
positivity or completion premise is introduced here. -/
def canonicalDynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily
    {half : Nat} (family : DynamicVacuumSectorCompletedFamily half) :
    DynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily family where
  cauchySchwarzAt := fun scale =>
    centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
      (family.nome_pos scale) (family.nome_lt_one scale) half

/-- The fixed-`w = 1/2` geometric family carries the existing completed
strict form gap at every scale. -/
def marginalHalfGeometricCompletedFormGapFamily :
    DynamicVacuumSectorCompletedFormGapFamily
      marginalHalfGeometricCompletedFamily where
  formGapAt := fun _scale =>
    completedSectorFormGap (w := HalfPow.half) (by decide) (by decide) (by decide)

@[simp] theorem marginalHalfGeometricCompletedFormGapFamily_rate (scale : Nat) :
    (marginalHalfGeometricCompletedFormGapFamily.formGapAt scale).rate =
      cutoffUniformRate HalfPow.half (by decide) := by
  rfl

/-! ## 2. Form plus Cauchy--Schwarz gives the same completed norm gap -/

/-- The two named scale-wise inputs compile to the squared-norm estimate for
the literal completed vacuum transfer on the channel's vector.  No alternate
carrier, transfer, or rate is introduced. -/
theorem channel_completed_norm_gap_of_formGap_and_markovCS
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (formFamily : DynamicVacuumSectorCompletedFormGapFamily family)
    (csFamily : DynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily
      family)
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          (family.nome_pos scale) (family.nome_lt_one scale) half
          (channel.vectorAt scale)).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          (family.nome_pos scale) (family.nome_lt_one scale) half
          (channel.vectorAt scale)).1)
      (CReal.RCscale
        ((formFamily.formGapAt scale).rate *
          (formFamily.formGapAt scale).rate)
        (channel.normSq scale)) := by
  exact centralPhysicalVacuumSectorCylinderCompletedTransfer_norm_gap
    (csFamily.cauchySchwarzAt scale)
    (formFamily.formGapAt scale)
    (channel.vectorAt scale)

/-- The same completed norm gap with the Cauchy--Schwarz input discharged by
the canonical adaptive producer. -/
theorem channel_completed_norm_gap_of_formGap
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (formFamily : DynamicVacuumSectorCompletedFormGapFamily family)
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          (family.nome_pos scale) (family.nome_lt_one scale) half
          (channel.vectorAt scale)).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          (family.nome_pos scale) (family.nome_lt_one scale) half
          (channel.vectorAt scale)).1)
      (CReal.RCscale
        ((formFamily.formGapAt scale).rate *
          (formFamily.formGapAt scale).rate)
        (channel.normSq scale)) := by
  exact channel_completed_norm_gap_of_formGap_and_markovCS
    formFamily
    (canonicalDynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily family)
    channel scale

/-- Concrete non-vacuous consequence on the literal moving-centered cube
channel: the canonical adaptive Cauchy--Schwarz producer and the inhabited
`w = 1/2` form gap give squared-norm contraction at every geometric scale. -/
theorem marginalHalfGeometricMovingCube_completed_norm_gap (scale : Nat) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner
        (marginalHalfGeometricCompletedFamily.nome_pos scale)
        (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
          ((centralPhysicalDynamicMovingCubeRCChannel
            marginalHalfGeometricCompletedFamily).vectorAt scale)).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
          ((centralPhysicalDynamicMovingCubeRCChannel
            marginalHalfGeometricCompletedFamily).vectorAt scale)).1)
      (CReal.RCscale
        ((marginalHalfGeometricCompletedFormGapFamily.formGapAt scale).rate *
          (marginalHalfGeometricCompletedFormGapFamily.formGapAt scale).rate)
        ((centralPhysicalDynamicMovingCubeRCChannel
            marginalHalfGeometricCompletedFamily).normSq scale)) := by
  exact channel_completed_norm_gap_of_formGap
    marginalHalfGeometricCompletedFormGapFamily
    (centralPhysicalDynamicMovingCubeRCChannel
      marginalHalfGeometricCompletedFamily)
    scale

#print axioms channel_completed_norm_gap_of_formGap_and_markovCS
#print axioms canonicalDynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily
#print axioms channel_completed_norm_gap_of_formGap
#print axioms marginalHalfGeometricCompletedFormGapFamily
#print axioms marginalHalfGeometricCompletedFormGapFamily_rate
#print axioms marginalHalfGeometricMovingCube_completed_norm_gap

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge
