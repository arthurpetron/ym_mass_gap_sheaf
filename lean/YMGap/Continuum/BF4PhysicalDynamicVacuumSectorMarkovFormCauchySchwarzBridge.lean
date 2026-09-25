/-
# Dynamic form-to-operator bridge for the completed BF4 sector

The dynamic form-gap family records the completed one-step form estimate, but
the cutoff-removed operator-norm compiler also needs the positive Markov-form
Cauchy--Schwarz law.  This module factors that law into a scale-indexed,
same-family certificate and compiles it together with the form family into the
literal completed squared-norm estimate.

No Cauchy--Schwarz family is inhabited here.  The result is a minimal honest
bridge for the next operator/power consumer; it does not create a rate band,
thermodynamic or continuum limit, or a Yang--Mills mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap

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
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel

/-! ## 1. The missing functional-analytic field -/

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

#print axioms channel_completed_norm_gap_of_formGap_and_markovCS

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge
