/-
# A changing-nome completed BF4 family

The completed marginal SU(2) contraction is available for every strict nome
at or below one half.  This file packages an explicit nonconstant nome
schedule and an independent positive spacing-to-zero schedule into the
source-independent dynamic-family interface.  It is therefore a genuine
changing completed family, unlike the fixed-carrier obstruction witness.

No physical-rate band, observable pin, OS/GNS identification, continuum
measure, or Clay conclusion is asserted here.  The schedules are explicit
constructive data, not a claim that this particular calibration is the
Yang--Mills scaling trajectory.
-/

import YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
import YMGap.Continuum.PhysicalSeparatorLinearTail

namespace YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.RCStrictPositivity

def changingNome (scale : Nat) : Q' :=
  Q'.invSucc (scale + 2)

theorem changingNome_pos (scale : Nat) :
    (0 : Q') < changingNome scale :=
  Q'.invSucc_pos _

theorem changingNome_lt_one (scale : Nat) :
    changingNome scale < (1 : Q') := by
  have hle : Q'.invSucc (scale + 2) ≤ Q'.invSucc 1 :=
    ExpNeg.invSucc_le_of_le (by omega)
  exact Q'.lt_of_le_of_lt hle (by decide)

theorem changingNome_le_half (scale : Nat) :
    changingNome scale ≤ HalfPow.half := by
  have hle : Q'.invSucc (scale + 2) ≤ Q'.invSucc 1 :=
    ExpNeg.invSucc_le_of_le (by omega)
  exact Q'.le_trans' _ _ _ hle (by decide)

theorem changingNome_nonconstant :
    changingNome 0 ≠ changingNome 1 := by
  decide

def changingSpacing : PhysicalSpacing where
  spacing := fun j => Q'.invSucc (j + 1)
  spacing_pos := fun _j => Q'.invSucc_pos _

def changingSpacingToZero : SpacingToZero changingSpacing where
  modulus := fun epsilon => epsilon.den
  spacing_le := by
    intro epsilon hepsilon j hj
    have hindex : epsilon.den ≤ j + 1 := by omega
    exact Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hindex)
      (HalfPow.invSucc_den_le epsilon hepsilon)

def changingNomeDynamicFamily : DynamicVacuumSectorCompletedFamily 0 where
  nome := changingNome
  nome_pos := changingNome_pos
  nome_lt_one := changingNome_lt_one
  transferSpacing := changingSpacing
  transferSpacingToZero := changingSpacingToZero
  completedGap := fun scale =>
    completedSectorContraction
      (changingNome_pos scale)
      (changingNome_lt_one scale)
      (changingNome_le_half scale)

theorem changingNomeDynamicFamily_rate (scale : Nat) :
    (changingNomeDynamicFamily.completedGap scale).rate =
      cutoffUniformRate (changingNome scale)
        (Q'.le_of_lt (changingNome_pos scale)) := rfl

theorem changingNomeDynamicFamily_spacing (scale : Nat) :
    changingNomeDynamicFamily.transferSpacing.spacing scale =
      Q'.invSucc (scale + 1) := rfl

theorem changingNomeDynamicFamily_nome (scale : Nat) :
    changingNomeDynamicFamily.nome scale = changingNome scale := rfl

def changingNomeFormGap (scale : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      (changingNome_pos scale) (changingNome_lt_one scale) 0 :=
  completedSectorFormGap
    (changingNome_pos scale)
    (changingNome_lt_one scale)
    (changingNome_le_half scale)

theorem changingNomeFormGap_rate (scale : Nat) :
    (changingNomeFormGap scale).rate =
      cutoffUniformRate (changingNome scale)
        (Q'.le_of_lt (changingNome_pos scale)) := rfl

theorem changingNomeFormGap_margin_positive (scale : Nat) :
    (0 : Q') < 1 - (changingNomeFormGap scale).rate :=
  one_sub_pos_of_lt_one (changingNomeFormGap scale).rate_lt_one

private theorem changingNome_deficit_lower (r : Q') (norm form : CReal.RC)
    (h : CReal.RCle form (CReal.RCscale r norm)) :
    CReal.RCle (CReal.RCscale (1 - r) norm)
      (CReal.RCsub norm form) := by
  revert h
  refine Quotient.inductionOn₂ norm form ?_
  intro N F h epsilon hepsilon
  obtain ⟨index, hN⟩ := h epsilon hepsilon
  refine ⟨index, fun n hn => ?_⟩
  have hf := hN n hn
  change F.approx n ≤ r * N.approx n + epsilon at hf
  have hneg := Q'.neg_le_neg_add hf
  have hsum := Q'.add_le_add_left (N.approx n) _ _ hneg
  change (1 - r) * N.approx n ≤
    (N.approx n + -F.approx n) + epsilon
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv 1 (-r) (N.approx n))
        (Q'.add_eqv_congr'
          (Q'.one_mul_eqv (N.approx n))
          (Q'.neg_mul_eqv r (N.approx n)))))
    (Q'.le_trans' _ _ _ hsum
      (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _)))

def changingNomeMovingCubeChannel :
    DynamicVacuumSectorSameObjectRCChannel changingNomeDynamicFamily :=
  centralPhysicalDynamicMovingCubeRCChannel changingNomeDynamicFamily

/-! ## 3a. One typed bridge for the changing completed family -/

/-- The inhabited changing-nome family and its literal moving-cube channel are
packaged with the schedule equalities that downstream physical compilers
consume.  The bridge exposes an actual completed SU(2) sector at every scale;
it does not assert the missing physical-rate band. -/
structure ChangingNomeConcreteChannelBridge : Type 1 where
  family : DynamicVacuumSectorCompletedFamily 0
  channel : DynamicVacuumSectorSameObjectRCChannel family
  nome_eq : ∀ scale, family.nome scale = changingNome scale
  spacing_eq : ∀ scale,
    family.transferSpacing.spacing scale = changingSpacing.spacing scale
  vectorAt_eq : ∀ scale,
    channel.vectorAt scale =
      centralPhysicalDynamicMovingCubeVectorAt family scale
  autocorrelation_eq : ∀ scale time,
    channel.connectedAutocorrelation scale time =
      DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        (centralPhysicalDynamicMovingCubeRCChannel family) scale time

/-- Construct the changing-nome concrete channel bridge from the existing
inhabited completed family and literal moving-cube channel. -/
def changingNomeConcreteChannelBridge : ChangingNomeConcreteChannelBridge where
  family := changingNomeDynamicFamily
  channel := changingNomeMovingCubeChannel
  nome_eq := by
    intro scale
    exact changingNomeDynamicFamily_nome scale
  spacing_eq := by
    intro scale
    exact changingNomeDynamicFamily_spacing scale
  vectorAt_eq := by
    intro scale
    rfl
  autocorrelation_eq := by
    intro scale time
    rfl

/-- The bridge retains strict zero-time positivity of the literal channel at
every changing-nome scale. -/
theorem changingNomeConcreteChannelBridge_zero_isPositive (scale : Nat) :
    RCIsPositive
      (changingNomeConcreteChannelBridge.channel.connectedAutocorrelation
        scale 0) :=
  centralPhysicalDynamicMovingCube_connected_zero_isPositive
    changingNomeConcreteChannelBridge.family scale

/-- The bridge retains the completed same-object squared decay bound at every
changing-nome scale and time. -/
theorem changingNomeConcreteChannelBridge_connectedSq_decay
    (scale time : Nat) :
    CReal.RCle
      (changingNomeConcreteChannelBridge.channel.connectedAutocorrelationSq
        scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((changingNomeConcreteChannelBridge.family.completedGap scale).rate *
              (changingNomeConcreteChannelBridge.family.completedGap scale).rate)) ^ time)
          (changingNomeConcreteChannelBridge.channel.normSq scale))
        (changingNomeConcreteChannelBridge.channel.normSq scale)) :=
  centralPhysicalDynamicMovingCube_connectedSq_decay
    changingNomeConcreteChannelBridge.family scale time

theorem changingNomeMovingCube_relative_loss (scale : Nat) :
    CReal.RCle
      (CReal.RCscale
        (1 - (changingNomeFormGap scale).rate)
        (DynamicVacuumSectorSameObjectRCChannel.normSq
          changingNomeMovingCubeChannel scale))
      (CReal.RCsub
        (DynamicVacuumSectorSameObjectRCChannel.normSq
          changingNomeMovingCubeChannel scale)
        (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
          changingNomeMovingCubeChannel scale 1)) := by
  exact changingNome_deficit_lower
    (changingNomeFormGap scale).rate
    (DynamicVacuumSectorSameObjectRCChannel.normSq
      changingNomeMovingCubeChannel scale)
    (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
      changingNomeMovingCubeChannel scale 1)
    (by
      simpa only [DynamicVacuumSectorSameObjectRCChannel.normSq,
        DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation,
        centralPhysicalVacuumSectorCylinderCompletedAutocorrelation,
        centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower] using
        (changingNomeFormGap scale).form_gap
        (changingNomeMovingCubeChannel.vectorAt scale))

theorem changingNomeMovingCube_relative_loss_global (scale : Nat) :
    CReal.RCle
      (CReal.RCscale
        (1 - (changingNomeFormGap scale).rate)
        (DynamicVacuumSectorSameObjectRCChannel.normSq
          changingNomeMovingCubeChannel scale))
      (CReal.RCsub
        (DynamicVacuumSectorSameObjectRCChannel.normSq
          changingNomeMovingCubeChannel scale)
        (centralPhysicalCutoffCompletedInner
          (changingNomeDynamicFamily.nome_pos scale)
          (changingNomeDynamicFamily.nome_lt_one scale) 0
          (centralPhysicalConcreteAdaptiveCompletedMarkovPower
            (changingNomeDynamicFamily.nome_pos scale)
            (changingNomeDynamicFamily.nome_lt_one scale) 0 1
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              (changingNomeMovingCubeChannel.vectorAt scale).1))
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (changingNomeMovingCubeChannel.vectorAt scale).1))) := by
  simpa only [DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_eq_global] using
    changingNomeMovingCube_relative_loss scale

theorem changingNomeMovingCube_zero_isPositive (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        changingNomeMovingCubeChannel scale 0) :=
  centralPhysicalDynamicMovingCube_connected_zero_isPositive
    changingNomeDynamicFamily scale

theorem changingNomeMovingCube_connectedSq_decay (scale time : Nat) :
    CReal.RCle
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq
        changingNomeMovingCubeChannel scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((changingNomeDynamicFamily.completedGap scale).rate *
              (changingNomeDynamicFamily.completedGap scale).rate)) ^ time)
          ((changingNomeMovingCubeChannel).normSq scale))
        ((changingNomeMovingCubeChannel).normSq scale)) :=
  centralPhysicalDynamicMovingCube_connectedSq_decay
    changingNomeDynamicFamily scale time

#print axioms changingNome
#print axioms changingNome_pos
#print axioms changingNome_lt_one
#print axioms changingNome_le_half
#print axioms changingNome_nonconstant
#print axioms changingSpacing
#print axioms changingSpacingToZero
#print axioms changingNomeDynamicFamily
#print axioms changingNomeDynamicFamily_rate
#print axioms changingNomeDynamicFamily_spacing
#print axioms changingNomeDynamicFamily_nome
#print axioms changingNomeFormGap
#print axioms changingNomeFormGap_rate
#print axioms changingNomeFormGap_margin_positive
#print axioms changingNomeMovingCube_relative_loss
#print axioms changingNomeMovingCube_relative_loss_global
#print axioms changingNomeMovingCubeChannel
#print axioms changingNomeConcreteChannelBridge
#print axioms changingNomeConcreteChannelBridge_zero_isPositive
#print axioms changingNomeConcreteChannelBridge_connectedSq_decay
#print axioms changingNomeMovingCube_zero_isPositive
#print axioms changingNomeMovingCube_connectedSq_decay

end YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
