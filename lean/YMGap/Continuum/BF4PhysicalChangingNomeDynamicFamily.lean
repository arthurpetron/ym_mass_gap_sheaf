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

def changingNomeMovingCubeChannel :
    DynamicVacuumSectorSameObjectRCChannel changingNomeDynamicFamily :=
  centralPhysicalDynamicMovingCubeRCChannel changingNomeDynamicFamily

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
#print axioms changingNomeMovingCubeChannel
#print axioms changingNomeMovingCube_zero_isPositive
#print axioms changingNomeMovingCube_connectedSq_decay

end YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
