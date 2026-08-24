/-
# A genuine RC-valued same-object channel through the dynamic BF4 family

The existing dynamic observable pin asks that completed norm squares and
squared autocorrelations be exactly embedded rationals.  The constructed
completed BF4 moments are genuine constructive reals, so that rationality
cannot be assumed merely to enter the downstream `PhysicalSeparator`
interface.

This file introduces the honest intermediate compiler.  A
`DynamicVacuumSectorSameObjectRCChannel` selects one vector in the actual
completed vacuum complement at every scale and retains an explicit positive
rational lower floor for its literal completed norm.  Its norm, connected
autocorrelation, and squared connected autocorrelation are definitions, not
independently supplied numerical data.  Consequently the dynamic completed
contraction applies directly, and the existing moment bridge identifies the
same quantity with the global adaptive-transfer matrix coefficient.

The cutoff-one moving-centered cube construction inhabits this channel for
every supplied `DynamicVacuumSectorCompletedFamily 0`.  This does not inhabit
such a dynamic family, prove that the RC moments are rational, produce a
physical rate band, construct a projective continuum limit, or claim the Clay
theorem.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.RCStrictPositivity

/-! ## 1. The same-object RC channel -/

/-- A scale-indexed non-vacuous channel in the actual completed BF4 vacuum
sector.  The rational norm floor is retained as Type-level data because later
compilers consume both its value and positivity proof.  Moments themselves
are deliberately not postulated as rational. -/
structure DynamicVacuumSectorSameObjectRCChannel
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  vectorAt : (scale : Nat) ->
    CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (family.nome_pos scale) (family.nome_lt_one scale) half
  normFloor : Nat -> Q'
  normFloor_pos : forall scale, (0 : Q') < normFloor scale
  normFloor_le : forall scale,
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' (normFloor scale)))
      (centralPhysicalVacuumSectorCylinderCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) half
        (vectorAt scale).1 (vectorAt scale).1)

namespace DynamicVacuumSectorSameObjectRCChannel

/-- The literal completed norm square of the selected vector. -/
def normSq
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) : CReal.RC :=
  centralPhysicalVacuumSectorCylinderCompletedInner
    (family.nome_pos scale) (family.nome_lt_one scale) half
    (channel.vectorAt scale).1 (channel.vectorAt scale).1

/-- The literal connected same-object autocorrelation.  It is connected
because `vectorAt` lives in the actual completed vacuum complement. -/
def connectedAutocorrelation
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) : CReal.RC :=
  centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
    (family.nome_pos scale) (family.nome_lt_one scale) half time
    (channel.vectorAt scale).1

/-- Squared connected autocorrelation in genuine completed-real currency. -/
def connectedAutocorrelationSq
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) : CReal.RC :=
  CReal.RCmul
    (channel.connectedAutocorrelation scale time)
    (channel.connectedAutocorrelation scale time)

/-- The retained Type-level rational floor bounds the literal norm square. -/
theorem normFloor_le_normSq
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (channel.normFloor scale)))
      (channel.normSq scale) :=
  channel.normFloor_le scale

/-- At time zero, no observable or vector changes: the connected
autocorrelation is definitionally the same completed norm square. -/
theorem connectedAutocorrelation_zero_eq_normSq
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    channel.connectedAutocorrelation scale 0 = channel.normSq scale := rfl

/-- The literal zero-time connected channel is strictly positive with the
same explicit rational witness carried by the channel. -/
theorem connectedAutocorrelation_zero_isPositive
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale : Nat) :
    RCIsPositive (channel.connectedAutocorrelation scale 0) := by
  rw [channel.connectedAutocorrelation_zero_eq_normSq scale]
  exact ⟨channel.normFloor scale, channel.normFloor_pos scale,
    channel.normFloor_le_normSq scale⟩

/-- The RC-valued squared connected autocorrelation is controlled by the
actual completed contraction rate of the definitionally same transfer. -/
theorem connectedAutocorrelationSq_decay
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) :
    CReal.RCle
      (channel.connectedAutocorrelationSq scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((family.completedGap scale).rate *
              (family.completedGap scale).rate)) ^ time)
          (channel.normSq scale))
        (channel.normSq scale)) :=
  family.completedAutocorrelation_sq_decay
    scale time (channel.vectorAt scale)

/-- The channel's completed autocorrelation is exactly the global physical
adaptive-transfer matrix coefficient of the same embedded vector. -/
theorem connectedAutocorrelation_eq_global
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (scale time : Nat) :
    channel.connectedAutocorrelation scale time =
      centralPhysicalCutoffCompletedInner
        (family.nome_pos scale) (family.nome_lt_one scale) half
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (family.nome_pos scale) (family.nome_lt_one scale) half time
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (channel.vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (channel.vectorAt scale).1) :=
  centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_eq_global
    (family.nome_pos scale) (family.nome_lt_one scale) half time
      (channel.vectorAt scale).1

end DynamicVacuumSectorSameObjectRCChannel

/-! ## 2. The concrete moving cube channel -/

/-- At every scale, the exact moving-centered cutoff-one cube vector in the
actual completed vacuum complement of that scale's nome. -/
def centralPhysicalDynamicMovingCubeVectorAt
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      (family.nome_pos scale) (family.nome_lt_one scale) 0 :=
  ⟨centralPhysicalVacuumSectorMovingCenteredCompletion
      (family.nome_pos scale) (family.nome_lt_one scale) 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient
        (family.nome scale) (family.nome_pos scale)),
    centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal
      (family.nome_pos scale) (family.nome_lt_one scale) 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient
        (family.nome scale) (family.nome_pos scale))⟩

/-- The moving-centered cutoff-one cube construction forms a concrete
same-object RC channel through every supplied dynamic completed family. -/
def centralPhysicalDynamicMovingCubeRCChannel
    (family : DynamicVacuumSectorCompletedFamily 0) :
    DynamicVacuumSectorSameObjectRCChannel family where
  vectorAt := centralPhysicalDynamicMovingCubeVectorAt family
  normFloor := fun scale =>
    centralPhysicalVacuumSectorCoordinateFloor
      (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) 1 0
  normFloor_pos := fun scale =>
    centralPhysicalVacuumSectorCoordinateFloor_pos
      (family.nome scale) (Q'.le_of_lt (family.nome_pos scale)) 1 0
  normFloor_le := fun scale =>
    centralPhysicalCutoffOneCubeMovingCentered_floor_le_completedInner
      (family.nome_pos scale) (family.nome_lt_one scale)

/-- The concrete moving cube channel has a strictly positive literal
zero-time connected autocorrelation at every dynamic scale. -/
theorem centralPhysicalDynamicMovingCube_connected_zero_isPositive
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    RCIsPositive
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
        (centralPhysicalDynamicMovingCubeRCChannel family) scale 0) :=
  DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_zero_isPositive
      (centralPhysicalDynamicMovingCubeRCChannel family) scale

/-- The concrete moving cube's literal squared connected autocorrelation
inherits the actual completed rate at every scale and time. -/
theorem centralPhysicalDynamicMovingCube_connectedSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) :
    CReal.RCle
      (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq
        (centralPhysicalDynamicMovingCubeRCChannel family) scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((family.completedGap scale).rate *
              (family.completedGap scale).rate)) ^ time)
          ((centralPhysicalDynamicMovingCubeRCChannel family).normSq scale))
        ((centralPhysicalDynamicMovingCubeRCChannel family).normSq scale)) :=
  DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq_decay
    (centralPhysicalDynamicMovingCubeRCChannel family) scale time

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.centralPhysicalDynamicMovingCubeRCChannel
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.centralPhysicalDynamicMovingCube_connectedSq_decay
