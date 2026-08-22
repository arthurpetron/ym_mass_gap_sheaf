/-
# The six-element spatial S3 action on the cutoff-two physical sector

The adjacent swaps `(01)` and `(12)` are packaged into six normal words.  An
explicit multiplication table, finite action-composition check, and inverse
laws verify the `S3` presentation on the literal 65-state sector.  The two
generator kernel equalities then compose to simultaneous physical-kernel
invariance under every normal word.

This is a finite cutoff-two symmetry theorem.  Orbit representatives and the
remaining physical/raw trace comparisons are constructed in later modules.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private def axisSwap12SectorTargetIndex (sourceIndex : Fin 65) : Fin 65 :=
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.axisSwap12SectorTargetIndex
    sourceIndex

/-- Six normal words for the unsigned permutations of three spatial axes. -/
inductive CutoffTwoSpatialS3 : Type
  | identity
  | swap01
  | swap12
  | swap12_swap01
  | swap01_swap12
  | swap01_swap12_swap01
  deriving DecidableEq, Repr

def cutoffTwoSpatialS3Elements : List CutoffTwoSpatialS3 :=
  [.identity, .swap01, .swap12, .swap12_swap01,
    .swap01_swap12, .swap01_swap12_swap01]

theorem cutoffTwoSpatialS3Elements_nodup :
    cutoffTwoSpatialS3Elements.Nodup := by
  decide

theorem mem_cutoffTwoSpatialS3Elements (action : CutoffTwoSpatialS3) :
    action ∈ cutoffTwoSpatialS3Elements := by
  cases action <;> simp [cutoffTwoSpatialS3Elements]

/-- Literal action of a normal word on the exact 65-state sector order. -/
def cutoffTwoSpatialS3Action : CutoffTwoSpatialS3 → Fin 65 → Fin 65
  | .identity, index => index
  | .swap01, index => axisSwap01SectorTargetIndex index
  | .swap12, index => axisSwap12SectorTargetIndex index
  | .swap12_swap01, index =>
      axisSwap12SectorTargetIndex (axisSwap01SectorTargetIndex index)
  | .swap01_swap12, index =>
      axisSwap01SectorTargetIndex (axisSwap12SectorTargetIndex index)
  | .swap01_swap12_swap01, index =>
      axisSwap01SectorTargetIndex
        (axisSwap12SectorTargetIndex (axisSwap01SectorTargetIndex index))

/-- Multiplication is `outer` after `inner`, matching function composition. -/
def cutoffTwoSpatialS3Compose :
    CutoffTwoSpatialS3 → CutoffTwoSpatialS3 → CutoffTwoSpatialS3
  | .identity, inner => inner
  | .swap01, .identity => .swap01
  | .swap01, .swap01 => .identity
  | .swap01, .swap12 => .swap01_swap12
  | .swap01, .swap12_swap01 => .swap01_swap12_swap01
  | .swap01, .swap01_swap12 => .swap12
  | .swap01, .swap01_swap12_swap01 => .swap12_swap01
  | .swap12, .identity => .swap12
  | .swap12, .swap01 => .swap12_swap01
  | .swap12, .swap12 => .identity
  | .swap12, .swap12_swap01 => .swap01
  | .swap12, .swap01_swap12 => .swap01_swap12_swap01
  | .swap12, .swap01_swap12_swap01 => .swap01_swap12
  | .swap12_swap01, .identity => .swap12_swap01
  | .swap12_swap01, .swap01 => .swap12
  | .swap12_swap01, .swap12 => .swap01_swap12_swap01
  | .swap12_swap01, .swap12_swap01 => .swap01_swap12
  | .swap12_swap01, .swap01_swap12 => .identity
  | .swap12_swap01, .swap01_swap12_swap01 => .swap01
  | .swap01_swap12, .identity => .swap01_swap12
  | .swap01_swap12, .swap01 => .swap01_swap12_swap01
  | .swap01_swap12, .swap12 => .swap01
  | .swap01_swap12, .swap12_swap01 => .identity
  | .swap01_swap12, .swap01_swap12 => .swap12_swap01
  | .swap01_swap12, .swap01_swap12_swap01 => .swap12
  | .swap01_swap12_swap01, .identity => .swap01_swap12_swap01
  | .swap01_swap12_swap01, .swap01 => .swap01_swap12
  | .swap01_swap12_swap01, .swap12 => .swap12_swap01
  | .swap01_swap12_swap01, .swap12_swap01 => .swap12
  | .swap01_swap12_swap01, .swap01_swap12 => .swap01
  | .swap01_swap12_swap01, .swap01_swap12_swap01 => .identity

def cutoffTwoSpatialS3Inverse : CutoffTwoSpatialS3 → CutoffTwoSpatialS3
  | .identity => .identity
  | .swap01 => .swap01
  | .swap12 => .swap12
  | .swap12_swap01 => .swap01_swap12
  | .swap01_swap12 => .swap12_swap01
  | .swap01_swap12_swap01 => .swap01_swap12_swap01

theorem cutoffTwoSpatialS3Compose_assoc
    (first second third : CutoffTwoSpatialS3) :
    cutoffTwoSpatialS3Compose first
        (cutoffTwoSpatialS3Compose second third) =
      cutoffTwoSpatialS3Compose
        (cutoffTwoSpatialS3Compose first second) third := by
  cases first <;> cases second <;> cases third <;> rfl

theorem cutoffTwoSpatialS3Compose_identity_left
    (action : CutoffTwoSpatialS3) :
    cutoffTwoSpatialS3Compose .identity action = action := by
  rfl

theorem cutoffTwoSpatialS3Compose_identity_right
    (action : CutoffTwoSpatialS3) :
    cutoffTwoSpatialS3Compose action .identity = action := by
  cases action <;> rfl

theorem cutoffTwoSpatialS3Compose_inverse_left
    (action : CutoffTwoSpatialS3) :
    cutoffTwoSpatialS3Compose (cutoffTwoSpatialS3Inverse action) action =
      .identity := by
  cases action <;> rfl

theorem cutoffTwoSpatialS3Compose_inverse_right
    (action : CutoffTwoSpatialS3) :
    cutoffTwoSpatialS3Compose action (cutoffTwoSpatialS3Inverse action) =
      .identity := by
  cases action <;> rfl

def cutoffTwoSpatialS3ActionCompositionCheck : Bool :=
  cutoffTwoSpatialS3Elements.all fun outer =>
    cutoffTwoSpatialS3Elements.all fun inner =>
      (List.finRange 65).all fun index =>
        decide
          (cutoffTwoSpatialS3Action
              (cutoffTwoSpatialS3Compose outer inner) index =
            cutoffTwoSpatialS3Action outer
              (cutoffTwoSpatialS3Action inner index))

theorem cutoffTwoSpatialS3ActionCompositionCheck_true :
    cutoffTwoSpatialS3ActionCompositionCheck = true := by
  unfold cutoffTwoSpatialS3ActionCompositionCheck
    cutoffTwoSpatialS3Elements cutoffTwoSpatialS3Compose
    cutoffTwoSpatialS3Action axisSwap12SectorTargetIndex
  decide

theorem cutoffTwoSpatialS3Action_compose
    (outer inner : CutoffTwoSpatialS3) (index : Fin 65) :
    cutoffTwoSpatialS3Action
        (cutoffTwoSpatialS3Compose outer inner) index =
      cutoffTwoSpatialS3Action outer
        (cutoffTwoSpatialS3Action inner index) := by
  have houter := List.all_eq_true.mp
    cutoffTwoSpatialS3ActionCompositionCheck_true outer
      (mem_cutoffTwoSpatialS3Elements outer)
  have hinner := List.all_eq_true.mp houter inner
    (mem_cutoffTwoSpatialS3Elements inner)
  have hindex := List.all_eq_true.mp hinner index
    (List.mem_finRange index)
  exact of_decide_eq_true hindex

/-- Every one of the six normal words preserves the genuine production
physical kernel when applied simultaneously to both sector arguments. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_spatialS3_eqv
    (action : CutoffTwoSpatialS3) (left right : Fin 65) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt left)
        (cutoffTwoSectorStateAt right) ≈
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt (cutoffTwoSpatialS3Action action left))
        (cutoffTwoSectorStateAt
          (cutoffTwoSpatialS3Action action right)) := by
  cases action with
  | identity => exact Q'.eqv_refl _
  | swap01 =>
      exact centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv left right
  | swap12 =>
      exact centralPhysicalReflectedKernel_cutoffTwo_axisSwap12_eqv left right
  | swap12_swap01 =>
      exact Q'.eqv_trans _ _ _
        (centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv left right)
        (centralPhysicalReflectedKernel_cutoffTwo_axisSwap12_eqv
          (axisSwap01SectorTargetIndex left)
          (axisSwap01SectorTargetIndex right))
  | swap01_swap12 =>
      exact Q'.eqv_trans _ _ _
        (centralPhysicalReflectedKernel_cutoffTwo_axisSwap12_eqv left right)
        (centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv
          (axisSwap12SectorTargetIndex left)
          (axisSwap12SectorTargetIndex right))
  | swap01_swap12_swap01 =>
      exact Q'.eqv_trans _ _ _
        (centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv left right)
        (Q'.eqv_trans _ _ _
          (centralPhysicalReflectedKernel_cutoffTwo_axisSwap12_eqv
            (axisSwap01SectorTargetIndex left)
            (axisSwap01SectorTargetIndex right))
          (centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv
            (axisSwap12SectorTargetIndex
              (axisSwap01SectorTargetIndex left))
            (axisSwap12SectorTargetIndex
              (axisSwap01SectorTargetIndex right))))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction.cutoffTwoSpatialS3Action_compose
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction.centralPhysicalReflectedKernel_cutoffTwo_spatialS3_eqv
