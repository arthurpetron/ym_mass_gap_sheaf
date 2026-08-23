/-
# Positive old/new Dirichlet blocks on the full growing sector

The signed reflected quadratic is awkward under an old/new split because its
cross blocks may help rather than hurt a centered gap.  The equivalent
Dirichlet energy has a better causal decomposition: its old-old, old-new,
new-old, and new-new edge blocks are all nonnegative.

This module proves the generic four-block identity for directed finite
Dirichlet energy, specializes it to the physical cutoff-two embedding, and
shows that both the within-block and cross-block energies are nonnegative and
bounded by the full energy.  The full energy remains exactly twice the
physical diagonal-minus-transfer deficit.

These facts expose the next honest frontier as a recursive Poincare/gluing
estimate in which cross edges contribute coercivity.  No such uniform gluing
estimate, completed gap inhabitant, thermodynamic/continuum limit, or Clay
conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic four-block Dirichlet decomposition -/

/-- A rectangular directed block of finite Dirichlet edge energy. -/
def finiteJointDirichletBlock {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (joint : State → State → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right =>
        joint left right *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)))
      rightStates)
    leftStates

/-- Filtering both endpoints gives the exact four directed edge blocks. -/
theorem finiteJointDirichletEnergy_filter_four_blocks
    {State : Type}
    (states : List State) (test : State → Bool)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletEnergy states coefficient joint ≈
      (finiteJointDirichletBlock
          (states.filter test) (states.filter test)
          coefficient joint +
        finiteJointDirichletBlock
          (states.filter test) (states.filter (fun state => !(test state)))
          coefficient joint) +
      (finiteJointDirichletBlock
          (states.filter (fun state => !(test state))) (states.filter test)
          coefficient joint +
        finiteJointDirichletBlock
          (states.filter (fun state => !(test state)))
          (states.filter (fun state => !(test state)))
          coefficient joint) := by
  let entry := fun left right =>
    joint left right *
      ((coefficient left + -coefficient right) *
        (coefficient left + -coefficient right))
  let row := fun left => listQSum (entry left) states
  have houter := listQSum_filter_partition row test states
  have hold :
      listQSum row (states.filter test) ≈
        finiteJointDirichletBlock
            (states.filter test) (states.filter test)
            coefficient joint +
          finiteJointDirichletBlock
            (states.filter test)
            (states.filter (fun state => !(test state)))
            coefficient joint := by
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum (entry left) (states.filter test) +
            listQSum (entry left)
              (states.filter (fun state => !(test state))))
        (states.filter test)) _ ?_ ?_
    · apply listQSum_congr_on
      intro left _hleft
      exact listQSum_filter_partition (entry left) test states
    · unfold finiteJointDirichletBlock
      exact listQSum_add _ _ _
  have hnew :
      listQSum row (states.filter (fun state => !(test state))) ≈
        finiteJointDirichletBlock
            (states.filter (fun state => !(test state)))
            (states.filter test) coefficient joint +
          finiteJointDirichletBlock
            (states.filter (fun state => !(test state)))
            (states.filter (fun state => !(test state)))
            coefficient joint := by
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum (entry left) (states.filter test) +
            listQSum (entry left)
              (states.filter (fun state => !(test state))))
        (states.filter (fun state => !(test state)))) _ ?_ ?_
    · apply listQSum_congr_on
      intro left _hleft
      exact listQSum_filter_partition (entry left) test states
    · unfold finiteJointDirichletBlock
      exact listQSum_add _ _ _
  unfold finiteJointDirichletEnergy
  exact Q'.eqv_trans _ _ _ houter
    (Q'.add_eqv_congr' hold hnew)

theorem finiteJointDirichletBlock_nonnegative
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q') (joint : State → State → Q')
    (hjoint : ∀ left right, (0 : Q') ≤ joint left right) :
    (0 : Q') ≤ finiteJointDirichletBlock
      leftStates rightStates coefficient joint := by
  unfold finiteJointDirichletBlock
  apply listQSum_nonnegative_on
  intro left _hleft
  apply listQSum_nonnegative_on
  intro right _hright
  exact Q'.mul_nonneg _ _ (hjoint left right)
    (SumOfSquares.q_mul_self_nonneg
      (coefficient left + -coefficient right))

/-! ## 2. Physical cutoff-two old/new energy blocks -/

def cutoffTwoFullSectorDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoOldOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoOldNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoNewOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoNewNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoWithinBlockDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoOldOldDirichlet later coefficient +
    cutoffTwoNewNewDirichlet later coefficient

def cutoffTwoCrossBlockDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoOldNewDirichlet later coefficient +
    cutoffTwoNewOldDirichlet later coefficient

/-- Exact four-block partition of the physical full-sector energy. -/
theorem cutoffTwoFullSectorDirichlet_four_blocks
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorDirichlet later coefficient ≈
      (cutoffTwoOldOldDirichlet later coefficient +
        cutoffTwoOldNewDirichlet later coefficient) +
      (cutoffTwoNewOldDirichlet later coefficient +
        cutoffTwoNewNewDirichlet later coefficient) := by
  unfold cutoffTwoFullSectorDirichlet
    cutoffTwoOldOldDirichlet cutoffTwoOldNewDirichlet
    cutoffTwoNewOldDirichlet cutoffTwoNewNewDirichlet
    centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteVacuumSectorNewBlockIndices
  exact finiteJointDirichletEnergy_filter_four_blocks
    (centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0)
    (centralPhysicalFiniteEmbeddedVacuumSectorB
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

private theorem four_term_within_cross_reshuffle
    (oldOld oldNew newOld newNew : Q') :
    (oldOld + oldNew) + (newOld + newNew) ≈
      (oldOld + newNew) + (oldNew + newOld) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv oldOld oldNew (newOld + newNew)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left oldOld _ _
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv oldNew newOld newNew))
        (Q'.add_comm_eqv (oldNew + newOld) newNew))) ?_
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv oldOld newNew (oldNew + newOld))

/-- The same partition grouped causally into within-block and cross-block
positive energies. -/
theorem cutoffTwoFullSectorDirichlet_eqv_within_add_cross
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorDirichlet later coefficient ≈
      cutoffTwoWithinBlockDirichlet later coefficient +
        cutoffTwoCrossBlockDirichlet later coefficient := by
  refine Q'.eqv_trans _ _ _
    (cutoffTwoFullSectorDirichlet_four_blocks later coefficient) ?_
  unfold cutoffTwoWithinBlockDirichlet cutoffTwoCrossBlockDirichlet
  exact four_term_within_cross_reshuffle
    (cutoffTwoOldOldDirichlet later coefficient)
    (cutoffTwoOldNewDirichlet later coefficient)
    (cutoffTwoNewOldDirichlet later coefficient)
    (cutoffTwoNewNewDirichlet later coefficient)

private theorem cutoffTwoDirichletBlock_nonnegative
    (leftStates rightStates : List Nat)
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteJointDirichletBlock
      leftStates rightStates coefficient
      (centralPhysicalFiniteKernel
        cutoffTwoHalfCoupling (by decide) later 0) := by
  exact finiteJointDirichletBlock_nonnegative
    leftStates rightStates coefficient _
    (fun left right => by
      unfold centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        (by decide) later 0 _ _)

theorem cutoffTwoOldOldDirichlet_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoOldOldDirichlet later coefficient := by
  unfold cutoffTwoOldOldDirichlet
  exact cutoffTwoDirichletBlock_nonnegative _ _ later coefficient

theorem cutoffTwoOldNewDirichlet_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoOldNewDirichlet later coefficient := by
  unfold cutoffTwoOldNewDirichlet
  exact cutoffTwoDirichletBlock_nonnegative _ _ later coefficient

theorem cutoffTwoNewOldDirichlet_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoNewOldDirichlet later coefficient := by
  unfold cutoffTwoNewOldDirichlet
  exact cutoffTwoDirichletBlock_nonnegative _ _ later coefficient

theorem cutoffTwoNewNewDirichlet_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoNewNewDirichlet later coefficient := by
  unfold cutoffTwoNewNewDirichlet
  exact cutoffTwoDirichletBlock_nonnegative _ _ later coefficient

theorem cutoffTwoWithinBlockDirichlet_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoWithinBlockDirichlet later coefficient := by
  unfold cutoffTwoWithinBlockDirichlet
  exact Q'.zero_le_add _ _
    (cutoffTwoOldOldDirichlet_nonnegative later coefficient)
    (cutoffTwoNewNewDirichlet_nonnegative later coefficient)

theorem cutoffTwoCrossBlockDirichlet_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoCrossBlockDirichlet later coefficient := by
  unfold cutoffTwoCrossBlockDirichlet
  exact Q'.zero_le_add _ _
    (cutoffTwoOldNewDirichlet_nonnegative later coefficient)
    (cutoffTwoNewOldDirichlet_nonnegative later coefficient)

/-- Within-block energy is a genuine lower portion of full energy. -/
theorem cutoffTwoWithinBlockDirichlet_le_full
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoWithinBlockDirichlet later coefficient ≤
      cutoffTwoFullSectorDirichlet later coefficient := by
  have hsplit :=
    cutoffTwoFullSectorDirichlet_eqv_within_add_cross later coefficient
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (cutoffTwoCrossBlockDirichlet_nonnegative later coefficient))
    (Q'.ge_of_eqv hsplit)

/-- Cross-block energy is also a genuine lower portion of full energy, so it
can be used as coercivity rather than paid as a matrix error. -/
theorem cutoffTwoCrossBlockDirichlet_le_full
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCrossBlockDirichlet later coefficient ≤
      cutoffTwoFullSectorDirichlet later coefficient := by
  have hsplit :=
    cutoffTwoFullSectorDirichlet_eqv_within_add_cross later coefficient
  refine Q'.le_trans' _
    (cutoffTwoWithinBlockDirichlet later coefficient +
      cutoffTwoCrossBlockDirichlet later coefficient) _ ?_ ?_
  · exact Q'.le_trans' _
      (cutoffTwoCrossBlockDirichlet later coefficient +
        cutoffTwoWithinBlockDirichlet later coefficient) _
      (Q'.add_le_self_of_nonneg _ _
        (cutoffTwoWithinBlockDirichlet_nonnegative later coefficient))
      (Q'.le_of_eqv
        (Q'.add_comm_eqv
          (cutoffTwoCrossBlockDirichlet later coefficient)
          (cutoffTwoWithinBlockDirichlet later coefficient)))
  · exact Q'.ge_of_eqv hsplit

/-! ## 3. Connection back to the transfer deficit -/

/-- The partitioned full energy is still exactly twice the physical
diagonal-minus-transfer deficit. -/
theorem cutoffTwoFullSectorDirichlet_eqv_twice_deficit
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorDirichlet later coefficient ≈
      (cutoffTwoFullSectorDiagonal later coefficient +
        cutoffTwoFullSectorDiagonal later coefficient) +
      -(cutoffTwoFullSectorMatrix later coefficient +
        cutoffTwoFullSectorMatrix later coefficient) := by
  unfold cutoffTwoFullSectorDirichlet
    cutoffTwoFullSectorDiagonal cutoffTwoFullSectorMatrix
  exact centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
    cutoffTwoHalfCoupling (by decide) later 0 coefficient

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.finiteJointDirichletEnergy_filter_four_blocks
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.finiteJointDirichletBlock_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.cutoffTwoFullSectorDirichlet_four_blocks
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.cutoffTwoFullSectorDirichlet_eqv_within_add_cross
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.cutoffTwoWithinBlockDirichlet_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.cutoffTwoCrossBlockDirichlet_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.cutoffTwoWithinBlockDirichlet_le_full
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.cutoffTwoCrossBlockDirichlet_le_full
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.cutoffTwoFullSectorDirichlet_eqv_twice_deficit
