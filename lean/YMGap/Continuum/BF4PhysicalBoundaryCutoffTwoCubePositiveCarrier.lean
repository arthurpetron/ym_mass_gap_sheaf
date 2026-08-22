/-
# The cutoff-two cube sector lies in the physical positive-row carrier

The sealed production-kernel row-zero star gives every state in the exact
65-state table a positive return entry through the table hub.  Hence every
table state has strictly positive physical row marginal and belongs to the
literal positive-row Markov carrier.

This is finite cutoff two only.  It does not assert cutoff compatibility,
ergodicity, a completed-space gap, or a continuum limit.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

theorem zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates :
    zeroEdgeLabelling ∈ cutoffTwoCubeSectorStates := by
  apply (mem_cutoffTwoCubeSectorStates_iff zeroEdgeLabelling).mpr
  right
  constructor
  · intro id _
    exact Or.inl rfl
  · intro id _
    rfl

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

/-- Every state of the certified block is genuinely retained by the
positive-row Markov carrier.  The positive table-hub row and kernel symmetry
give a positive normalized entry in the state's own row. -/
theorem cutoffTwoCubeSectorState_mem_positive
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    state ∈ centralPositiveHalfStates cutoffTwoHalfCoupling
      (by decide) 2 0 := by
  obtain ⟨column, hcolumnLength, hcolumnState⟩ :=
    finiteListStateAt_exists_of_mem zeroEdgeLabelling state hstate
  have hcolumn : column < 65 := by
    rw [cutoffTwoCubeSectorStates_length] at hcolumnLength
    exact hcolumnLength
  change cutoffTwoSectorStateAt column = state at hcolumnState
  have hhubHalf : cutoffTwoSectorStateAt 0 ∈ centralHalfStates 2 0 :=
    cutoffTwoCubeSectorState_mem_halfStates
      (cutoffTwoSectorStateAt_mem (by decide : 0 < 65))
  have hstateHalf : state ∈ centralHalfStates 2 0 :=
    cutoffTwoCubeSectorState_mem_halfStates hstate
  have hforward : (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt 0) state := by
    rw [← hcolumnState]
    exact centralPhysicalReflectedKernel_cutoffTwo_stateAt_zero_sectorStateAt_pos
      hcolumn
  have hreverse : (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        state (cutoffTwoSectorStateAt 0) := by
    exact Q'.pos_of_lt_of_le hforward
      (Q'.ge_of_eqv
        (centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
          hstateHalf hhubHalf))
  have hnormalized : (0 : Q') <
      centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
        (by decide) 2 0 state (cutoffTwoSectorStateAt 0) := by
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.mul_pos hreverse (Q'.recipPos_pos _ _)
  have hrow : (0 : Q') <
      centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide) 2 0 state := by
    unfold centralPhysicalRowMarginal
    exact Q'.pos_of_lt_of_le hnormalized
      (listQSum_member_le_nonnegative_local
        (centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
          (by decide) 2 0 state)
        (fun target => centralNormalizedPhysicalReflectedKernel_nonnegative
          (by decide) 2 0 state target)
        (centralHalfStates 2 0) hhubHalf)
  exact mem_centralPositiveHalfStates_iff.mpr ⟨hstateHalf, hrow⟩

/-- Proof-local table index for a literal sector state.  The existential is
used only to establish propositional graph membership; it is not exposed as a
computational modulus or later data field. -/
theorem cutoffTwoCubeSectorState_exists_tableIndex
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    ∃ column, column < 65 ∧ cutoffTwoSectorStateAt column = state := by
  obtain ⟨column, hlength, hstateAt⟩ :=
    finiteListStateAt_exists_of_mem zeroEdgeLabelling state hstate
  refine ⟨column, ?_, ?_⟩
  · rw [cutoffTwoCubeSectorStates_length] at hlength
    exact hlength
  · exact hstateAt

/-- Proof-local positive-carrier index for a literal sector state. -/
theorem cutoffTwoCubeSectorState_exists_positiveIndex
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    ∃ index,
      index < centralPhysicalFiniteCarrierSize cutoffTwoHalfCoupling
        (by decide) 2 0 ∧
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) 2 0 index = state :=
  centralPhysicalFiniteStateAt_exists cutoffTwoHalfCoupling
    (by decide) 2 0 (cutoffTwoCubeSectorState_mem_positive hstate)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier.zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier.cutoffTwoCubeSectorState_mem_positive
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier.cutoffTwoCubeSectorState_exists_tableIndex
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier.cutoffTwoCubeSectorState_exists_positiveIndex
