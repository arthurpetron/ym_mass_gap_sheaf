/-
# Exact conditional Haar row on the retained fine-intertwiner carrier

For fixed fine face labels, the SU(2) link factor is the cardinality of the
literal finite list `slabFineFusionWitnesses`.  Each accepted global
intertwiner assignment contributes one unit.  This module therefore defines
the exact conditional Haar-fiber row: raw weight one on the typed carrier
list, normalized by its finite partition.

Positivity of the physical spin-foam summand makes the witness list
nonempty.  The resulting kernel is nonnegative, row-normalized, strictly
positive on every retained member.  It is the first normalization layer
surviving the four-preimage raw-row no-go.

This is not yet a coarse BF4 pushforward.  Conditional integration must next
contract observables while this fine intertwiner index remains present (or
replace it by a proved-equivalent side-complete collared packet).

## Axiom gate

Finite list recursion and exact `Q'` division only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, choice, or noncomputable
declaration.
-/

import YMGap.Continuum.BF4SU2OuterFineIntertwinerRetainedCarrier

namespace YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
open YMGap.Continuum.BF4SU2OuterFineIntertwinerRetainedCarrier
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Unit counting weight.  Its target domain is the literal
`slabFineFusionWitnesses` list used in every row sum below; assignments
outside that list are not part of the typed carrier. -/
def retainedFineIntertwinerRawWeight
    (_D : SlabPhysicalData) (_fineState : EdgeLabelling)
    (_witness : SlabFusionWitnessAssignment) : Q' :=
  1

theorem retainedFineIntertwinerRawWeight_nonnegative
    (D : SlabPhysicalData) (fineState : EdgeLabelling)
    (witness : SlabFusionWitnessAssignment) :
    (0 : Q') ≤
      retainedFineIntertwinerRawWeight D fineState witness := by
  unfold retainedFineIntertwinerRawWeight
  exact Q'.zero_le_one

theorem retainedFineIntertwinerRawWeight_eq_one
    {D : SlabPhysicalData} {fineState : EdgeLabelling}
    {witness : SlabFusionWitnessAssignment}
    (_hmem : witness ∈ slabFineFusionWitnesses D fineState) :
    retainedFineIntertwinerRawWeight D fineState witness = 1 := by
  rfl

/-- The exact cardinality partition of the retained Haar fiber. -/
def retainedFineIntertwinerPartition
    (D : SlabPhysicalData) (fineState : EdgeLabelling) : Q' :=
  listQSum
    (retainedFineIntertwinerRawWeight D fineState)
    (slabFineFusionWitnesses D fineState)

private theorem listQSum_member_le_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items →
        value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head)
              (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

/-- Positive physical mass makes the retained Haar-fiber partition
strictly positive. -/
theorem retainedFineIntertwinerPartition_pos
    (D : SlabPhysicalData) (fineState : EdgeLabelling)
    (hpositive : (0 : Q') < D.physicalTerm fineState) :
    (0 : Q') <
      retainedFineIntertwinerPartition D fineState := by
  let selected :=
    positivePhysicalTermFineFusionWitness
      D fineState hpositive
  have hselected :
      retainedFineIntertwinerRawWeight
        D fineState selected.1 = 1 :=
    retainedFineIntertwinerRawWeight_eq_one selected.2
  have hle :
      retainedFineIntertwinerRawWeight
          D fineState selected.1 ≤
        retainedFineIntertwinerPartition D fineState := by
    unfold retainedFineIntertwinerPartition
    exact listQSum_member_le_nonnegative
      (retainedFineIntertwinerRawWeight D fineState)
      (retainedFineIntertwinerRawWeight_nonnegative D fineState)
      (slabFineFusionWitnesses D fineState)
      selected.2
  rw [hselected] at hle
  exact Q'.pos_of_lt_of_le (by decide) hle

/-- A positive physical row together with its exact retained-carrier
normalization data. -/
structure RetainedFineIntertwinerSource
    (D : SlabPhysicalData) : Type where
  fineState : EdgeLabelling
  fineState_mem : fineState ∈ D.physicalLabellings
  physicalTerm_pos : (0 : Q') < D.physicalTerm fineState

/-- The normalized conditional Haar-fiber row. -/
def retainedFineIntertwinerConditionalKernel
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (witness : SlabFusionWitnessAssignment) : Q' :=
  Q'.divPos
    (retainedFineIntertwinerRawWeight
      D source.fineState witness)
    (retainedFineIntertwinerPartition
      D source.fineState)
    (retainedFineIntertwinerPartition_pos
      D source.fineState source.physicalTerm_pos)

theorem retainedFineIntertwinerConditionalKernel_nonnegative
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (witness : SlabFusionWitnessAssignment) :
    (0 : Q') ≤
      retainedFineIntertwinerConditionalKernel
        source witness := by
  unfold retainedFineIntertwinerConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (retainedFineIntertwinerRawWeight_nonnegative
      D source.fineState witness)
    (Q'.le_of_lt
      (Q'.recipPos_pos _ _))

theorem retainedFineIntertwinerConditionalKernel_pos_on
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    {witness : SlabFusionWitnessAssignment}
    (hmem :
      witness ∈
        slabFineFusionWitnesses D source.fineState) :
    (0 : Q') <
      retainedFineIntertwinerConditionalKernel
        source witness := by
  unfold retainedFineIntertwinerConditionalKernel
  rw [retainedFineIntertwinerRawWeight_eq_one hmem]
  exact Q'.divPos_pos _ _
    (retainedFineIntertwinerPartition_pos
      D source.fineState source.physicalTerm_pos)
    (by decide)

/-- Exact Markov normalization on the literal retained carrier. -/
theorem retainedFineIntertwinerConditionalKernel_row_normalized
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D) :
    listQSum
        (retainedFineIntertwinerConditionalKernel source)
        (slabFineFusionWitnesses D source.fineState) ≈ 1 := by
  unfold retainedFineIntertwinerConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (retainedFineIntertwinerPartition D source.fineState *
      Q'.recipPos
        (retainedFineIntertwinerPartition D source.fineState)
        (retainedFineIntertwinerPartition_pos
          D source.fineState source.physicalTerm_pos)) _
    (listQSum_mul_right
      (retainedFineIntertwinerRawWeight
        D source.fineState)
      (Q'.recipPos
        (retainedFineIntertwinerPartition D source.fineState)
        (retainedFineIntertwinerPartition_pos
          D source.fineState source.physicalTerm_pos))
      (slabFineFusionWitnesses D source.fineState))
    (Q'.mul_recipPos_eqv _
      (retainedFineIntertwinerPartition_pos
        D source.fineState source.physicalTerm_pos))

#print axioms retainedFineIntertwinerPartition_pos
#print axioms retainedFineIntertwinerConditionalKernel_nonnegative
#print axioms retainedFineIntertwinerConditionalKernel_pos_on
#print axioms retainedFineIntertwinerConditionalKernel_row_normalized

end YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
