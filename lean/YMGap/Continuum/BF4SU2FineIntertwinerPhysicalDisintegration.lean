/-
# Exact BF4 physical disintegration over the retained fine intertwiner

The complete corrected-slab physical term is the product of its heat-kernel
face factor and the cardinality of the global fine-intertwiner witness list.
This module turns that production formula into an exact finite disintegration:
every literal witness carries one Haar counting unit, and summing the
corresponding face contribution reconstructs the genuine BF4 physical term.

This is the missing physical anchor for the retained conditional kernel.  It
shows that the enlarged carrier is not an auxiliary probability space pasted
onto the spin foam: it is precisely the finite Haar fiber whose cardinality
already occurs in `SlabPhysicalData.physicalTerm`.

Honest scope: this is an exact fixed-spacing disintegration.  It does not yet
identify the grouped five-holonomy Feynman--Kac amplitude, prove a
spacing-uniform spatial window, dominate carrier growth by Mehler decay, or
identify the continuum Perron vector.

## Axiom gate

Finite list recursion and exact `Q'` setoid algebra only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FineIntertwinerChoiCPOrder

namespace YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The counting partition is the production multiplicity -/

private theorem listQSum_one_eqv_ofNat_length {A : Type} :
    ∀ items : List A,
      listQSum (fun _ => (1 : Q')) items ≈
        Q'.ofNat items.length
  | [] => Q'.eqv_symm Q'.ofNat_zero_eqv
  | _ :: tail => by
      simp only [listQSum, List.length_cons]
      refine Q'.eqv_trans _ (1 + Q'.ofNat tail.length) _ ?_ ?_
      · exact Q'.add_eqv_congr_left 1 _ _
          (listQSum_one_eqv_ofNat_length tail)
      · rw [Nat.add_comm tail.length 1]
        exact Q'.eqv_symm (Q'.ofNat_add_eqv 1 tail.length)

/-- The retained conditional partition is exactly the `Q'` image of the
global SU(2) link multiplicity appearing in the physical summand. -/
theorem retainedFineIntertwinerPartition_eqv_linkMultiplicity
    (D : SlabPhysicalData) (fineState : EdgeLabelling) :
    retainedFineIntertwinerPartition D fineState ≈
      Q'.ofNat
        (slabExplicitLinkMultiplicityProduct
          D.cutoff D.extent fineState) := by
  unfold retainedFineIntertwinerPartition
    retainedFineIntertwinerRawWeight
  exact Q'.eqv_trans _ _ _
    (listQSum_one_eqv_ofNat_length
      (slabFineFusionWitnesses D fineState))
    (Q'.eqv_of_eq
      (congrArg Q'.ofNat
        (slabFineFusionWitnesses_length D fineState)))

/-! ## 2. Exact unnormalized physical fiber -/

/-- One literal fine-intertwiner contribution to the corrected-slab physical
term: the common heat-kernel face factor times one Haar counting unit. -/
def retainedFineIntertwinerPhysicalFiberWeight
    (D : SlabPhysicalData) (fineState : EdgeLabelling)
    (witness : SlabFusionWitnessAssignment) : Q' :=
  slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent fineState *
    retainedFineIntertwinerRawWeight D fineState witness

/-- Summing the literal fine-intertwiner fiber reconstructs the genuine BF4
corrected-slab physical term exactly. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_total
    (D : SlabPhysicalData) (fineState : EdgeLabelling) :
    listQSum
        (retainedFineIntertwinerPhysicalFiberWeight D fineState)
        (slabFineFusionWitnesses D fineState) ≈
      D.physicalTerm fineState := by
  unfold retainedFineIntertwinerPhysicalFiberWeight
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent fineState *
      retainedFineIntertwinerPartition D fineState) _ ?_ ?_
  · exact listQSum_mul_left
      (slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent fineState)
      (retainedFineIntertwinerRawWeight D fineState)
      (slabFineFusionWitnesses D fineState)
  · refine Q'.eqv_trans _
      (slabParametricKPhysicalFaceFactor
          D.coupling D.cutoff D.extent fineState *
        Q'.ofNat
          (slabExplicitLinkMultiplicityProduct
            D.cutoff D.extent fineState)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        (slabParametricKPhysicalFaceFactor
          D.coupling D.cutoff D.extent fineState)
        _ _
        (retainedFineIntertwinerPartition_eqv_linkMultiplicity
          D fineState)
    · unfold SlabPhysicalData.physicalTerm
        slabParametricKPhysicalTerm
      exact Q'.eqv_refl _

/-! ## 3. The normalized Haar row is the physical conditional law -/

/-- On a positive physical source, the production summand is the common face
factor times the exact retained Haar partition. -/
theorem physicalTerm_eqv_faceFactor_mul_retainedPartition
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D) :
    D.physicalTerm source.fineState ≈
      slabParametricKPhysicalFaceFactor
          D.coupling D.cutoff D.extent source.fineState *
        retainedFineIntertwinerPartition D source.fineState := by
  unfold SlabPhysicalData.physicalTerm
    slabParametricKPhysicalTerm
  exact Q'.mul_eqv_congr_left
    (slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent source.fineState)
    _ _
    (Q'.eqv_symm
      (retainedFineIntertwinerPartition_eqv_linkMultiplicity
        D source.fineState))

/-- Multiplying the normalized conditional row by its genuine physical source
mass recovers the literal unnormalized fine-intertwiner contribution. -/
theorem physicalTerm_mul_conditionalKernel_eqv_fiberWeight
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (witness : SlabFusionWitnessAssignment) :
    D.physicalTerm source.fineState *
        retainedFineIntertwinerConditionalKernel source witness ≈
      retainedFineIntertwinerPhysicalFiberWeight
        D source.fineState witness := by
  unfold retainedFineIntertwinerConditionalKernel Q'.divPos
    retainedFineIntertwinerPhysicalFiberWeight
  let face :=
    slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent source.fineState
  let partition :=
    retainedFineIntertwinerPartition D source.fineState
  let raw :=
    retainedFineIntertwinerRawWeight
      D source.fineState witness
  let inverse :=
    Q'.recipPos partition
      (retainedFineIntertwinerPartition_pos
        D source.fineState source.physicalTerm_pos)
  refine Q'.eqv_trans _
    ((face * partition) * (raw * inverse)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right
      (D.physicalTerm source.fineState)
      (face * partition)
      (raw * inverse)
      (physicalTerm_eqv_faceFactor_mul_retainedPartition source)
  · refine Q'.eqv_trans _
      ((face * raw) * (partition * inverse)) _ ?_ ?_
    · refine Q'.eqv_trans _
        ((raw * face) * (inverse * partition)) _ ?_ ?_
      · exact mul4_rearrange face partition raw inverse
      · exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (raw * face) (face * raw)
            (inverse * partition)
            (Q'.mul_comm_eqv raw face))
          (Q'.mul_eqv_congr_left
            (face * raw)
            (inverse * partition) (partition * inverse)
            (Q'.mul_comm_eqv inverse partition))
    · refine Q'.eqv_trans _
        ((face * raw) * 1) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left
          (face * raw)
          (partition * inverse) 1
          (Q'.mul_recipPos_eqv partition
            (retainedFineIntertwinerPartition_pos
              D source.fineState source.physicalTerm_pos))
      · exact Q'.mul_one_eqv (face * raw)

/-- The normalized version of the literal physical fine-intertwiner fiber. -/
def retainedFineIntertwinerNormalizedPhysicalFiberWeight
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (witness : SlabFusionWitnessAssignment) : Q' :=
  Q'.divPos
    (retainedFineIntertwinerPhysicalFiberWeight
      D source.fineState witness)
    (D.physicalTerm source.fineState)
    source.physicalTerm_pos

/-- The normalized unit-counting kernel is not merely compatible with the
physical disintegration: it is exactly its conditional probability law. -/
theorem normalizedPhysicalFiberWeight_eqv_conditionalKernel
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (witness : SlabFusionWitnessAssignment) :
    retainedFineIntertwinerNormalizedPhysicalFiberWeight
        source witness ≈
      retainedFineIntertwinerConditionalKernel
        source witness := by
  unfold retainedFineIntertwinerNormalizedPhysicalFiberWeight
  apply Q'.mul_left_cancel_of_pos source.physicalTerm_pos
  refine Q'.eqv_trans _
    (retainedFineIntertwinerPhysicalFiberWeight
      D source.fineState witness) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (D.physicalTerm source.fineState)
        (Q'.divPos
          (retainedFineIntertwinerPhysicalFiberWeight
            D source.fineState witness)
          (D.physicalTerm source.fineState)
          source.physicalTerm_pos))
      (Q'.divPos_mul_eqv
        (retainedFineIntertwinerPhysicalFiberWeight
          D source.fineState witness)
        (D.physicalTerm source.fineState)
        source.physicalTerm_pos)
  · exact Q'.eqv_symm
      (physicalTerm_mul_conditionalKernel_eqv_fiberWeight
        source witness)

/-- Consequently the normalized literal physical fiber has exact row mass
one on the same production witness list. -/
theorem normalizedPhysicalFiberWeight_total
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D) :
    listQSum
        (retainedFineIntertwinerNormalizedPhysicalFiberWeight source)
        (slabFineFusionWitnesses D source.fineState) ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (normalizedPhysicalFiberWeight_eqv_conditionalKernel source)
      (slabFineFusionWitnesses D source.fineState))
    (retainedFineIntertwinerConditionalKernel_row_normalized source)

#print axioms retainedFineIntertwinerPartition_eqv_linkMultiplicity
#print axioms retainedFineIntertwinerPhysicalFiberWeight_total
#print axioms physicalTerm_eqv_faceFactor_mul_retainedPartition
#print axioms physicalTerm_mul_conditionalKernel_eqv_fiberWeight
#print axioms normalizedPhysicalFiberWeight_eqv_conditionalKernel
#print axioms normalizedPhysicalFiberWeight_total

end YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
