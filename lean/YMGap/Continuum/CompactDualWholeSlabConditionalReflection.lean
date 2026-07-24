/-
# Reflection of the normalized whole-slab recoupling kernel

`CompactDualWholeSlabRecouplingReflection` proves reflection of the complete
unnormalized slab carrier.  This module lifts that result through the single
whole-row partition and the positive rational division used to normalize a
coherent row.

The construction is proof-relevant: a reflected
`CoherentSlabRecouplingSource` carries its reflected fine state, reflected
positive coarse witness, both physical-membership proofs, and the transported
strict-positivity proof.  The row partition is then reindexed by the literal
reflection permutation of the complete coarse labelling list.

This closes the normalized reflection seam needed before zero-mass rows can be
completed into a total cutoff-one `FiniteSlabKernel`.

## Axiom gate

Finite list reindexing and exact positive-rational division only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.CompactDualWholeSlabRecouplingReflection

namespace YMGap.Continuum.CompactDualWholeSlabConditionalReflection

set_option maxRecDepth 30000
set_option maxHeartbeats 600000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.CompactDualWholeSlabRecouplingReflection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-- Reflect a coherent positive row together with its positive coarse witness. -/
def reflectCoherentSlabRecouplingSource
    {S : SlabScalePair}
    (source : CoherentSlabRecouplingSource S) :
    CoherentSlabRecouplingSource S where
  fineState := S.fine.reflectLabelling source.fineState
  fine_mem :=
    reflectSupportedSlabFaceLabelling_mem source.fine_mem
  coarseWitness :=
    S.coarse.reflectLabelling source.coarseWitness
  coarseWitness_mem :=
    reflectSupportedSlabFaceLabelling_mem source.coarseWitness_mem
  coarseWitness_positive := by
    have hreflection :=
      wholeSlabRecouplingRawWeight_reflection
        S (fineState := source.fineState)
          (coarseState := source.coarseWitness)
          source.coarseWitness_mem
    exact Q'.pos_of_lt_of_le
      source.coarseWitness_positive
      (Q'.ge_of_eqv hreflection)

/-- Reflection reindexes the complete whole-row partition exactly. -/
theorem wholeSlabRecouplingPartition_reflection
    {S : SlabScalePair}
    (source : CoherentSlabRecouplingSource S) :
    wholeSlabRecouplingPartition
        (reflectCoherentSlabRecouplingSource source) ≈
      wholeSlabRecouplingPartition source := by
  unfold wholeSlabRecouplingPartition
  let reflectedWeight : EdgeLabelling → Q' :=
    wholeSlabRecouplingRawWeight S
      (S.fine.reflectLabelling source.fineState)
  let sourceWeight : EdgeLabelling → Q' :=
    wholeSlabRecouplingRawWeight S source.fineState
  change
    listQSum reflectedWeight S.coarse.physicalLabellings ≈
      listQSum sourceWeight S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum reflectedWeight
      (S.coarse.physicalLabellings.map
        S.coarse.reflectLabelling)) _ ?_ ?_
  · exact
      YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm
        reflectedWeight
        (boundedSlabFaceLabellings_reflection_perm
          S.coarse.cutoff S.coarse.extent).symm
  · rw [listQSum_map]
    exact listQSum_congr_on _ _
      S.coarse.physicalLabellings
      (fun coarseState hcoarse =>
        wholeSlabRecouplingRawWeight_reflection S hcoarse)

private theorem qeqv_of_le_of_ge {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr
    {numerator numerator' denominator denominator' : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hdenominator' : (0 : Q') < denominator')
    (hnumerator : numerator ≈ numerator')
    (hdenominatorEq : denominator ≈ denominator') :
    Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos numerator' denominator' hdenominator' := by
  apply qeqv_of_le_of_ge
  · apply Q'.le_divPos_of_mul_le
      numerator' denominator' hdenominator'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator denominator hdenominator)
          denominator' denominator
          (Q'.eqv_symm hdenominatorEq))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator denominator hdenominator)
          hnumerator))
  · apply Q'.le_divPos_of_mul_le
      numerator denominator hdenominator
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator' denominator' hdenominator')
          denominator denominator' hdenominatorEq)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator' denominator' hdenominator')
          (Q'.eqv_symm hnumerator)))

/-- The normalized coherent whole-slab row intertwines corrected-slab
reflection exactly. -/
theorem wholeSlabRecouplingConditionalKernel_reflection
    {S : SlabScalePair}
    (source : CoherentSlabRecouplingSource S)
    {coarseState : EdgeLabelling}
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    wholeSlabRecouplingConditionalKernel
        (reflectCoherentSlabRecouplingSource source)
        (S.coarse.reflectLabelling coarseState) ≈
      wholeSlabRecouplingConditionalKernel source coarseState := by
  unfold wholeSlabRecouplingConditionalKernel
  exact divPos_eqv_congr
    (wholeSlabRecouplingPartition_pos
      (reflectCoherentSlabRecouplingSource source))
    (wholeSlabRecouplingPartition_pos source)
    (wholeSlabRecouplingRawWeight_reflection S hcoarse)
    (wholeSlabRecouplingPartition_reflection source)

#print axioms reflectCoherentSlabRecouplingSource
#print axioms wholeSlabRecouplingPartition_reflection
#print axioms wholeSlabRecouplingConditionalKernel_reflection

end YMGap.Continuum.CompactDualWholeSlabConditionalReflection
