/-
# Exact physical pushforward through the total cutoff-one slab kernel

The total whole-slab matrix includes a stochastic completion on Gibbs-null
rows.  This module removes that bookkeeping from the pushed physical law.
It defines a dependent finite sum over strictly positive fine Gibbs rows,
using the globally link-glued recoupling conditional kernel on each such row,
and proves that the instantiated `FiniteSlabKernel.blockedMass` is exactly
that sum.

The retained remainder is therefore an actual, computed discrepancy:

    recoupled positive fine mass - normalized coarse Gibbs mass.

It has zero total mass and exact `L¹` norm at most two.  No smallness, cutoff
uniformity, or vanishing estimate is claimed here; those remain the next
analytic gate.

## Axiom gate

Finite exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualCutoffOneTotalKernel

namespace YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Nonpositive listed rows have exactly zero normalized mass -/

private theorem qeqv_of_le_of_ge {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

theorem physicalTerm_eqv_zero_of_not_positive
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (hnotPositive : ¬ (0 : Q') < D.physicalTerm physical) :
    D.physicalTerm physical ≈ 0 := by
  apply qeqv_of_le_of_ge
  · exact Int.not_lt.mp hnotPositive
  · exact slabParametricKPhysicalTerm_nonnegative
      D.coupling_nonnegative D.cutoff D.extent physical

theorem normalizedMass_eqv_zero_of_not_positive
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (hnotPositive : ¬ (0 : Q') < D.physicalTerm physical) :
    D.normalizedMass physical ≈ 0 := by
  unfold SlabPhysicalData.normalizedMass Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos D.physicalPartition
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (physicalTerm_eqv_zero_of_not_positive
        D physical hnotPositive)
  · exact Q'.zero_mul_eqv _

theorem nullRow_pushforwardContribution_eqv_zero
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineState coarseState : EdgeLabelling)
    (hnotPositive :
      ¬ (0 : Q') < S.fine.physicalTerm fineState) :
    S.fine.normalizedMass fineState *
        cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
          fineState coarseState ≈
      0 := by
  refine Q'.eqv_trans _
    (0 * cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
      fineState coarseState) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (normalizedMass_eqv_zero_of_not_positive
        S.fine fineState hnotPositive)
  · exact Q'.zero_mul_eqv _

/-! ## 2. The positive-row recoupling sum -/

/-- The fine pushforward with all Gibbs-null rows omitted.  The membership
argument makes the strictly positive branch able to construct its coherent
whole-slab recoupling witness without choice. -/
def positiveRecouplingBlockedMassAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) → Q'
  | [], _ => 0
  | source :: tail, hphysical =>
      if hpositive :
          (0 : Q') < S.fine.physicalTerm source then
        S.fine.normalizedMass source *
            wholeSlabRecouplingConditionalKernel
              (positiveCoherentSource S hfineCutoff hcoarseCoupling
                source
                (hphysical source List.mem_cons_self)
                hpositive)
              target +
          positiveRecouplingBlockedMassAux S hfineCutoff
            hcoarseCoupling target tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        positiveRecouplingBlockedMassAux S hfineCutoff
          hcoarseCoupling target tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

def positiveRecouplingBlockedMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) : Q' :=
  positiveRecouplingBlockedMassAux S hfineCutoff hcoarseCoupling
    target S.fine.physicalLabellings
    (fun _ hsource => hsource)

private theorem kernelSum_eq_positiveRecouplingAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              cutoffOneWholeSlabKernel S hfineCutoff
                hcoarseCoupling source target)
          sources ≈
        positiveRecouplingBlockedMassAux S hfineCutoff
          hcoarseCoupling target sources hphysical
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let hsource :=
        hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum, positiveRecouplingBlockedMassAux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.normalizedMass source) _ _
            (cutoffOneWholeSlabKernel_eq_positive
              S hfineCutoff hcoarseCoupling
              hsource hpositive target))
          (kernelSum_eq_positiveRecouplingAux
            S hfineCutoff hcoarseCoupling target tail htail)
      · simp only [listQSum, positiveRecouplingBlockedMassAux,
          dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + positiveRecouplingBlockedMassAux S hfineCutoff
            hcoarseCoupling target tail htail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (nullRow_pushforwardContribution_eqv_zero
              S hfineCutoff hcoarseCoupling source target hpositive)
            (kernelSum_eq_positiveRecouplingAux
              S hfineCutoff hcoarseCoupling target tail htail)
        · exact Q'.eqv_of_eq (Q'.zero_add' _)

def physicalKernel
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    S.FiniteSlabKernel :=
  cutoffOneWholeSlabFiniteKernel
    S hfineCutoff hcoarseCoupling

theorem blockedMass_eq_positiveRecouplingBlockedMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    (physicalKernel S hfineCutoff hcoarseCoupling).blockedMass target ≈
      positiveRecouplingBlockedMass S hfineCutoff
        hcoarseCoupling target := by
  unfold SlabScalePair.FiniteSlabKernel.blockedMass
    physicalKernel positiveRecouplingBlockedMass
  exact kernelSum_eq_positiveRecouplingAux
    S hfineCutoff hcoarseCoupling target
    S.fine.physicalLabellings
    (fun source hsource => hsource)

/-! ## 3. The actual retained remainder -/

def physicalRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) : Q' :=
  positiveRecouplingBlockedMass S hfineCutoff
      hcoarseCoupling target +
    -(S.coarse.normalizedMass target)

def physicalRemainderL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (physicalRemainder S hfineCutoff hcoarseCoupling target))
    S.coarse.physicalLabellings

theorem retainedRemainder_eq_physicalRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    (physicalKernel S hfineCutoff hcoarseCoupling).remainder target ≈
      physicalRemainder S hfineCutoff hcoarseCoupling target := by
  unfold SlabScalePair.FiniteSlabKernel.remainder physicalRemainder
  exact Q'.add_eqv_congr_right _ _ _
    (blockedMass_eq_positiveRecouplingBlockedMass
      S hfineCutoff hcoarseCoupling target)

theorem physical_pushforward_decomposition
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    positiveRecouplingBlockedMass S hfineCutoff
        hcoarseCoupling target ≈
      S.coarse.normalizedMass target +
        physicalRemainder S hfineCutoff hcoarseCoupling target := by
  unfold physicalRemainder
  exact Q'.add_sub_cancel_eqv
    (positiveRecouplingBlockedMass S hfineCutoff
      hcoarseCoupling target)
    (S.coarse.normalizedMass target)

theorem physicalRemainder_total_eqv_zero
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    listQSum
        (physicalRemainder S hfineCutoff hcoarseCoupling)
        S.coarse.physicalLabellings ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum
      (physicalKernel S hfineCutoff hcoarseCoupling).remainder
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _
      S.coarse.physicalLabellings
      (fun target _ =>
        Q'.eqv_symm
          (retainedRemainder_eq_physicalRemainder
            S hfineCutoff hcoarseCoupling target))
  · exact
      (physicalKernel S hfineCutoff hcoarseCoupling
      ).remainder_total_eqv_zero

theorem retainedRemainderL1_eq_physicalRemainderL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    (physicalKernel S hfineCutoff hcoarseCoupling).remainderL1 ≈
      physicalRemainderL1 S hfineCutoff hcoarseCoupling := by
  unfold SlabScalePair.FiniteSlabKernel.remainderL1
    physicalRemainderL1
  exact listQSum_congr_on _ _ S.coarse.physicalLabellings
    (fun target _ =>
      Q'.abs_eqv_congr
        (retainedRemainder_eq_physicalRemainder
          S hfineCutoff hcoarseCoupling target))

theorem physicalRemainderL1_le_two
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    physicalRemainderL1 S hfineCutoff hcoarseCoupling ≤ 2 := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (retainedRemainderL1_eq_physicalRemainderL1
          S hfineCutoff hcoarseCoupling)))
    ((physicalKernel S hfineCutoff hcoarseCoupling
      ).remainderL1_le_two)

#print axioms physicalTerm_eqv_zero_of_not_positive
#print axioms blockedMass_eq_positiveRecouplingBlockedMass
#print axioms retainedRemainder_eq_physicalRemainder
#print axioms physical_pushforward_decomposition
#print axioms physicalRemainder_total_eqv_zero
#print axioms physicalRemainderL1_le_two

end YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
