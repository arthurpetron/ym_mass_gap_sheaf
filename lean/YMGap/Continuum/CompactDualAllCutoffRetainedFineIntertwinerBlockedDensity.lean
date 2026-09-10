/-
# Exact point density of the retained blocked law

For a positive physical row whose four-preimage raw partition is not
positive, the lossless all-cutoff kernel uses the retained
fine-intertwiner sector.  This module proves that the complete blocked mass
of each retained target is exactly its normalized literal expanded-source
weight.

The only possible contribution comes from the target's own physical source.
A mixed-radix physical-state code proves this constructively on the attached
finite carrier; every other source row vanishes at that retained target.  The
surviving term is then the normalized density identity already connecting the
retained conditional law to component peeling.

No uniform estimate, reflection lift, spectral gap, continuum limit, or Clay
theorem is claimed.

## Axiom gate

Finite recursion on a duplicate-free attached list and exact rational algebra
only.  No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedDensity

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A constructive unique-code summation lemma -/

private theorem listQSum_eq_selected_of_code
    {A : Type} (value : A → Q') (code : A → Nat) (selected : A) :
    ∀ (items : List A), items.Nodup → selected ∈ items →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        code left = code right → left = right) →
      (∀ item, item ∈ items → code item ≠ code selected →
        value item ≈ 0) →
      listQSum value items ≈ value selected
  | [], _, hmem, _, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem, hinjective, hzero => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hcode : code head = code selected
      · have heq : head = selected :=
          hinjective head List.mem_cons_self selected hmem hcode
        subst head
        have htailZero : listQSum value tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _ : A => (0 : Q')) tail) _ ?_
            (listQSum_zero tail)
          apply listQSum_congr_on _ _ tail
          intro item hitem
          apply hzero item (List.mem_cons_of_mem selected hitem)
          intro hitemCode
          have hitemEq : item = selected :=
            hinjective item (List.mem_cons_of_mem selected hitem)
              selected List.mem_cons_self hitemCode
          subst item
          exact hparts.1 hitem
        simp only [listQSum]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hselectedTail : selected ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst head
            exact False.elim (hcode rfl)
          · exact htail
        have htailInjective :
            ∀ left, left ∈ tail → ∀ right, right ∈ tail →
              code left = code right → left = right := by
          intro left hleft right hright hsame
          exact hinjective left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) hsame
        have htailZero :
            ∀ item, item ∈ tail → code item ≠ code selected →
              value item ≈ 0 := by
          intro item hitem hne
          exact hzero item (List.mem_cons_of_mem head hitem) hne
        simp only [listQSum]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr'
            (hzero head List.mem_cons_self hcode)
            (listQSum_eq_selected_of_code value code selected tail
              hparts.2 hselectedTail htailInjective htailZero))
          (Q'.eqv_of_eq (Q'.zero_add' _))

/-! ## 2. Every differently coded source vanishes -/

private theorem retainedTargetSourceTerm_zero_of_code_ne
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (source : SlabPhysicalSourceEntry S.fine)
    (hcode : slabPhysicalStateCode S.fine source.1 ≠
      slabPhysicalStateCode S.fine target.1) :
    S.fine.normalizedMass source.1 *
        allCutoffRetainedFineIntertwinerKernel S source (.inr target) ≈
      0 := by
  unfold allCutoffRetainedFineIntertwinerKernel
  by_cases hpositive : (0 : Q') < S.fine.physicalTerm source.1
  · rw [dif_pos hpositive]
    by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S source.1
    · rw [dif_pos hpartition]
      exact Q'.mul_zero_eqv _
    · rw [dif_neg hpartition]
      unfold retainedSamePhysicalStateKernel
      have hne : slabPhysicalStateCode S.fine target.1 ≠
          slabPhysicalStateCode S.fine source.1 := by
        intro heq
        exact hcode heq.symm
      change
        S.fine.normalizedMass source.1 *
            (if slabPhysicalStateCode S.fine target.1 =
                slabPhysicalStateCode S.fine source.1 then
              retainedFineIntertwinerConditionalKernel
                (retainedSourceOfPhysicalEntry source hpositive) target.2
            else 0) ≈ 0
      rw [if_neg hne]
      exact Q'.mul_zero_eqv _
  · rw [dif_neg hpositive]
    exact Q'.mul_zero_eqv _

/-! ## 3. The selected source is the expanded point density -/

theorem retainedFineTargetSelectedSourceTerm_eqv_expandedMass
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : (Sum.inr target : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hpositive : (0 : Q') < S.fine.physicalTerm target.1)
    (hnotPartition : ¬ (0 : Q') <
      wholeSlabRawRowPartition S target.1) :
    S.fine.normalizedMass target.1 *
        allCutoffRetainedFineIntertwinerKernel S
          (retainedFineTargetPhysicalSource S target htarget)
          (.inr target) ≈
      slabExpandedFineEntryNormalizedMass S.fine
        (retainedFineTargetExpandedEntry S target htarget) := by
  rw [allCutoffRetainedFineIntertwinerKernel_eq_retained_of_incoherent
    S (retainedFineTargetPhysicalSource S target htarget)
      hpositive hnotPartition target]
  exact normalizedMass_mul_retainedKernel_eqv_expandedMass
    S target htarget hpositive

/-! ## 4. Exact targetwise retained blocked mass -/

/-- On a positive incoherent target, the complete enriched blocked law has
exactly the normalized literal expanded-source point mass. -/
theorem allCutoffRetainedBlockedMass_eqv_expandedMass_of_incoherent
    (S : SlabScalePair)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : (Sum.inr target : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S)
    (hpositive : (0 : Q') < S.fine.physicalTerm target.1)
    (hnotPartition : ¬ (0 : Q') <
      wholeSlabRawRowPartition S target.1) :
    allCutoffRetainedFineIntertwinerBlockedMass S (.inr target) ≈
      slabExpandedFineEntryNormalizedMass S.fine
        (retainedFineTargetExpandedEntry S target htarget) := by
  let selected := retainedFineTargetPhysicalSource S target htarget
  unfold allCutoffRetainedFineIntertwinerBlockedMass
  refine Q'.eqv_trans _
    (S.fine.normalizedMass selected.1 *
      allCutoffRetainedFineIntertwinerKernel S selected (.inr target)) _
    ?_ ?_
  · apply listQSum_eq_selected_of_code
      (fun source : SlabPhysicalSourceEntry S.fine =>
        S.fine.normalizedMass source.1 *
          allCutoffRetainedFineIntertwinerKernel S source (.inr target))
      (fun source : SlabPhysicalSourceEntry S.fine =>
        slabPhysicalStateCode S.fine source.1)
      selected
      (slabPhysicalSourceEntries S.fine)
      (slabPhysicalSourceEntries_nodup S.fine)
      (List.mem_attach S.fine.physicalLabellings selected)
    · intro left _ right _ hsame
      apply Subtype.ext
      exact slabPhysicalStateCode_injective_on_carrier
        left.2 right.2 hsame
    · intro source _ hne
      apply retainedTargetSourceTerm_zero_of_code_ne S target source
      simpa only [selected, retainedFineTargetPhysicalSource] using hne
  · simpa only [selected, retainedFineTargetPhysicalSource] using
      retainedFineTargetSelectedSourceTerm_eqv_expandedMass
        S target htarget hpositive hnotPartition

/-! ## Axiom audit -/

#print axioms retainedFineTargetSelectedSourceTerm_eqv_expandedMass
#print axioms allCutoffRetainedBlockedMass_eqv_expandedMass_of_incoherent

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedDensity
