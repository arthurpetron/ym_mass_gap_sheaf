/-
# The old all-cutoff kernel is the lossy projection of the retained kernel

The corrected all-cutoff target has two sectors: coherent coarse states and
retained fine-intertwiner states.  This module defines the literal forgetting
kernel back to the old coarse carrier.  Ordinary coarse states are preserved
by a supported Dirac row; a retained state is forgotten through exactly the
old source-dependent null completion.

The main theorem proves the row-level commuting square: composing the lossless
retained kernel with this forgetting kernel gives the previous total
four-preimage kernel exactly.  Thus the old fallback is now identified as a
specific quotient of a genuine finite probability flow, and the datum erased
by that quotient is explicit.

This comparison does not assert that forgetting is physically harmless.  The
cutoff-two counterexample proves that it discards a positive-mass sector.  No
reflection lift, repeated same-object carrier, posterior contraction,
spectral gap, continuum limit, or Clay theorem is claimed.

## Axiom gate

Finite exact-rational Fubini and the existing supported point masses only.
No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerProjection

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A weighted supported-Dirac identity -/

private theorem listQSum_weighted_bool_dirac
    {A : Type} (value : A → Q') (selected : A)
    (predicate : A → Bool) :
    ∀ (items : List A), items.Nodup → selected ∈ items →
      (∀ item, item ∈ items →
        (predicate item = true ↔ item = selected)) →
      listQSum
          (fun item =>
            value item * if predicate item then (1 : Q') else 0)
          items ≈ value selected
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem, hunique => by
      have hparts := List.nodup_cons.mp hnodup
      cases hpredicate : predicate head with
      | true =>
        have heq : head = selected :=
          (hunique head List.mem_cons_self).mp hpredicate
        subst head
        have htrue : predicate selected = true :=
          (hunique selected List.mem_cons_self).mpr rfl
        have htailZero :
            listQSum
                (fun item =>
                  value item *
                    if predicate item then (1 : Q') else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _ : A => (0 : Q')) tail) _ ?_ (listQSum_zero tail)
          apply listQSum_congr_on _ _ tail
          intro item hitem
          have hfalse : predicate item = false := by
            apply Bool.eq_false_iff.mpr
            intro hitemTrue
            have hitemEq : item = selected :=
              ((hunique item)
                (List.mem_cons_of_mem selected hitem)).mp hitemTrue
            subst item
            exact hparts.1 hitem
          rw [hfalse]
          exact Q'.mul_zero_eqv _
        simp only [listQSum, htrue, ↓reduceIte]
        exact Q'.eqv_trans _
          (value selected + 0) _
          (Q'.add_eqv_congr' (Q'.mul_one_eqv _) htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      | false =>
        have hselectedTail : selected ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · have htrue : predicate selected = true :=
              (hunique selected hmem).mpr rfl
            have hheadTrue : predicate head = true := by
              rw [← hhead]
              exact htrue
            exact False.elim
              (Bool.noConfusion (hheadTrue.symm.trans hpredicate))
          · exact htail
        simp only [listQSum, hpredicate]
        exact Q'.eqv_trans _
          (0 + value selected) _
          (Q'.add_eqv_congr'
            (Q'.mul_zero_eqv _)
            (listQSum_weighted_bool_dirac value selected predicate
              tail hparts.2 hselectedTail
              (fun item hitem =>
                hunique item (List.mem_cons_of_mem head hitem))))
          (Q'.eqv_of_eq (Q'.zero_add' _))

/-- Summing against the supported identity row evaluates the weight at the
selected physical state. -/
theorem listQSum_mul_supportedDirac_eqv
    (D : SlabPhysicalData) (value : EdgeLabelling → Q')
    {selected : EdgeLabelling}
    (hselected : selected ∈ D.physicalLabellings) :
    listQSum
        (fun intermediate =>
          value intermediate *
            supportedDirac D.faceEdges intermediate selected)
        D.physicalLabellings ≈ value selected := by
  unfold supportedDirac
  apply listQSum_weighted_bool_dirac value selected
    (fun intermediate =>
      supportedLabellingEqB D.faceEdges selected intermediate)
    D.physicalLabellings (slabPhysicalLabellings_nodup D) hselected
  intro intermediate hintermediate
  constructor
  · intro hsame
    exact ((supportedLabellingEqB_true_iff
      hselected hintermediate).mp hsame).symm
  · intro heq
    subst intermediate
    exact supportedLabellingEqB_true_of_eq D.faceEdges rfl

/-! ## 2. Forgetting the retained sector -/

/-- Coarse states are kept; retained fine states are sent through precisely
the null-completion row used by the old total kernel. -/
def allCutoffRetainedForgetKernel
    (S : SlabScalePair) (retained : AllCutoffRetainedTarget)
    (coarseState : EdgeLabelling) : Q' :=
  match retained with
  | .inl intermediate =>
      supportedDirac S.coarse.faceEdges intermediate coarseState
  | .inr fineSource =>
      nullCompletionKernel S fineSource.1 coarseState

theorem allCutoffRetainedForgetKernel_nonnegative
    (S : SlabScalePair) (retained : AllCutoffRetainedTarget)
    (coarseState : EdgeLabelling) :
    (0 : Q') ≤
      allCutoffRetainedForgetKernel S retained coarseState := by
  cases retained with
  | inl intermediate =>
      exact supportedDirac_nonnegative
        S.coarse.faceEdges intermediate coarseState
  | inr fineSource =>
      exact nullCompletionKernel_nonnegative
        S fineSource.1 coarseState

theorem allCutoffRetainedForgetKernel_row_normalized
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    {retained : AllCutoffRetainedTarget}
    (hretained : retained ∈ allCutoffRetainedTargets S) :
    listQSum
        (allCutoffRetainedForgetKernel S retained)
        S.coarse.physicalLabellings ≈ 1 := by
  cases retained with
  | inl intermediate =>
      have hintermediate : intermediate ∈
          S.coarse.physicalLabellings := by
        unfold allCutoffRetainedTargets at hretained
        rcases List.mem_append.mp hretained with hleft | hright
        · obtain ⟨state, hstate, heq⟩ := List.mem_map.mp hleft
          injection heq with heq'
          exact heq' ▸ hstate
        · obtain ⟨fineSource, _, heq⟩ := List.mem_map.mp hright
          cases heq
      exact supportedDirac_slab_row_normalized
        S.coarse hintermediate
  | inr fineSource =>
      exact allCutoffNullCompletionKernel_row_normalized
        S hfineCutoff fineSource.1

/-! ## 3. Retained rows collapse to their old null row -/

private theorem retainedSamePhysicalStateKernel_mul_null_eqv
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (coarseState : EdgeLabelling)
    (retained : EdgeLabelling × SlabFusionWitnessAssignment)
    (hretained : retained ∈ slabExpandedFineSources S.fine) :
    retainedSamePhysicalStateKernel source hpositive retained *
        nullCompletionKernel S retained.1 coarseState ≈
      retainedSamePhysicalStateKernel source hpositive retained *
        nullCompletionKernel S source.1 coarseState := by
  by_cases hcode :
      slabPhysicalStateCode S.fine retained.1 =
        slabPhysicalStateCode S.fine source.1
  · have hphysical : retained.1 ∈ S.fine.physicalLabellings :=
      (mem_slabExpandedFineSources_iff.mp hretained).1
    have heq : retained.1 = source.1 :=
      slabPhysicalStateCode_injective_on_carrier
        hphysical source.2 hcode
    rw [heq]
    exact Q'.eqv_refl _
  · have hzero :
        retainedSamePhysicalStateKernel source hpositive retained = 0 := by
      unfold retainedSamePhysicalStateKernel
      rw [if_neg hcode]
    rw [hzero]
    exact Q'.eqv_trans _ 0 _
      (Q'.zero_mul_eqv _)
      (Q'.eqv_symm (Q'.zero_mul_eqv _))

theorem retainedSamePhysicalStateKernel_forget_eqv_null
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (coarseState : EdgeLabelling) :
    listQSum
        (fun retained =>
          retainedSamePhysicalStateKernel source hpositive retained *
            nullCompletionKernel S retained.1 coarseState)
        (slabExpandedFineSources S.fine) ≈
      nullCompletionKernel S source.1 coarseState := by
  refine Q'.eqv_trans _
    (listQSum
      (fun retained =>
        retainedSamePhysicalStateKernel source hpositive retained *
          nullCompletionKernel S source.1 coarseState)
      (slabExpandedFineSources S.fine)) _ ?_ ?_
  · apply listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
    intro retained hretained
    exact retainedSamePhysicalStateKernel_mul_null_eqv
      S source hpositive coarseState retained hretained
  refine Q'.eqv_trans _
    (listQSum
        (retainedSamePhysicalStateKernel source hpositive)
        (slabExpandedFineSources S.fine) *
      nullCompletionKernel S source.1 coarseState) _ ?_ ?_
  · exact listQSum_mul_right _ _ _
  · refine Q'.eqv_trans _
      (1 * nullCompletionKernel S source.1 coarseState) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (retainedSamePhysicalStateKernel_row_normalized
          source hpositive)
    · exact Q'.one_mul_eqv _

/-! ## 4. The commuting row-level projection square -/

def allCutoffRetainedForgottenKernel
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (coarseState : EdgeLabelling) : Q' :=
  listQSum
    (fun retained =>
      allCutoffRetainedFineIntertwinerKernel S source retained *
        allCutoffRetainedForgetKernel S retained coarseState)
    (allCutoffRetainedTargets S)

/-- Forgetting the explicit retained fine-intertwiner sector recovers exactly
the former total four-preimage kernel, including its null fallback. -/
theorem allCutoffRetainedForgottenKernel_eqv_allCutoffWholeSlabKernel
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (coarseState : EdgeLabelling)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    allCutoffRetainedForgottenKernel S source coarseState ≈
      allCutoffWholeSlabKernel S source.1 coarseState := by
  unfold allCutoffRetainedForgottenKernel allCutoffRetainedTargets
  refine Q'.eqv_trans _
    (listQSum
        (fun retained =>
          allCutoffRetainedFineIntertwinerKernel S source retained *
            allCutoffRetainedForgetKernel S retained coarseState)
        (S.coarse.physicalLabellings.map Sum.inl) +
      listQSum
        (fun retained =>
          allCutoffRetainedFineIntertwinerKernel S source retained *
            allCutoffRetainedForgetKernel S retained coarseState)
        ((slabExpandedFineSources S.fine).map Sum.inr)) _
    (listQSum_append _ _ _) ?_
  rw [listQSum_map, listQSum_map]
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm source.1
  · by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S source.1
    · refine Q'.eqv_trans _
        (listQSum
          (fun intermediate =>
            wholeSlabRecouplingConditionalKernel
                (coherentSlabRecouplingSourceOfRawPartitionPos
                  S source.1 source.2 hpartition) intermediate *
              supportedDirac S.coarse.faceEdges intermediate coarseState)
          S.coarse.physicalLabellings + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (listQSum_congr_on _ _ S.coarse.physicalLabellings
            (fun intermediate _ => by
              rw [allCutoffRetainedFineIntertwinerKernel_eq_recoupling
                S source hpositive hpartition]
              exact Q'.eqv_refl _))
          (Q'.eqv_trans _ _ _
            (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
              (fun retained _ => by
                rw [allCutoffRetainedFineIntertwinerKernel_retained_zero_of_coherent
                  S source hpositive hpartition]
                exact Q'.zero_mul_eqv _))
            (listQSum_zero _))
      refine Q'.eqv_trans _
        (wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S source.1 source.2 hpartition) coarseState + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (listQSum_mul_supportedDirac_eqv S.coarse _ hcoarse)
          (Q'.eqv_refl 0)
      refine Q'.eqv_trans _
        (wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S source.1 source.2 hpartition) coarseState) _
        (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
      exact Q'.eqv_symm (Q'.eqv_of_eq
        (allCutoffWholeSlabKernel_eq_recoupling
          S source.2 hpositive hpartition coarseState))
    · refine Q'.eqv_trans _
        (0 + listQSum
          (fun retained =>
            retainedSamePhysicalStateKernel source hpositive retained *
              nullCompletionKernel S retained.1 coarseState)
          (slabExpandedFineSources S.fine)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (listQSum_congr_on _ _ S.coarse.physicalLabellings
              (fun intermediate _ => by
                rw [allCutoffRetainedFineIntertwinerKernel_coarse_zero_of_incoherent
                  S source hpositive hpartition]
                exact Q'.zero_mul_eqv _))
            (listQSum_zero _))
          (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
            (fun retained _ => by
              rw [allCutoffRetainedFineIntertwinerKernel_eq_retained_of_incoherent
                S source hpositive hpartition]
              exact Q'.eqv_refl _))
      refine Q'.eqv_trans _
        (0 + nullCompletionKernel S source.1 coarseState) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl 0)
          (retainedSamePhysicalStateKernel_forget_eqv_null
            S source hpositive coarseState)
      refine Q'.eqv_trans _
        (nullCompletionKernel S source.1 coarseState) _
        (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
      exact Q'.eqv_symm (Q'.eqv_of_eq
        (allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
          S source.2 hpositive hpartition coarseState))
  · refine Q'.eqv_trans _
      (listQSum
        (fun intermediate =>
          nullCompletionKernel S source.1 intermediate *
            supportedDirac S.coarse.faceEdges intermediate coarseState)
        S.coarse.physicalLabellings + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (listQSum_congr_on _ _ S.coarse.physicalLabellings
          (fun intermediate _ => by
            unfold allCutoffRetainedFineIntertwinerKernel
              allCutoffRetainedForgetKernel
            rw [dif_neg hpositive]
            exact Q'.eqv_refl _))
        (Q'.eqv_trans _ _ _
          (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
            (fun retained _ => by
              unfold allCutoffRetainedFineIntertwinerKernel
                allCutoffRetainedForgetKernel
              rw [dif_neg hpositive]
              exact Q'.zero_mul_eqv _))
          (listQSum_zero _))
    refine Q'.eqv_trans _
      (nullCompletionKernel S source.1 coarseState + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (listQSum_mul_supportedDirac_eqv S.coarse _ hcoarse)
        (Q'.eqv_refl 0)
    refine Q'.eqv_trans _
      (nullCompletionKernel S source.1 coarseState) _
      (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq
      (allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
        S source.2 hpositive coarseState))

/-! ## Axiom audit -/

#print axioms listQSum_mul_supportedDirac_eqv
#print axioms allCutoffRetainedForgetKernel_nonnegative
#print axioms allCutoffRetainedForgetKernel_row_normalized
#print axioms retainedSamePhysicalStateKernel_forget_eqv_null
#print axioms allCutoffRetainedForgottenKernel_eqv_allCutoffWholeSlabKernel

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerProjection
