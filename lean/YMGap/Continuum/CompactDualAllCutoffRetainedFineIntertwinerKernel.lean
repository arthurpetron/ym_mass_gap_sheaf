/-
# A lossless all-cutoff kernel with a retained fine-intertwiner sector

The four-preimage coarse carrier is not closed at cutoff two: a positive
physical collar row has zero raw recoupling partition.  The missing datum is
already present before that projection, in the literal finite list of global
fine link-intertwiner assignments.

This module therefore uses a disjoint enriched target.  A coherent positive
row lands in the ordinary coarse recoupling sector.  An incoherent positive
row lands in a retained `(fineState, assignment)` sector and is distributed
by the exact normalized Haar-fiber conditional law.  A Gibbs-null row uses
the existing coarse null completion.  The three cases are disjoint, each row
is nonnegative, and each row has exact mass one.

The resulting pushed law is a genuine finite probability law.  No claim is
made that the enriched carrier is yet a repeated same-object RG carrier, that
reflection has been lifted to its retained sector, or that any posterior,
spectral, continuum, or Clay obligation is closed.

## Axiom gate

Finite list algebra, exact rational normalization, and a mixed-radix key on
the literal bounded face carrier only.  No classical choice, placeholder,
trusted external computation, computability escape, heartbeat increase, or
new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffTotalKernel
import YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
import YMGap.Continuum.BF4FiveHolonomyNormalizedKernel

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The disjoint finite carrier -/

/-- A physical row together with its literal membership witness. -/
abbrev SlabPhysicalSourceEntry (D : SlabPhysicalData) :=
  {state : EdgeLabelling // state ∈ D.physicalLabellings}

def slabPhysicalSourceEntries (D : SlabPhysicalData) :
    List (SlabPhysicalSourceEntry D) :=
  D.physicalLabellings.attach

/-- The corrected target is a disjoint sum: an ordinary coarse state, or a
fine physical state together with one accepted global link-intertwiner
assignment. -/
abbrev AllCutoffRetainedTarget :=
  Sum EdgeLabelling (EdgeLabelling × SlabFusionWitnessAssignment)

def allCutoffRetainedTargets (S : SlabScalePair) :
    List AllCutoffRetainedTarget :=
  S.coarse.physicalLabellings.map Sum.inl ++
    (slabExpandedFineSources S.fine).map Sum.inr

theorem slabPhysicalSourceEntries_nodup (D : SlabPhysicalData) :
    (slabPhysicalSourceEntries D).Nodup := by
  exact attach_nodup_of_nodup D.physicalLabellings
    (slabPhysicalLabellings_nodup D)

private theorem nodup_map_inl {A B : Type} :
    ∀ (items : List A), items.Nodup →
      (items.map (Sum.inl : A → Sum A B)).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        injection heq with heq'
        exact hparts.1 (heq' ▸ hitem)
      · exact nodup_map_inl tail hparts.2

private theorem nodup_map_inr {A B : Type} :
    ∀ (items : List B), items.Nodup →
      (items.map (Sum.inr : B → Sum A B)).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        injection heq with heq'
        exact hparts.1 (heq' ▸ hitem)
      · exact nodup_map_inr tail hparts.2

theorem allCutoffRetainedTargets_nodup (S : SlabScalePair) :
    (allCutoffRetainedTargets S).Nodup := by
  unfold allCutoffRetainedTargets
  apply List.nodup_append.mpr
  refine ⟨nodup_map_inl _ (slabPhysicalLabellings_nodup S.coarse),
    nodup_map_inr _ (slabExpandedFineSources_nodup S.fine), ?_⟩
  intro target hcoarse retained hretained heq
  obtain ⟨coarseState, _, hcoarseEq⟩ := List.mem_map.mp hcoarse
  obtain ⟨fineSource, _, hretainedEq⟩ := List.mem_map.mp hretained
  rw [← hcoarseEq, ← hretainedEq] at heq
  cases heq

/-! ## 2. A faithful decidable key for the physical part -/

def slabPhysicalStateCode
    (D : SlabPhysicalData) (state : EdgeLabelling) : Nat :=
  edgeLabellingCode (D.cutoff + 1) D.faceEdges state

theorem slabPhysicalStateCode_injective_on_carrier
    {D : SlabPhysicalData} {left right : EdgeLabelling}
    (hleft : left ∈ D.physicalLabellings)
    (hright : right ∈ D.physicalLabellings)
    (hcode : slabPhysicalStateCode D left =
      slabPhysicalStateCode D right) :
    left = right := by
  have hleftSound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges left hleft
  have hrightSound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges right hright
  exact edgeLabellingCode_injective_on_bounded
    (Nat.zero_lt_succ D.cutoff)
    hleftSound.1 hrightSound.1 hleftSound.2 hrightSound.2 hcode

/-! ## 3. Exact retained-Haar row on the expanded carrier -/

def retainedSourceOfPhysicalEntry
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1) :
    RetainedFineIntertwinerSource D :=
  { fineState := source.1
    fineState_mem := source.2
    physicalTerm_pos := hpositive }

/-- The exact conditional Haar row, extended by zero from the source's
physical block to the complete expanded carrier using a faithful finite key. -/
def retainedSamePhysicalStateKernel
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1)
    (target : EdgeLabelling × SlabFusionWitnessAssignment) : Q' :=
  if slabPhysicalStateCode D target.1 =
      slabPhysicalStateCode D source.1 then
    retainedFineIntertwinerConditionalKernel
      (retainedSourceOfPhysicalEntry source hpositive) target.2
  else
    0

theorem retainedSamePhysicalStateKernel_nonnegative
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1)
    (target : EdgeLabelling × SlabFusionWitnessAssignment) :
    (0 : Q') ≤ retainedSamePhysicalStateKernel source hpositive target := by
  unfold retainedSamePhysicalStateKernel
  split
  · exact retainedFineIntertwinerConditionalKernel_nonnegative _ _
  · exact Q'.le_refl' 0

private theorem listQSum_code_dirac_one
    {A : Type} (code : A → Nat) (selected : A) :
    ∀ (items : List A), items.Nodup → selected ∈ items →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        code left = code right → left = right) →
      listQSum
          (fun item => if code item = code selected then (1 : Q') else 0)
          items ≈ 1
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : code head = code selected
      · have heq : head = selected :=
          hinjective head List.mem_cons_self selected hmem hhead
        subst head
        have htailZero :
            listQSum
                (fun item =>
                  if code item = code selected then (1 : Q') else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _ : A => (0 : Q')) tail) _ ?_ (listQSum_zero tail)
          apply listQSum_congr_on _ _ tail
          intro item hitem
          have hne : code item ≠ code selected := by
            intro hcode
            have hitemEq : item = selected :=
              hinjective item (List.mem_cons_of_mem selected hitem)
                selected List.mem_cons_self hcode
            subst item
            exact hparts.1 hitem
          rw [if_neg hne]
          exact Q'.eqv_refl 0
        simp only [listQSum, if_true]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 1) htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' 1))
      · have hselectedTail : selected ∈ tail := by
          rcases List.mem_cons.mp hmem with hselectedHead | htail
          · subst head
            exact False.elim (hhead rfl)
          · exact htail
        have htailInjective :
            ∀ left, left ∈ tail → ∀ right, right ∈ tail →
              code left = code right → left = right := by
          intro left hleft right hright hcode
          exact hinjective left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) hcode
        simp only [listQSum, if_neg hhead]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 0)
            (listQSum_code_dirac_one code selected tail hparts.2
              hselectedTail htailInjective))
          (Q'.eqv_of_eq (Q'.zero_add' 1))

theorem retainedSamePhysicalStateKernel_block
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1)
    (physical : EdgeLabelling)
    (hphysical : physical ∈ D.physicalLabellings) :
    listQSum
        (retainedSamePhysicalStateKernel source hpositive)
        (slabExpandedFineSourceBlock D physical) ≈
      if slabPhysicalStateCode D physical =
          slabPhysicalStateCode D source.1 then 1 else 0 := by
  unfold slabExpandedFineSourceBlock
  rw [listQSum_map]
  by_cases hcode : slabPhysicalStateCode D physical =
      slabPhysicalStateCode D source.1
  · have heq : physical = source.1 :=
      slabPhysicalStateCode_injective_on_carrier hphysical source.2 hcode
    subst physical
    rw [if_pos hcode]
    refine Q'.eqv_trans _
      (listQSum
        (retainedFineIntertwinerConditionalKernel
          (retainedSourceOfPhysicalEntry source hpositive))
        (slabFineFusionWitnesses D source.1)) _ ?_ ?_
    · apply listQSum_congr
      intro assignment
      unfold retainedSamePhysicalStateKernel
      rw [if_pos rfl]
      exact Q'.eqv_refl _
    · exact retainedFineIntertwinerConditionalKernel_row_normalized _
  · rw [if_neg hcode]
    refine Q'.eqv_trans _
      (listQSum (fun _ : SlabFusionWitnessAssignment => (0 : Q'))
        (slabFineFusionWitnesses D physical)) _ ?_ ?_
    · apply listQSum_congr
      intro assignment
      unfold retainedSamePhysicalStateKernel
      rw [if_neg hcode]
      exact Q'.eqv_refl 0
    · exact listQSum_zero _

/-- The zero-extended retained Haar row has exact mass one on the complete
expanded source carrier. -/
theorem retainedSamePhysicalStateKernel_row_normalized
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1) :
    listQSum
        (retainedSamePhysicalStateKernel source hpositive)
        (slabExpandedFineSources D) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        listQSum
          (retainedSamePhysicalStateKernel source hpositive)
          (slabExpandedFineSourceBlock D physical))
      D.physicalLabellings) _ ?_ ?_
  · unfold slabExpandedFineSources
    exact listQSum_flatMap _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        if slabPhysicalStateCode D physical =
            slabPhysicalStateCode D source.1 then (1 : Q') else 0)
      D.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on _ _ D.physicalLabellings
    intro physical hphysical
    exact retainedSamePhysicalStateKernel_block
      source hpositive physical hphysical
  · apply listQSum_code_dirac_one
      (slabPhysicalStateCode D) source.1 D.physicalLabellings
      (slabPhysicalLabellings_nodup D) source.2
    intro left hleft right hright hcode
    exact slabPhysicalStateCode_injective_on_carrier hleft hright hcode

/-! ## 4. The total enriched all-cutoff row -/

def allCutoffRetainedFineIntertwinerKernel
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (target : AllCutoffRetainedTarget) : Q' :=
  if hpositive : (0 : Q') < S.fine.physicalTerm source.1 then
    if hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1 then
      match target with
      | .inl coarseState =>
          wholeSlabRecouplingConditionalKernel
            (coherentSlabRecouplingSourceOfRawPartitionPos
              S source.1 source.2 hpartition) coarseState
      | .inr _ => 0
    else
      match target with
      | .inl _ => 0
      | .inr retained =>
          retainedSamePhysicalStateKernel source hpositive retained
  else
    match target with
    | .inl coarseState => nullCompletionKernel S source.1 coarseState
    | .inr _ => 0

theorem allCutoffRetainedFineIntertwinerKernel_eq_recoupling
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseState : EdgeLabelling) :
    allCutoffRetainedFineIntertwinerKernel S source (.inl coarseState) =
      wholeSlabRecouplingConditionalKernel
        (coherentSlabRecouplingSourceOfRawPartitionPos
          S source.1 source.2 hpartition) coarseState := by
  unfold allCutoffRetainedFineIntertwinerKernel
  rw [dif_pos hpositive, dif_pos hpartition]

theorem allCutoffRetainedFineIntertwinerKernel_retained_zero_of_coherent
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (retained : EdgeLabelling × SlabFusionWitnessAssignment) :
    allCutoffRetainedFineIntertwinerKernel S source (.inr retained) = 0 := by
  unfold allCutoffRetainedFineIntertwinerKernel
  rw [dif_pos hpositive, dif_pos hpartition]

theorem allCutoffRetainedFineIntertwinerKernel_coarse_zero_of_incoherent
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition : ¬ (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseState : EdgeLabelling) :
    allCutoffRetainedFineIntertwinerKernel S source (.inl coarseState) = 0 := by
  unfold allCutoffRetainedFineIntertwinerKernel
  rw [dif_pos hpositive, dif_neg hnotPartition]

theorem allCutoffRetainedFineIntertwinerKernel_eq_retained_of_incoherent
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition : ¬ (0 : Q') < wholeSlabRawRowPartition S source.1)
    (retained : EdgeLabelling × SlabFusionWitnessAssignment) :
    allCutoffRetainedFineIntertwinerKernel S source (.inr retained) =
      retainedSamePhysicalStateKernel source hpositive retained := by
  unfold allCutoffRetainedFineIntertwinerKernel
  rw [dif_pos hpositive, dif_neg hnotPartition]

theorem allCutoffRetainedFineIntertwinerKernel_nonnegative
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (target : AllCutoffRetainedTarget) :
    (0 : Q') ≤
      allCutoffRetainedFineIntertwinerKernel S source target := by
  unfold allCutoffRetainedFineIntertwinerKernel
  by_cases hpositive : (0 : Q') < S.fine.physicalTerm source.1
  · rw [dif_pos hpositive]
    by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S source.1
    · rw [dif_pos hpartition]
      cases target with
      | inl coarseState =>
          exact wholeSlabRecouplingConditionalKernel_nonnegative _ _
      | inr _ => exact Q'.le_refl' 0
    · rw [dif_neg hpartition]
      cases target with
      | inl _ => exact Q'.le_refl' 0
      | inr retained =>
          exact retainedSamePhysicalStateKernel_nonnegative
            source hpositive retained
  · rw [dif_neg hpositive]
    cases target with
    | inl coarseState =>
        exact nullCompletionKernel_nonnegative S source.1 coarseState
    | inr _ => exact Q'.le_refl' 0

/-- Every enriched row is exactly stochastic. -/
theorem allCutoffRetainedFineIntertwinerKernel_row_normalized
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (source : SlabPhysicalSourceEntry S.fine) :
    listQSum
        (allCutoffRetainedFineIntertwinerKernel S source)
        (allCutoffRetainedTargets S) ≈ 1 := by
  unfold allCutoffRetainedTargets
  refine Q'.eqv_trans _
    (listQSum
        (allCutoffRetainedFineIntertwinerKernel S source)
        (S.coarse.physicalLabellings.map Sum.inl) +
      listQSum
        (allCutoffRetainedFineIntertwinerKernel S source)
        ((slabExpandedFineSources S.fine).map Sum.inr)) _
    (listQSum_append _ _ _) ?_
  rw [listQSum_map, listQSum_map]
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm source.1
  · by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S source.1
    · refine Q'.eqv_trans _
        (listQSum
            (wholeSlabRecouplingConditionalKernel
              (coherentSlabRecouplingSourceOfRawPartitionPos
                S source.1 source.2 hpartition))
            S.coarse.physicalLabellings + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (listQSum_congr_on _ _ S.coarse.physicalLabellings
            (fun coarseState _ => by
              unfold allCutoffRetainedFineIntertwinerKernel
              rw [dif_pos hpositive, dif_pos hpartition]
              exact Q'.eqv_refl _))
          (Q'.eqv_trans _ _ _
            (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
              (fun retained _ => by
                unfold allCutoffRetainedFineIntertwinerKernel
                rw [dif_pos hpositive, dif_pos hpartition]
                exact Q'.eqv_refl 0))
            (listQSum_zero _))
      · exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (wholeSlabRecouplingConditionalKernel_row_normalized _)
            (Q'.eqv_refl 0))
          (Q'.eqv_of_eq (Q'.add_zero' 1))
    · refine Q'.eqv_trans _
        (0 + listQSum
          (retainedSamePhysicalStateKernel source hpositive)
          (slabExpandedFineSources S.fine)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (listQSum_congr_on _ _ S.coarse.physicalLabellings
              (fun coarseState _ => by
                unfold allCutoffRetainedFineIntertwinerKernel
                rw [dif_pos hpositive, dif_neg hpartition]
                exact Q'.eqv_refl 0))
            (listQSum_zero _))
          (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
            (fun retained _ => by
              unfold allCutoffRetainedFineIntertwinerKernel
              rw [dif_pos hpositive, dif_neg hpartition]
              exact Q'.eqv_refl _))
      · exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 0)
            (retainedSamePhysicalStateKernel_row_normalized source hpositive))
          (Q'.eqv_of_eq (Q'.zero_add' 1))
  · refine Q'.eqv_trans _
      (listQSum (nullCompletionKernel S source.1)
          S.coarse.physicalLabellings + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (listQSum_congr_on _ _ S.coarse.physicalLabellings
          (fun coarseState _ => by
            unfold allCutoffRetainedFineIntertwinerKernel
            rw [dif_neg hpositive]
            exact Q'.eqv_refl _))
        (Q'.eqv_trans _ _ _
          (listQSum_congr_on _ _ (slabExpandedFineSources S.fine)
            (fun retained _ => by
              unfold allCutoffRetainedFineIntertwinerKernel
              rw [dif_neg hpositive]
              exact Q'.eqv_refl 0))
          (listQSum_zero _))
    · exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (allCutoffNullCompletionKernel_row_normalized
            S hfineCutoff source.1)
          (Q'.eqv_refl 0))
        (Q'.eqv_of_eq (Q'.add_zero' 1))

/-! ## 5. Exact finite pushforward law -/

def allCutoffRetainedFineIntertwinerBlockedMass
    (S : SlabScalePair) (target : AllCutoffRetainedTarget) : Q' :=
  listQSum
    (fun source : SlabPhysicalSourceEntry S.fine =>
      S.fine.normalizedMass source.1 *
        allCutoffRetainedFineIntertwinerKernel S source target)
    (slabPhysicalSourceEntries S.fine)

theorem allCutoffRetainedFineIntertwinerBlockedMass_nonnegative
    (S : SlabScalePair) (target : AllCutoffRetainedTarget) :
    (0 : Q') ≤
      allCutoffRetainedFineIntertwinerBlockedMass S target := by
  unfold allCutoffRetainedFineIntertwinerBlockedMass
  apply listQSum_nonnegative_on
  intro source _
  exact Q'.mul_nonneg _ _
    (S.fine.normalizedMass_nonnegative source.1)
    (allCutoffRetainedFineIntertwinerKernel_nonnegative S source target)

/-- The pushed normalized Gibbs law has exact total mass one on the disjoint
enriched target carrier. -/
theorem allCutoffRetainedFineIntertwinerBlockedMass_total
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff) :
    listQSum
        (allCutoffRetainedFineIntertwinerBlockedMass S)
        (allCutoffRetainedTargets S) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source : SlabPhysicalSourceEntry S.fine =>
        listQSum
          (fun target =>
            S.fine.normalizedMass source.1 *
              allCutoffRetainedFineIntertwinerKernel S source target)
          (allCutoffRetainedTargets S))
      (slabPhysicalSourceEntries S.fine)) _ ?_ ?_
  · exact listQSum_swap
      (fun source : SlabPhysicalSourceEntry S.fine =>
        fun target : AllCutoffRetainedTarget =>
          S.fine.normalizedMass source.1 *
            allCutoffRetainedFineIntertwinerKernel S source target)
      (slabPhysicalSourceEntries S.fine)
      (allCutoffRetainedTargets S)
  refine Q'.eqv_trans _
    (listQSum
      (fun source : SlabPhysicalSourceEntry S.fine =>
        S.fine.normalizedMass source.1)
      (slabPhysicalSourceEntries S.fine)) _ ?_ ?_
  · apply listQSum_congr_on _ _ (slabPhysicalSourceEntries S.fine)
    intro source _
    exact Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (S.fine.normalizedMass source.1)
        (allCutoffRetainedFineIntertwinerKernel S source)
        (allCutoffRetainedTargets S))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (S.fine.normalizedMass source.1) _ _
          (allCutoffRetainedFineIntertwinerKernel_row_normalized
            S hfineCutoff source))
        (Q'.mul_one_eqv _))
  · exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (listQSum_attach S.fine.normalizedMass
          S.fine.physicalLabellings))
      (S.fine.normalizedMass_total)

/-! ## Axiom audit -/

#print axioms allCutoffRetainedTargets_nodup
#print axioms slabPhysicalStateCode_injective_on_carrier
#print axioms retainedSamePhysicalStateKernel_nonnegative
#print axioms retainedSamePhysicalStateKernel_row_normalized
#print axioms allCutoffRetainedFineIntertwinerKernel_eq_recoupling
#print axioms allCutoffRetainedFineIntertwinerKernel_eq_retained_of_incoherent
#print axioms allCutoffRetainedFineIntertwinerKernel_nonnegative
#print axioms allCutoffRetainedFineIntertwinerKernel_row_normalized
#print axioms allCutoffRetainedFineIntertwinerBlockedMass_nonnegative
#print axioms allCutoffRetainedFineIntertwinerBlockedMass_total

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
