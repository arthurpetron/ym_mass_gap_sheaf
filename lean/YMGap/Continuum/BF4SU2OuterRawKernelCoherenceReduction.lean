/-
# Minimal cutoff coherence for the physical BF4 SU(2) raw kernel

The explicit all-cutoff kernel in
`BF4SU2OuterPhysicalMarkovKernelFrontier` is nonnegative and row
normalized on nested finite target carriers.  Consequently its
`old_source_no_new_target` field is not an independent physical input:
old-entry stability alone forces the total mass of the new sector to be
zero, and nonnegativity then forces every new entry to vanish.

This module makes that redundancy constructive.  The sharper frontier
`SU2OuterRawKernelCutoffStability` has one field, `cutoff_stable`.  It
canonically produces the earlier two-field
`SU2OuterRawKernelCutoffCoherence`, and hence the physical Markov contract.

Two adversarial fences rule out hidden completions:

* changing the positive coarse witness in `SU2OuterPositiveRowClosure`
  cannot change any kernel entry on a physical source; the normalized
  raw row depends only on the fine source;
* a Gibbs-null fine row has exactly zero normalized source mass, so any
  bookkeeping completion on that row contributes zero to every physical
  pushforward.

Thus cutoff-one recovery and normalization do not hide an additional
positive-mass completion.  This module isolates two inputs: (i) positive
raw-row closure and (ii) old-entry stability for the explicit BF4 raw
formula.  The subsequent
`BF4SU2OuterRawKernelCutoffDiagnostics` module derives (ii) from (i), leaving
positive-row closure as the sole raw-kernel input.  Neither module constructs
that physical nonvanishing datum.

## Axiom gate

Finite `List`, `Nat`, `Bool`, and `Q'` algebra only.  No classical
principle, native decision shortcut, custom axiom, hidden proof hole,
functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier

namespace
  YMGap.Continuum.BF4SU2OuterRawKernelCoherenceReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Hidden-completion fences -/

/-- The normalized positive raw row is independent of which positive
coarse witness was used to certify its denominator.  Null rows use the
same explicit bookkeeping completion. -/
theorem outerWholeSlabKernel_closure_independent_on_physical
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (left right :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (target : OuterSlabLabelling) :
    outerWholeSlabKernel left K source target ≈
      outerWholeSlabKernel right K source target := by
  by_cases hpositive :
      (0 : Q') <
        (su2FineOuterData G g hg K).physicalTerm source
  · refine Q'.eqv_trans _
      (wholeSlabRecouplingConditionalKernel
        (left.coherentSource
          K source hsource hpositive)
        target) _ ?_ ?_
    · exact outerWholeSlabKernel_eq_positive
        left K hsource hpositive target
    refine Q'.eqv_trans _
      (wholeSlabRecouplingConditionalKernel
        (right.coherentSource
          K source hsource hpositive)
        target) _ ?_ ?_
    · apply wholeSlabConditionalKernel_eq_of_fineState_eq
        (left.coherentSource
          K source hsource hpositive)
        (right.coherentSource
          K source hsource hpositive)
      · unfold SU2OuterPositiveRowClosure.coherentSource
        split <;> rfl
    · exact Q'.eqv_symm
        (outerWholeSlabKernel_eq_positive
          right K hsource hpositive target)
  · rw [outerWholeSlabKernel_eq_null
      left K hsource hpositive target]
    rw [outerWholeSlabKernel_eq_null
      right K hsource hpositive target]
    exact Q'.eqv_refl _

/-- A Gibbs-null row contributes exactly zero to every pushed target,
independently of its bookkeeping Markov completion. -/
theorem outerWholeSlabKernel_null_source_contribution_eqv_zero
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    (source target : OuterSlabLabelling)
    (hnotPositive :
      ¬ (0 : Q') <
        (su2FineOuterData G g hg K).physicalTerm source) :
    (su2FineOuterData G g hg K).normalizedMass source *
        outerWholeSlabKernel closure K source target ≈
      0 := by
  refine Q'.eqv_trans _
    (0 * outerWholeSlabKernel
      closure K source target) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (normalizedMass_eqv_zero_of_not_positive
        (su2FineOuterData G g hg K)
        source hnotPositive)
  · exact Q'.zero_mul_eqv _

/-- The explicit total raw kernel is nonnegative even away from the listed
target carrier.  The carrier hypotheses in the earlier public theorem are
needed by the Markov interface, not by pointwise positivity itself. -/
theorem outerWholeSlabKernel_nonnegative_all_targets
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    (source target : OuterSlabLabelling) :
    (0 : Q') ≤
      outerWholeSlabKernel closure K source target := by
  unfold outerWholeSlabKernel
  dsimp only
  split
  · split
    · exact
        wholeSlabRecouplingConditionalKernel_nonnegative
          _ target
    · exact outerNullCompletion_nonnegative
        G g hg candidate hcandidate K _ target
  · exact outerNullCompletion_nonnegative
      G g hg candidate hcandidate K source target

/-! ## 2. Finite constructive cancellation tools -/

private theorem outerRaw_range_nodup :
    ∀ N : Nat, (List.range N).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨outerRaw_range_nodup N,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl N)
        (List.mem_range.mp hleft)

private theorem outerRaw_faceEdges_nodup
    (extent : Nat) :
    (slabPhysicalFaceEdges extent).Nodup := by
  unfold slabPhysicalFaceEdges
  exact outerRaw_range_nodup _

private theorem listQSum_member_le_local
    {A : Type}
    (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items →
        value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on
            value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih :=
          listQSum_member_le_local
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have h :=
            Q'.add_le_add_right
              0 (value head)
              (listQSum value tail)
              (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem add_left_cancel_eqv_zero
    {base extra : Q'}
    (h : base + extra ≈ base) :
    extra ≈ 0 := by
  have hshift :
      (base + extra) + (-base) ≈
        base + (-base) :=
    Q'.add_eqv_congr_right
      (base + extra) base (-base) h
  have hleft :
      (base + extra) + (-base) ≈ extra := by
    refine Q'.eqv_trans _
      ((extra + base) + (-base)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right
        (base + extra) (extra + base) (-base)
        (Q'.add_comm_eqv base extra)
    refine Q'.eqv_trans _
      (extra + (base + (-base))) _ ?_ ?_
    · exact Q'.add_assoc_eqv extra base (-base)
    refine Q'.eqv_trans _
      (extra + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left
        extra (base + (-base)) 0
        (Q'.add_neg_self_eqv base)
    · exact Q'.eqv_of_eq (Q'.add_zero' extra)
  exact Q'.eqv_trans extra
    ((base + extra) + (-base)) 0
    (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _
      hshift
      (Q'.add_neg_self_eqv base))

private theorem old_source_mem_larger_cutoff
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {K L : Nat} (hKL : K ≤ L)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    source ∈
      (su2FineOuterData G g hg L).physicalLabellings := by
  have hsound :
      (∀ edge,
          edge ∈
              slabPhysicalFaceEdges
                (centralExtent G.fineHalf) →
            source edge < K + 1) ∧
        (∀ edge,
          edge ∉
              slabPhysicalFaceEdges
                (centralExtent G.fineHalf) →
            source edge = 0) := by
    exact boundedEdgeLabellings_sound K
      (slabPhysicalFaceEdges
        (centralExtent G.fineHalf))
      source hsource
  apply boundedEdgeLabellings_complete L
  · intro edge hedge
    exact Nat.lt_of_lt_of_le
      (hsound.1 edge hedge)
      (Nat.add_le_add_right hKL 1)
  · exact hsound.2

/-! ## 3. The one-field intermediate raw-kernel frontier -/

/-- **MINIMAL INTERMEDIATE INTERFACE.** Old entries of the explicit normalized
BF4 raw kernel are unchanged when the fine and induced coarse cutoffs are
enlarged.

Unlike `SU2OuterRawKernelCutoffCoherence`, no separate zero-on-new-targets
field is assumed.  That law follows from this field, finite carrier nesting,
nonnegativity, and row normalization.  The subsequent cutoff-diagnostics
module constructs this interface from `SU2OuterPositiveRowClosure`. -/
structure SU2OuterRawKernelCutoffStability
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate) : Type where
  cutoff_stable :
    ∀ K L source target,
      K ≤ L →
      source ∈
          (su2FineOuterData
            G g hg K).physicalLabellings →
      target ∈
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings →
        outerWholeSlabKernel closure K source target ≈
          outerWholeSlabKernel closure L source target

/-- Old-entry stability plus stochastic normalization constructively forces
every newly admitted target entry to vanish. -/
theorem old_source_no_new_target_of_cutoff_stable
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (stability :
      SU2OuterRawKernelCutoffStability closure) :
    ∀ K L source target,
      K ≤ L →
      source ∈
          (su2FineOuterData
            G g hg K).physicalLabellings →
      target ∈
          (su2CoarseOuterData
            G candidate hcandidate L).physicalLabellings →
      target ∉
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings →
        outerWholeSlabKernel closure L source target ≈ 0 := by
  intro K L source target hKL hsource htarget htargetNew
  let edges :=
    slabPhysicalFaceEdges
      (centralExtent G.coarseHalf)
  let smallSupport :=
    boundedEdgeLabellings (4 * K) edges
  let largeSupport :=
    boundedEdgeLabellings (4 * L) edges
  let oldTest :=
    labelWithinB (4 * K) edges
  let weightK : OuterSlabLabelling → Q' :=
    outerWholeSlabKernel closure K source
  let weightL : OuterSlabLabelling → Q' :=
    outerWholeSlabKernel closure L source
  change target ∈ largeSupport at htarget
  change target ∉ smallSupport at htargetNew
  have hsourceL :
      source ∈
        (su2FineOuterData
          G g hg L).physicalLabellings :=
    old_source_mem_larger_cutoff hKL hsource
  have h4KL : 4 * K ≤ 4 * L := by omega
  have hfilter :
      largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, edges]
    exact boundedEdgeLabellings_filter_cutoff
      h4KL _
      (outerRaw_faceEdges_nodup
        (centralExtent G.coarseHalf))
  have hold :
      listQSum weightL
          (largeSupport.filter oldTest) ≈
        listQSum weightK smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro oldTarget holdTarget
    exact Q'.eqv_symm
      (stability.cutoff_stable
        K L source oldTarget hKL hsource holdTarget)
  have hsplit :
      listQSum weightL largeSupport ≈
        listQSum weightL
            (largeSupport.filter oldTest) +
          listQSum weightL
            (largeSupport.filter
              (fun newTarget => !(oldTest newTarget))) :=
    listQSum_filter_partition
      weightL oldTest largeSupport
  have hrowK :
      listQSum weightK smallSupport ≈ 1 :=
    outerWholeSlabKernel_row_normalized
      closure K hsource
  have hrowL :
      listQSum weightL largeSupport ≈ 1 :=
    outerWholeSlabKernel_row_normalized
      closure L hsourceL
  have hsum :
      listQSum weightL
            (largeSupport.filter oldTest) +
          listQSum weightL
            (largeSupport.filter
              (fun newTarget => !(oldTest newTarget))) ≈
        listQSum weightL
          (largeSupport.filter oldTest) := by
    refine Q'.eqv_trans _
      (listQSum weightL largeSupport) _ ?_ ?_
    · exact Q'.eqv_symm hsplit
    refine Q'.eqv_trans _ 1 _ hrowL ?_
    refine Q'.eqv_trans _
      (listQSum weightK smallSupport) _ ?_ ?_
    · exact Q'.eqv_symm hrowK
    · exact Q'.eqv_symm hold
  have hnewSumZero :
      listQSum weightL
          (largeSupport.filter
            (fun newTarget => !(oldTest newTarget))) ≈
        0 :=
    add_left_cancel_eqv_zero hsum
  have holdTestFalse :
      oldTest target = false := by
    cases holdTest : oldTest target with
    | false => rfl
    | true =>
        exfalso
        apply htargetNew
        rw [← hfilter]
        exact List.mem_filter.mpr
          ⟨htarget, holdTest⟩
  have htargetFiltered :
      target ∈
        largeSupport.filter
          (fun newTarget => !(oldTest newTarget)) := by
    apply List.mem_filter.mpr
    exact ⟨htarget, by simp [holdTestFalse]⟩
  have hweightNonnegative :
      ∀ newTarget,
        (0 : Q') ≤ weightL newTarget := by
    intro newTarget
    dsimp only [weightL]
    exact outerWholeSlabKernel_nonnegative_all_targets
      closure L source newTarget
  have htargetLeSum :
      weightL target ≤
        listQSum weightL
          (largeSupport.filter
            (fun newTarget => !(oldTest newTarget))) :=
    listQSum_member_le_local
      weightL hweightNonnegative
      (largeSupport.filter
        (fun newTarget => !(oldTest newTarget)))
      htargetFiltered
  exact ExpNeg.eqv_of_le_le
    (Q'.le_trans' _ _ _
      htargetLeSum
      (Q'.le_of_eqv hnewSumZero))
    (hweightNonnegative target)

/-- The previous two-field coherence interface is a derived package. -/
def SU2OuterRawKernelCutoffStability.toCoherence
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    {closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate}
    (stability :
      SU2OuterRawKernelCutoffStability closure) :
    SU2OuterRawKernelCutoffCoherence closure where
  cutoff_stable := stability.cutoff_stable
  old_source_no_new_target :=
    old_source_no_new_target_of_cutoff_stable
      closure stability

/-- The physical Markov contract therefore needs only positive-row closure
and old-entry stability of the explicit raw kernel. -/
def physicalMarkovContractOfRawKernelCutoffStability
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (stability :
      SU2OuterRawKernelCutoffStability closure) :
    SU2OuterPhysicalMarkovContract
      G g hg candidate hcandidate :=
  physicalMarkovContractOfRawKernel
    closure stability.toCoherence

#print axioms
  outerWholeSlabKernel_closure_independent_on_physical
#print axioms
  outerWholeSlabKernel_null_source_contribution_eqv_zero
#print axioms outerWholeSlabKernel_nonnegative_all_targets
#print axioms SU2OuterRawKernelCutoffStability
#print axioms old_source_no_new_target_of_cutoff_stable
#print axioms SU2OuterRawKernelCutoffStability.toCoherence
#print axioms
  physicalMarkovContractOfRawKernelCutoffStability

end
  YMGap.Continuum.BF4SU2OuterRawKernelCoherenceReduction
