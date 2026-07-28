/-
# Physical all-cutoff BF4 SU(2) Markov-kernel frontier

`SU2OuterPhysicalMarkovContract` deliberately exposes stochastic and
cutoff-coherence laws, but those laws alone do not identify its entries with
the BF4 recoupling formula.  In particular, a frozen cutoff-one kernel
together with Dirac completion on genuinely new sources can satisfy that
interface while discarding every positive higher-spin row.

This module closes that loophole.  It defines the all-cutoff scale pair and
the total kernel whose positive rows are *definitionally* the normalized
globally link-glued `wholeSlabRecouplingRawWeight`.  Null rows retain the
cutoff-one bookkeeping completion (with a vacuum completion at cutoff zero).

The genuine missing physical theorem is isolated as
`SU2OuterPositiveRowClosure`: every positive fine Gibbs row must construct a
coarse target with strictly positive complete raw recoupling weight.  Given
that witness family, nonnegativity, row normalization, and exact cutoff-one
recovery are proved here.  `SU2OuterRawKernelCutoffCoherence` then records
the two still-unproved finite fusion-support facts: old entries are stable
when the channel carrier is enlarged, and an old source has zero raw mass
on genuinely new `4L` targets.

No inhabitant of either open input is invented.

## Axiom gate

Finite `List`, `Nat`, `Bool`, and `Q'` algebra only.  No classical principle,
native decision shortcut, custom axiom, hidden proof hole, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
import YMGap.Continuum.CompactDualCutoffOneTotalKernel

namespace YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal all-cutoff scale pair -/

/-- Fine cutoff `K`, induced coarse cutoff `4K`, and the same corrected-slab
geometry and candidate coupling as the cutoff-one BF4 step. -/
def su2OuterScalePair
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat) : SlabScalePair where
  fine := su2FineOuterData G g hg K
  coarse := su2CoarseOuterData G candidate hcandidate K
  couplingFlow := fun _ => candidate
  fine_extent := G.extent_relation
  coarse_cutoff := rfl
  coarse_coupling := Q'.eqv_refl candidate

theorem su2OuterScalePair_one
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    su2OuterScalePair G g hg candidate hcandidate 1 =
      G.candidateScalePair g hg candidate hcandidate :=
  rfl

/-! ## 2. The genuine positive-row closure theorem -/

/-- **OPEN PHYSICAL INPUT.** Every positive fine Gibbs row away from the
already-closed cutoff-one anchor constructs one coarse labelling with
strictly positive complete BF4 whole-slab recoupling weight.

This is the direct higher-spin replacement for the cutoff-one binary-parity
surface theorem.  The known cutoff-one theorem is inserted by
`coherentSource`, not repeated as an assumption.  The remaining field cannot
be discharged by an arbitrary Dirac row: the witness is tested against
`wholeSlabRecouplingRawWeight` itself. -/
structure SU2OuterPositiveRowClosure
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  coarseWitness :
    ∀ K source,
      K ≠ 1 →
      source ∈
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalTerm source →
        OuterSlabLabelling
  coarseWitness_mem :
    ∀ K source hK hsource hpositive,
      coarseWitness K source hK hsource hpositive ∈
        (su2OuterScalePair
          G g hg candidate hcandidate K).coarse.physicalLabellings
  coarseWitness_positive :
    ∀ K source hK hsource hpositive,
      (0 : Q') <
        wholeSlabRecouplingRawWeight
          (su2OuterScalePair
            G g hg candidate hcandidate K)
          source
          (coarseWitness K source hK hsource hpositive)

/-- Package the physical positive target as the existing normalized-row
source type. -/
def SU2OuterPositiveRowClosure.coherentSource
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat) (source : OuterSlabLabelling)
    (hsource :
      source ∈
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalLabellings)
    (hpositive :
      (0 : Q') <
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalTerm source) :
    CoherentSlabRecouplingSource
      (su2OuterScalePair
        G g hg candidate hcandidate K) := by
  by_cases hK : K = 1
  · subst K
    exact positiveCoherentSource
      (su2OuterScalePair
        G g hg candidate hcandidate 1)
      rfl hcandidate source hsource hpositive
  · exact
      { fineState := source
        fine_mem := hsource
        coarseWitness :=
          closure.coarseWitness K source hK hsource hpositive
        coarseWitness_mem :=
          closure.coarseWitness_mem
            K source hK hsource hpositive
        coarseWitness_positive :=
          closure.coarseWitness_positive
            K source hK hsource hpositive }

/-! ## 3. Honest total kernel from the raw physical rows -/

/-- Null-row bookkeeping.  At positive cutoffs this is exactly the existing
reflection-compatible completion.  At cutoff zero the only selected target
is the vacuum, avoiding an unavailable spin-one target. -/
def outerNullCompletion
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (source target : OuterSlabLabelling) : Q' :=
  if K = 0 then
    supportedDirac
      (su2CoarseOuterData
        G candidate hcandidate K).faceEdges
      zeroEdgeLabelling target
  else
    nullCompletionKernel
      (su2OuterScalePair
        G g hg candidate hcandidate K)
      source target

theorem outerNullCompletion_nonnegative
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (source target : OuterSlabLabelling) :
    (0 : Q') ≤
      outerNullCompletion
        G g hg candidate hcandidate K source target := by
  unfold outerNullCompletion
  split
  · exact supportedDirac_nonnegative _ _ _
  · exact nullCompletionKernel_nonnegative _ _ _

theorem outerNullCompletion_row_normalized
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (source : OuterSlabLabelling) :
    listQSum
        (outerNullCompletion
          G g hg candidate hcandidate K source)
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings ≈
      1 := by
  by_cases hK : K = 0
  · subst K
    unfold outerNullCompletion
    simp only [if_pos]
    exact supportedDirac_slab_row_normalized
      (su2CoarseOuterData
        G candidate hcandidate 0)
      (zeroEdgeLabelling_mem_slab _)
  · unfold outerNullCompletion
    simp only [if_neg hK]
    unfold nullCompletionKernel
    split
    · exact supportedDirac_slab_row_normalized
        (su2CoarseOuterData
          G candidate hcandidate K)
        (fixedSingletonLabelling_mem _ (by
          change 1 ≤ 4 * K
          omega))
    · exact supportedDirac_slab_row_normalized
        (su2CoarseOuterData
          G candidate hcandidate K)
        (zeroEdgeLabelling_mem_slab _)

theorem outerNullCompletion_one
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (source target : OuterSlabLabelling) :
    outerNullCompletion
        G g hg candidate hcandidate 1 source target =
      nullCompletionKernel
        (G.candidateScalePair
          g hg candidate hcandidate)
        source target := by
  unfold outerNullCompletion
  have hone : (1 : Nat) ≠ 0 := by decide
  rw [if_neg hone]
  dsimp only [su2OuterScalePair, su2FineOuterData,
    su2CoarseOuterData, CutoffOneGeometry.candidateScalePair,
    CutoffOneGeometry.fineData, CutoffOneGeometry.coarseData]

/-- The actual all-cutoff total row.  On a positive restricted source this
is the normalized complete whole-slab BF4 raw weight; only Gibbs-null rows
use `outerNullCompletion`. -/
def outerWholeSlabKernel
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    (source target : OuterSlabLabelling) : Q' :=
  let S :=
    su2OuterScalePair
      G g hg candidate hcandidate K
  if hbounded :
      slabCoordinatesBoundedB S.fine source = true then
    let restricted := restrictToSlabSupport S.fine source
    let hrestricted :=
      restrictToSlabSupport_mem_of_bounded S.fine hbounded
    if hpositive :
        (0 : Q') < S.fine.physicalTerm restricted then
      wholeSlabRecouplingConditionalKernel
        (closure.coherentSource
          K restricted hrestricted hpositive)
        target
    else
      outerNullCompletion
        G g hg candidate hcandidate K restricted target
  else
    outerNullCompletion
      G g hg candidate hcandidate K source target

theorem outerWholeSlabKernel_eq_positive
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData
          G g hg K).physicalLabellings)
    (hpositive :
      (0 : Q') <
        (su2FineOuterData
          G g hg K).physicalTerm source)
    (target : OuterSlabLabelling) :
    outerWholeSlabKernel closure K source target ≈
      wholeSlabRecouplingConditionalKernel
        (closure.coherentSource
          K source hsource hpositive)
        target := by
  unfold outerWholeSlabKernel
  dsimp only [su2OuterScalePair]
  rw [dif_pos
    (slabCoordinatesBoundedB_true_of_mem
      (su2FineOuterData G g hg K) hsource)]
  have hrestrict :=
    restrictToSlabSupport_eq_of_mem
      (su2FineOuterData G g hg K) hsource
  simp only [hrestrict]
  rw [dif_pos hpositive]
  exact Q'.eqv_refl _

theorem outerWholeSlabKernel_eq_null
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData
          G g hg K).physicalLabellings)
    (hnotPositive :
      ¬ (0 : Q') <
        (su2FineOuterData
          G g hg K).physicalTerm source)
    (target : OuterSlabLabelling) :
    outerWholeSlabKernel closure K source target =
      outerNullCompletion
        G g hg candidate hcandidate K source target := by
  unfold outerWholeSlabKernel
  dsimp only [su2OuterScalePair]
  rw [dif_pos
    (slabCoordinatesBoundedB_true_of_mem
      (su2FineOuterData G g hg K) hsource)]
  have hrestrict :=
    restrictToSlabSupport_eq_of_mem
      (su2FineOuterData G g hg K) hsource
  simp only [hrestrict]
  rw [dif_neg hnotPositive]

theorem outerWholeSlabKernel_nonnegative
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    {source target : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData
          G g hg K).physicalLabellings)
    (_htarget :
      target ∈
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) :
    (0 : Q') ≤
      outerWholeSlabKernel closure K source target := by
  by_cases hpositive :
      (0 : Q') <
        (su2FineOuterData
          G g hg K).physicalTerm source
  · exact Q'.le_trans' _ _ _
      (wholeSlabRecouplingConditionalKernel_nonnegative
        (closure.coherentSource
          K source hsource hpositive)
        target)
      (Q'.ge_of_eqv
        (outerWholeSlabKernel_eq_positive
          closure K hsource hpositive target))
  · rw [outerWholeSlabKernel_eq_null
      closure K hsource hpositive target]
    exact outerNullCompletion_nonnegative
      G g hg candidate hcandidate K source target

theorem outerWholeSlabKernel_row_normalized
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat)
    {source : OuterSlabLabelling}
    (hsource :
      source ∈
        (su2FineOuterData
          G g hg K).physicalLabellings) :
    listQSum
        (outerWholeSlabKernel closure K source)
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings ≈
      1 := by
  by_cases hpositive :
      (0 : Q') <
        (su2FineOuterData
          G g hg K).physicalTerm source
  · refine Q'.eqv_trans _
      (listQSum
        (wholeSlabRecouplingConditionalKernel
          (closure.coherentSource
            K source hsource hpositive))
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) _ ?_ ?_
    · apply listQSum_congr_on
      intro target _
      exact outerWholeSlabKernel_eq_positive
        closure K hsource hpositive target
    · exact
        wholeSlabRecouplingConditionalKernel_row_normalized _
  · refine Q'.eqv_trans _
      (listQSum
        (outerNullCompletion
          G g hg candidate hcandidate K source)
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) _ ?_ ?_
    · apply listQSum_congr_on
      intro target _
      exact Q'.eqv_of_eq
        (outerWholeSlabKernel_eq_null
          closure K hsource hpositive target)
    · exact outerNullCompletion_row_normalized
        G g hg candidate hcandidate K source

/-! ## 4. Exact cutoff-one recovery -/

theorem outerWholeSlabKernel_one
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (source target : OuterSlabLabelling) :
    outerWholeSlabKernel closure 1 source target ≈
      (physicalKernel
        (G.candidateScalePair
          g hg candidate hcandidate)
        rfl hcandidate).kernel source target := by
  change outerWholeSlabKernel closure 1 source target ≈
    cutoffOneWholeSlabKernel
      (G.candidateScalePair
        g hg candidate hcandidate)
      rfl hcandidate source target
  unfold outerWholeSlabKernel cutoffOneWholeSlabKernel
  dsimp only [su2OuterScalePair, su2FineOuterData,
    su2CoarseOuterData, CutoffOneGeometry.candidateScalePair,
    CutoffOneGeometry.fineData, CutoffOneGeometry.coarseData]
  by_cases hbounded :
      slabCoordinatesBoundedB
          ({ coupling := g
             coupling_nonnegative := hg
             cutoff := 1
             half := G.fineHalf } : SlabPhysicalData)
          source =
        true
  · rw [dif_pos hbounded, dif_pos hbounded]
    let restricted :=
      restrictToSlabSupport
        ({ coupling := g
           coupling_nonnegative := hg
           cutoff := 1
           half := G.fineHalf } : SlabPhysicalData)
        source
    let hrestricted :=
      restrictToSlabSupport_mem_of_bounded
        ({ coupling := g
           coupling_nonnegative := hg
           cutoff := 1
           half := G.fineHalf } : SlabPhysicalData)
        hbounded
    by_cases hpositive :
        (0 : Q') <
          ({ coupling := g
             coupling_nonnegative := hg
             cutoff := 1
             half := G.fineHalf } : SlabPhysicalData).physicalTerm
          restricted
    · rw [dif_pos hpositive, dif_pos hpositive]
      apply wholeSlabConditionalKernel_eq_of_fineState_eq
      rfl
    · rw [dif_neg hpositive, dif_neg hpositive]
      exact Q'.eqv_of_eq
        (outerNullCompletion_one
          G g hg candidate hcandidate restricted target)
  · rw [dif_neg hbounded, dif_neg hbounded]
    exact Q'.eqv_of_eq
      (outerNullCompletion_one
        G g hg candidate hcandidate source target)

/-! ## 5. The remaining exact finite fusion-support laws -/

/-- **OPEN ALGEBRAIC/PHYSICAL INPUT.** Cutoff coherence for the explicitly
defined BF4 total kernel.

The first field says enlarging the pair-channel and target carriers does not
alter any old entry.  The second is the exact lossless-support theorem:
every target newly admitted above `4K` has zero probability from an old
source.  Both statements refer to `outerWholeSlabKernel`, so arbitrary Dirac
completion on positive higher-spin rows cannot inhabit this fence. -/
structure SU2OuterRawKernelCutoffCoherence
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
  old_source_no_new_target :
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
        outerWholeSlabKernel closure L source target ≈ 0

/-- The earlier stochastic contract is now obtained from a physically
identified raw kernel, not from opaque entries. -/
def physicalMarkovContractOfRawKernel
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (coherence :
      SU2OuterRawKernelCutoffCoherence closure) :
    SU2OuterPhysicalMarkovContract
      G g hg candidate hcandidate where
  kernelEntry := outerWholeSlabKernel closure
  nonnegative := by
    intro K source target hsource htarget
    exact outerWholeSlabKernel_nonnegative
      closure K hsource htarget
  row_total := by
    intro K source hsource
    exact outerWholeSlabKernel_row_normalized
      closure K hsource
  cutoff_stable := coherence.cutoff_stable
  old_source_no_new_target :=
    coherence.old_source_no_new_target
  cutoff_one_entry := by
    intro source target
    exact outerWholeSlabKernel_one
      closure source target

#print axioms su2OuterScalePair_one
#print axioms SU2OuterPositiveRowClosure
#print axioms SU2OuterPositiveRowClosure.coherentSource
#print axioms SU2OuterRawKernelCutoffCoherence
#print axioms outerNullCompletion_nonnegative
#print axioms outerNullCompletion_row_normalized
#print axioms outerNullCompletion_one
#print axioms outerWholeSlabKernel_eq_positive
#print axioms outerWholeSlabKernel_eq_null
#print axioms outerWholeSlabKernel_nonnegative
#print axioms outerWholeSlabKernel_row_normalized
#print axioms outerWholeSlabKernel_one
#print axioms physicalMarkovContractOfRawKernel

end YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
