/-
# Tagged finite bookkeeping adapter for both-sides-unsafe sources

The normalized walk cannot in general be placed in the old carrier merely
from its construction: the old chain fuel is `Gamma.length`, whereas repeated
splicing conserves `walkLength + 2 * potential`.  Moreover, in the proved
strong-coupling window normalization is activity-nonincreasing, the opposite
direction from a pointwise source-to-old-target domination.

The honest bookkeeping carrier therefore adds a disjoint tagged unsafe-source
summand.  Covered sources retain the old occurrence carrier.  Each unsafe code
literally stores the original exceptional entry with its original weight; its
computed trace separately has a left inverse only at the `SpliceState` level.
Thus injectivity and the global weighted bound below come from retaining the
source tag, not from trace-based compression or activity payment.  The result
is a finite, duplicate-free partitioning carrier, while compression back into
the old carrier remains fully open.
-/

import YMGap.Continuum.XiExceptionalTracedNormalization
import YMGap.Continuum.XiExceptionalTargetNodup
import YMGap.Continuum.XiExceptionalUnequalEarFuelFence

namespace YMGap.Continuum.XiExceptionalTracedUnsafeAdapter

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalBothSidesUnsafeSplit
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalFirstConflictActivity
open YMGap.Continuum.XiExceptionalTracedNormalization
open YMGap.Continuum.XiExceptionalTargetNodup
open YMGap.Continuum.XiExceptionalUnequalEarFuelFence

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Entry-level splice state and trace -/

def entryLeftSpliceState
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    SpliceState Gamma (exceptionalMarkedIndex Gamma b1 b2 entry.1) path.seed := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  exact
    { walk := conflictWalkOfDisagreement Gamma
        (bitMask entry.1.1) (bitMask entry.1.2) path.indexWalk
      residual := leftPathResidual Gamma qP b1 b2 entry }

theorem entryLeftSpliceState_unsafeCheckB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : leftResidualPathSafeB Gamma qP b1 b2 entry = false) :
    (entryLeftSpliceState Gamma qP b1 b2 entry).unsafeCheckB = false := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  change (occurrenceIndices Gamma.length).all (fun i =>
    Bool.not ((leftPathResidual Gamma qP b1 b2 entry).at i) ||
      pathSafe Gamma
        (conflictWalkOfDisagreement Gamma (bitMask entry.1.1)
          (bitMask entry.1.2) path.indexWalk).vertices i) = false
  rw [conflictWalkOfDisagreement_vertices]
  simpa only [leftResidualPathSafeB] using hunsafe

theorem bothSidesPathUnsafe_left_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ bothSidesPathUnsafeSource Gamma qP b1 b2) :
    leftResidualPathSafeB Gamma qP b1 b2 entry = false := by
  have hnot := (List.mem_filter.mp hentry).2
  unfold twoSidedCoveredB at hnot
  cases hl : leftResidualPathSafeB Gamma qP b1 b2 entry <;>
    cases hr : rightResidualPathSafeB Gamma qP b1 b2 entry <;>
    simp [hl, hr] at hnot
  rfl

structure EntryTracedCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) : Type where
  entry : ExceptionalSourceEntry Gamma qP b1 b2

def EntryTracedCode.trace
    {Gamma : List (Polymer L)} {qP b1 b2 : Polymer L → Bool}
    (code : EntryTracedCode Gamma qP b1 b2) :=
  tracedExhaust (entryLeftSpliceState Gamma qP b1 b2 code.entry)

def unsafeEntryTracedCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    EntryTracedCode Gamma qP b1 b2 :=
  ⟨entry⟩

theorem unsafeEntryTracedCode_recovers
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (unsafeEntryTracedCode Gamma qP b1 b2 entry).entry = entry := rfl

theorem unsafeEntryTracedCode_trace_decodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (unsafeEntryTracedCode Gamma qP b1 b2 entry).trace.decodeInitial =
      entryLeftSpliceState Gamma qP b1 b2 entry :=
  tracedExhaust_decodeInitial _

theorem unsafeEntryTracedCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (a b : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : unsafeEntryTracedCode Gamma qP b1 b2 a =
      unsafeEntryTracedCode Gamma qP b1 b2 b) : a = b := by
  injection hcode

/-! ## Tagged disjoint finite bookkeeping carrier -/

inductive CorrectedCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) : Type
  | covered (code : OccCarrierXiCodeAt Gamma)
  | traced (code : EntryTracedCode Gamma qP b1 b2)

def correctedCarrierCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (CorrectedCarrierCode Gamma qP b1 b2) :=
  (occurrenceCarrierXiCodes Gamma).map CorrectedCarrierCode.covered ++
    (bothSidesPathUnsafeSource Gamma qP b1 b2).map
      (fun entry => CorrectedCarrierCode.traced
        (unsafeEntryTracedCode Gamma qP b1 b2 entry))

def correctedCarrierWeight
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep) :
    CorrectedCarrierCode Gamma qP b1 b2 → Q'
  | .covered code =>
      occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label code
  | .traced code =>
      occurrencePairWeight w qP b1 b2 Gamma label code.entry.1

theorem unsafe_trace_mem_correctedCarrierCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ bothSidesPathUnsafeSource Gamma qP b1 b2) :
    CorrectedCarrierCode.traced
      (unsafeEntryTracedCode Gamma qP b1 b2 entry) ∈
        correctedCarrierCodes Gamma qP b1 b2 := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨entry, hentry, rfl⟩

theorem correctedCarrierCodes_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (correctedCarrierCodes Gamma qP b1 b2).Nodup := by
  unfold correctedCarrierCodes
  apply List.nodup_append.mpr
  constructor
  · exact nodup_map_of_injOn CorrectedCarrierCode.covered
      (occurrenceCarrierXiCodes Gamma)
      (occurrenceCarrierXiCodes_nodup Gamma)
      (fun _ _ _ _ h => by injection h)
  constructor
  · apply nodup_map_of_injOn _ _
      (nodup_filter_bool _ _
        (fullExceptionalSource_nodup Gamma qP b1 b2))
    intro a _ b _ h
    injection h with hcode
    exact unsafeEntryTracedCode_injective Gamma qP b1 b2 a b hcode
  · intro a ha b hb hab
    obtain ⟨covered, _, hcovered⟩ := List.mem_map.mp ha
    obtain ⟨entry, _, htraced⟩ := List.mem_map.mp hb
    rw [← hcovered, ← htraced] at hab
    cases hab

theorem correctedCarrierCodes_weight_eqv
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum (correctedCarrierWeight w qP b1 b2 Gamma label)
        (correctedCarrierCodes Gamma qP b1 b2) ≈
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
          (occurrenceCarrierXiCodes Gamma) +
        qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (bothSidesPathUnsafeSource Gamma qP b1 b2) := by
  unfold correctedCarrierCodes
  refine Q'.eqv_trans _ _ _
    (qListSum_append (correctedCarrierWeight w qP b1 b2 Gamma label) _ _) ?_
  rw [qListSum_map, qListSum_map]
  exact Q'.eqv_refl _

theorem fullExceptionalSource_le_correctedCarrierCodes
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (fullExceptionalSource Gamma qP b1 b2) ≤
      qListSum (correctedCarrierWeight w qP b1 b2 Gamma label)
        (correctedCarrierCodes Gamma qP b1 b2) := by
  have hpartition := exceptionalSource_twoSided_unsafe_partition
    w Gamma qP b1 b2 label
  have hcovered := twoSidedCoveredSource_global_bound
    hw Gamma qP b1 b2 label
  have hadd := Q'.add_le_add hcovered (Q'.le_refl'
    (qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
      entry.1) (bothSidesPathUnsafeSource Gamma qP b1 b2)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition)
    (Q'.le_trans' _ _ _ hadd
      (Q'.ge_of_eqv (correctedCarrierCodes_weight_eqv
        w Gamma qP b1 b2 label)))

/-! ## Entry trace properties inherited from the reversible normalizer -/

theorem unsafeEntryTrace_final_safe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (unsafeEntryTracedCode Gamma qP b1 b2 entry).trace.final.unsafeCheckB =
      true :=
  tracedExhaust_final_safe _

theorem unsafeEntryTrace_activity_le_of_strong
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide))
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    SpliceState.totalActivity w label
        (unsafeEntryTracedCode Gamma qP b1 b2 entry).trace.final ≤
      SpliceState.totalActivity w label
        (entryLeftSpliceState Gamma qP b1 b2 entry) :=
  tracedExhaust_finalActivity_le_of_strong hw0 hw label _

/-! Conditionally, if this particular traced final walk exceeds the old fuel,
its corresponding chain code is absent from `occurrenceChainCodes`.  This does
not prove that an unsafe trace overflows, nor full-code nonmembership in
`occurrenceCarrierXiCodes`; it is only the exact chain-level fence stated by
the theorem. -/

theorem unsafeEntryTrace_old_chain_not_mem_of_overflow
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (background : OccBitVec Gamma.length)
    (hoverflow : Gamma.length + 1 <
      (unsafeEntryTracedCode Gamma qP b1 b2 entry).trace.final.walk.vertices.length) :
    occurrenceChainCodeOfWalk
        (unsafeEntryTracedCode Gamma qP b1 b2 entry).trace.final.walk
        background ∉ occurrenceChainCodes Gamma Gamma.length :=
  occurrenceChainCodeOfWalk_not_mem_of_overflow Gamma _ background hoverflow

#print axioms entryLeftSpliceState_unsafeCheckB
#print axioms bothSidesPathUnsafe_left_false
#print axioms unsafeEntryTracedCode_trace_decodes
#print axioms unsafeEntryTracedCode_injective
#print axioms unsafe_trace_mem_correctedCarrierCodes
#print axioms correctedCarrierCodes_nodup
#print axioms correctedCarrierCodes_weight_eqv
#print axioms fullExceptionalSource_le_correctedCarrierCodes
#print axioms unsafeEntryTrace_final_safe
#print axioms unsafeEntryTrace_activity_le_of_strong
#print axioms unsafeEntryTrace_old_chain_not_mem_of_overflow

end YMGap.Continuum.XiExceptionalTracedUnsafeAdapter
