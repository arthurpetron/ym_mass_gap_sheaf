/-
# Source-entry fence for complete final-length empty-mask rewirings

This is a genuine exceptional source, not an arbitrary splice state.  Its
canonical marked-to-bad path has one unsafe cleared left residual.  There are
exactly two in-range three-edge occurrence rewirings from the marked index to
the bad index, because the two residual-side polymers are compatible with one
another.  Both ordinary empty-mask carrier codes are present and distinct.

At the exact derived coupling `w = 1/2`, the source has weight `1/256`, while
each rewiring has weight `1/4096`; their complete block has weight `1/2048`.
Thus even the complete final-length rewiring block fails.  A successful
trace/right-keyed allocator must use additional masks, shorter paths, or some
other target structure; multiplying final detours is not enough.
-/

import YMGap.Continuum.XiExceptionalFinalCarrierFiberBlock
import YMGap.Continuum.XiExceptionalFiberwiseInjection

namespace YMGap.Continuum.XiExceptionalEntryRewiringBlockFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalTraceRightInvariant
open YMGap.Continuum.XiExceptionalTraceFuelSharp

local infix:50 " ≈ " => Q'.eqv

abbrev TL := toyLattice

instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

def p0 : TL.Plaquette := (0, 0)
def p1 : TL.Plaquette := (1, 0)
def A : Polymer TL := [p0, p1]
def B : Polymer TL := [p1]
def C : Polymer TL := [p0]
def Gamma : List (Polymer TL) := [A, B, C]
def qAll : Polymer TL → Bool := fun _ => true
def markA : Polymer TL → Bool := fun X => decide (X = A)
def badB : Polymer TL → Bool := fun X => decide (X = B)
def labelOne : TL.Plaquette → Rep := fun _ => 1
def half : Q' := Q'.mkPos 1 2 (by decide)
def oneOver256 : Q' := Q'.mkPos 1 256 (by decide)
def oneOver4096 : Q' := Q'.mkPos 1 4096 (by decide)
def oneOver2048 : Q' := Q'.mkPos 1 2048 (by decide)

def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

def sourcePair : MaskPair Gamma.length :=
  (bits3 false true true, bits3 true false false)

theorem sourcePair_mem :
    sourcePair ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete sourcePair, ?_⟩
  rfl

def sourceEntry : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨sourcePair, sourcePair_mem⟩

def sourceKey : EntryLeftTraceRightCode Gamma :=
  entryLeftTraceRightCode Gamma qAll markA badB sourceEntry

theorem sourceKey_recovers_entry
    (other : ExceptionalSourceEntry Gamma qAll markA badB)
    (hkey : entryLeftTraceRightCode Gamma qAll markA badB other = sourceKey) :
    other = sourceEntry := by
  exact entryLeftTraceRightCode_injective Gamma qAll markA badB
    other sourceEntry hkey

/-! ## Complete enumeration of the three-edge empty-mask rewirings -/

def allowedMiddlePairs : List (Nat × Nat) := [(1, 0), (2, 0)]

theorem allowedMiddlePairs_complete (i j : Nat)
    (hi : i < Gamma.length) (hj : j < Gamma.length)
    (h0i : incAtDistinct Gamma 0 i = true)
    (hij : incAtDistinct Gamma i j = true)
    (hj1 : incAtDistinct Gamma j 1 = true) :
    (i, j) ∈ allowedMiddlePairs := by
  have hi3 : i < 3 := by simpa [Gamma] using hi
  have hj3 : j < 3 := by simpa [Gamma] using hj
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hiCases with rfl | rfl | rfl
  · change false = true at h0i
    cases h0i
  · rcases hjCases with rfl | rfl | rfl
    · simp [allowedMiddlePairs]
    · change false = true at hij
      cases hij
    · change false = true at hij
      cases hij
  · rcases hjCases with rfl | rfl | rfl
    · simp [allowedMiddlePairs]
    · change false = true at hj1
      cases hj1
    · change false = true at hij
      cases hij

def walk0101 : CWalk (incAtDistinct Gamma) 0 1 :=
  .cons (y := 1) (by rfl)
    (.cons (y := 0) (by rfl) (.cons (y := 1) (by rfl) (.single 1)))

def walk0201 : CWalk (incAtDistinct Gamma) 0 1 :=
  .cons (y := 2) (by rfl)
    (.cons (y := 0) (by rfl) (.cons (y := 1) (by rfl) (.single 1)))

def emptyBits : OccBitVec Gamma.length := bits3 false false false

def carrierOfWalk (walk : CWalk (incAtDistinct Gamma) 0 1) :
    OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := occurrenceChainCodeOfWalk walk emptyBits }
    external := emptyBits }

def carrier0101 := carrierOfWalk walk0101
def carrier0201 := carrierOfWalk walk0201

def completeRewiringBlock : List (OccCarrierXiCodeAt Gamma) :=
  [carrier0101, carrier0201]

theorem completeRewiringBlock_nodup : completeRewiringBlock.Nodup := by
  decide

private theorem carrierOfWalk_mem
    (walk : CWalk (incAtDistinct Gamma) 0 1)
    (hlength : walk.vertices.length ≤ Gamma.length + 1)
    (hbounds : ∀ k, k ∈ walk.vertices → k < Gamma.length) :
    carrierOfWalk walk ∈ occurrenceCarrierXiCodes Gamma := by
  unfold carrierOfWalk occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨emptyBits, bitVectors_complete emptyBits, ?_⟩
  apply List.mem_map.mpr
  refine ⟨{ start := 0, chain := occurrenceChainCodeOfWalk walk emptyBits },
    ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk walk emptyBits, ?_, rfl⟩
  exact occurrenceChainCodeOfWalk_mem_sharp Gamma emptyBits walk Gamma.length
    hlength hbounds

private theorem four_vertices_bound (vertices : List Nat)
    (h : vertices = [0, 1, 0, 1] ∨ vertices = [0, 2, 0, 1]) :
    ∀ k, k ∈ vertices → k < Gamma.length := by
  intro k hk
  rcases h with h | h <;> rw [h] at hk <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk <;>
    rcases hk with rfl | rfl | rfl | rfl <;> decide

theorem carrier0101_mem : carrier0101 ∈ occurrenceCarrierXiCodes Gamma := by
  apply carrierOfWalk_mem walk0101
  · decide
  · exact four_vertices_bound walk0101.vertices (Or.inl rfl)

theorem carrier0201_mem : carrier0201 ∈ occurrenceCarrierXiCodes Gamma := by
  apply carrierOfWalk_mem walk0201
  · decide
  · exact four_vertices_bound walk0201.vertices (Or.inr rfl)

/-! ## Exact source and complete-block weights -/

def sourceWeight : Q' :=
  occurrencePairWeight half qAll markA badB Gamma labelOne sourcePair

def targetWeight (code : OccCarrierXiCodeAt Gamma) : Q' :=
  occurrenceCarrierXiCodeWeight half qAll markA badB Gamma labelOne code

theorem fundamental_activity_quarter : activity half B labelOne ≈
    Q'.mkPos 1 4 (by decide) := by
  decide

theorem sourceWeight_exact : sourceWeight ≈ oneOver256 := by
  decide

theorem carrier0101_weight_exact : targetWeight carrier0101 ≈
    oneOver4096 := by
  decide

theorem carrier0201_weight_exact : targetWeight carrier0201 ≈
    oneOver4096 := by
  decide

theorem completeRewiringBlock_weight_exact :
    qListSum targetWeight completeRewiringBlock ≈ oneOver2048 := by
  simp only [completeRewiringBlock, qListSum_cons, qListSum_nil]
  refine Q'.eqv_trans _ (oneOver4096 + (oneOver4096 + 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr' carrier0101_weight_exact
      (Q'.add_eqv_congr' carrier0201_weight_exact (Q'.eqv_refl _))
  · decide

/-- The complete final-length empty-mask rewiring block cannot pay this one
genuine exceptional source entry. -/
theorem completeRewiringBlock_fails_source :
    ¬ (sourceWeight ≤ qListSum targetWeight completeRewiringBlock) := by
  intro hbound
  have h256le2048 : oneOver256 ≤ oneOver2048 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv sourceWeight_exact)
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_of_eqv completeRewiringBlock_weight_exact))
  exact (by decide : ¬ (oneOver256 ≤ oneOver2048)) h256le2048

#print axioms sourcePair_mem
#print axioms sourceKey_recovers_entry
#print axioms allowedMiddlePairs_complete
#print axioms completeRewiringBlock_nodup
#print axioms carrier0101_mem
#print axioms carrier0201_mem
#print axioms sourceWeight_exact
#print axioms completeRewiringBlock_weight_exact
#print axioms completeRewiringBlock_fails_source

end YMGap.Continuum.XiExceptionalEntryRewiringBlockFence
