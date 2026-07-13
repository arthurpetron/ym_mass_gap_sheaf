/-
# Exact allocator for two parallel one-attached branches

This concrete branching node has a marked-to-bad main path and two mutually
compatible branch polymers attached only through the bad main polymer.  The
allocator never traverses a branch.  Instead it keeps the terminal background
empty and records the chosen parallel children in the external occurrence
mask.  All four branch subsets therefore give genuine, distinct target codes
of exact unit rational weight, with singleton source fibers.
-/

import YMGap.Continuum.XiExceptionalBranchMovedExample

namespace YMGap.Continuum.XiExceptionalParallelBranchAllocator

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalTargetBlocks

local infix:50 " ≈ " => Q'.eqv

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def p2 : TL.Plaquette := (2, 0)
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1, p2]
private def C : Polymer TL := [p1]
private def D : Polymer TL := [p2]
private def Gamma : List (Polymer TL) := [A, B, C, D]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def badB : Polymer TL → Bool := fun X => decide (X = B)
private def label0 : TL.Plaquette → Rep := fun _ => 0

private def bits4 (x0 x1 x2 x3 : Bool) : OccBitVec 4 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 .nil)))

private def emptyBits : OccBitVec Gamma.length :=
  bits4 false false false false

inductive ParallelCase : Type
  | none
  | first
  | second
  | both
deriving DecidableEq

def parallelCases : List ParallelCase :=
  [.none, .first, .second, .both]

private def rightBits : ParallelCase → OccBitVec Gamma.length
  | .none => bits4 true false false false
  | .first => bits4 true false true false
  | .second => bits4 true false false true
  | .both => bits4 true false true true

private def externalBits : ParallelCase → OccBitVec Gamma.length
  | .none => bits4 false false false false
  | .first => bits4 false false true false
  | .second => bits4 false false false true
  | .both => bits4 false false true true

private def decodeExternal (bits : OccBitVec Gamma.length) : ParallelCase :=
  match bits.at 2, bits.at 3 with
  | false, false => .none
  | true, false => .first
  | false, true => .second
  | true, true => .both

private theorem decode_externalBits (c : ParallelCase) :
    decodeExternal (externalBits c) = c := by
  cases c <;> rfl

private def sourcePair (c : ParallelCase) : MaskPair Gamma.length :=
  (bits4 false true false false, rightBits c)

theorem sourcePair_mem (c : ParallelCase) :
    sourcePair c ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete (sourcePair c), ?_⟩
  cases c <;> rfl

private def sourceEntry (c : ParallelCase) :
    ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨sourcePair c, sourcePair_mem c⟩

def parallelCode (c : ParallelCase) : OccCarrierXiCodeAt Gamma :=
  exceptionalCustomCarrierCode Gamma qAll markA badB (sourceEntry c)
    emptyBits (externalBits c)

theorem parallelCode_mem (c : ParallelCase) :
    parallelCode c ∈ occurrenceCarrierXiCodes Gamma :=
  exceptionalCustomCarrierCode_mem Gamma qAll markA badB (sourceEntry c)
    emptyBits (externalBits c)

theorem externalBits_injective : ∀ c d : ParallelCase,
    externalBits c = externalBits d → c = d := by
  intro c d h
  rw [← decode_externalBits c, ← decode_externalBits d]
  exact congrArg decodeExternal h

/-- The two external occurrence bits recover the full branch subset. -/
theorem parallelCode_injective : ∀ c d : ParallelCase,
    parallelCode c = parallelCode d → c = d := by
  intro c d hcode
  apply externalBits_injective c d
  have hext := congrArg (fun code => code.external) hcode
  simpa [parallelCode, exceptionalCustomCarrierCode] using hext

def parallelBlock : List (OccCarrierXiCodeAt Gamma) :=
  parallelCases.map parallelCode

theorem parallelCases_nodup : parallelCases.Nodup := by decide

theorem parallelBlock_nodup : parallelBlock.Nodup := by
  unfold parallelBlock
  exact nodup_map_of_injOn parallelCode parallelCases parallelCases_nodup
    (fun c _ d _ h => parallelCode_injective c d h)

theorem parallelBlock_length : parallelBlock.length = 4 := rfl

theorem parallelBlock_mem : ∀ code, code ∈ parallelBlock →
    code ∈ occurrenceCarrierXiCodes Gamma := by
  intro code hcode
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hcode
  exact parallelCode_mem c

/-- Explicit singleton-fiber control for the branch allocator. -/
theorem parallel_source_fiber_unique (c d : ParallelCase)
    (h : parallelCode c = parallelCode d) : c = d :=
  parallelCode_injective c d h

private theorem activity_label0_one (X : Polymer TL) :
    activity (1 : Q') X label0 = 1 := by
  induction X with
  | nil => rfl
  | cons p X ih =>
      simp only [activity_cons, plaqWeight, label0, coeffW_zero, ih]
      rfl

private theorem familyActivity_label0_one (S : List (Polymer TL)) :
    familyActivity (1 : Q') S label0 = 1 := by
  induction S with
  | nil => rfl
  | cons X S ih =>
      simp only [familyActivity_cons, activity_label0_one, ih]
      rfl

private theorem walkActivity_label0_one {X Y : Polymer TL}
    (walk : CWalk (fun U V : Polymer TL => !(compatibleB U V)) X Y) :
    walk.activityWeight (1 : Q') label0 = 1 := by
  induction walk with
  | single X => exact activity_label0_one X
  | cons _ rest ih =>
      simp only [CWalk.activityWeight, activity_label0_one, ih]
      rfl

def sourceWeight (c : ParallelCase) : Q' :=
  occurrencePairWeight 1 qAll markA badB Gamma label0 (sourcePair c)

theorem sourceWeight_one (c : ParallelCase) : sourceWeight c = 1 := by
  unfold sourceWeight
  rw [occurrencePairWeight_eq_source_activity_of_mem
    1 qAll markA badB Gamma label0 (sourcePair c) (sourcePair_mem c)]
  rw [familyActivity_label0_one, familyActivity_label0_one]
  rfl

/-- Exact weight preservation for every one of the four branch subsets. -/
theorem parallelCode_weight_eqv_one (c : ParallelCase) :
    occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0
      (parallelCode c) ≈ (1 : Q') := by
  have h := exceptionalCustomCarrierCode_weight_eqv
    1 qAll markA badB Gamma label0 (sourceEntry c)
      emptyBits (externalBits c)
      (by rfl) (by rfl)
      (by
        dsimp only
        intro X _ T hT
        cases hT)
      (by cases c <;> rfl)
      (by cases c <;> rfl)
  dsimp only at h
  refine Q'.eqv_trans _ _ _ h ?_
  rw [walkActivity_label0_one, familyActivity_label0_one,
    familyActivity_label0_one]
  rfl

theorem source_le_singleton_target (c : ParallelCase) :
    sourceWeight c ≤
      qListSum
        (occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0)
        [parallelCode c] := by
  simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
  rw [sourceWeight_one c]
  exact Q'.ge_of_eqv (parallelCode_weight_eqv_one c)

/-- The four-code branch block is an exact bounded-fiber allocation into the
complete occurrence target. -/
theorem parallel_branches_global_bound :
    qListSum sourceWeight parallelCases ≤
      qListSum
        (occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks parallelCases
    (occurrenceCarrierXiCodes Gamma) sourceWeight
    (occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0)
    (fun c => [parallelCode c])
  · simpa [parallelBlock, parallelCases] using parallelBlock_nodup
  · intro code hcode
    obtain ⟨c, hc, hsingleton⟩ := List.mem_flatMap.mp hcode
    rw [List.mem_singleton] at hsingleton
    subst code
    exact parallelCode_mem c
  · intro c _
    exact source_le_singleton_target c
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative
      (by decide) qAll markA badB Gamma label0 code

#print axioms sourcePair_mem
#print axioms parallelCode_mem
#print axioms parallelCode_injective
#print axioms parallelBlock_nodup
#print axioms parallel_source_fiber_unique
#print axioms sourceWeight_one
#print axioms parallelCode_weight_eqv_one
#print axioms parallel_branches_global_bound

end YMGap.Continuum.XiExceptionalParallelBranchAllocator
