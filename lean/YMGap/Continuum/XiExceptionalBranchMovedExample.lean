/-
# A positive branch-to-external target allocation

The three-polymer obstruction is repaired constructively by moving its
path-incompatible branch `C` out of the terminal background and into the
external family.  The bare and branched sources then receive distinct positive
carrier codes of exact weight one.  Their singleton target blocks are disjoint
and embed in the full occurrence target enumeration.
-/

import YMGap.Continuum.XiExceptionalCustomCarrier

namespace YMGap.Continuum.XiExceptionalBranchMovedExample

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
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1]
private def C : Polymer TL := [p1]
private def Gamma : List (Polymer TL) := [A, B, C]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def badB : Polymer TL → Bool := fun X => decide (X = B)
private def label0 : TL.Plaquette → Rep := fun _ => 0
private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))
private def emptyBits : OccBitVec Gamma.length := bits3 false false false
private def cBits : OccBitVec Gamma.length := bits3 false false true
private def pairBare : MaskPair Gamma.length :=
  (bits3 false true false, bits3 true false false)
private def pairBranch : MaskPair Gamma.length :=
  (bits3 false true false, bits3 true false true)

theorem pairBare_mem :
    pairBare ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairBare, ?_⟩
  rfl

theorem pairBranch_mem :
    pairBranch ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairBranch, ?_⟩
  rfl

private def entryBare : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pairBare, pairBare_mem⟩
private def entryBranch : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pairBranch, pairBranch_mem⟩

private def bareMovedCode : OccCarrierXiCodeAt Gamma :=
  exceptionalCustomCarrierCode Gamma qAll markA badB entryBare
    emptyBits emptyBits

private def branchMovedCode : OccCarrierXiCodeAt Gamma :=
  exceptionalCustomCarrierCode Gamma qAll markA badB entryBranch
    emptyBits cBits

theorem bareMovedCode_mem : bareMovedCode ∈ occurrenceCarrierXiCodes Gamma :=
  exceptionalCustomCarrierCode_mem Gamma qAll markA badB entryBare
    emptyBits emptyBits

theorem branchMovedCode_mem :
    branchMovedCode ∈ occurrenceCarrierXiCodes Gamma :=
  exceptionalCustomCarrierCode_mem Gamma qAll markA badB entryBranch
    emptyBits cBits

theorem movedCodes_ne : bareMovedCode ≠ branchMovedCode := by
  intro hcode
  have hext := congrArg (fun code => code.external) hcode
  have hat := congrArg (fun bits => bits.at 2) hext
  cases hat

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

theorem pairBare_weight_one :
    occurrencePairWeight 1 qAll markA badB Gamma label0 pairBare = 1 := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    1 qAll markA badB Gamma label0 pairBare pairBare_mem]
  rw [familyActivity_label0_one, familyActivity_label0_one]
  rfl

theorem pairBranch_weight_one :
    occurrencePairWeight 1 qAll markA badB Gamma label0 pairBranch = 1 := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    1 qAll markA badB Gamma label0 pairBranch pairBranch_mem]
  rw [familyActivity_label0_one, familyActivity_label0_one]
  rfl

theorem bareMovedCode_weight_eqv_one :
    occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0
      bareMovedCode ≈ (1 : Q') := by
  have h := exceptionalCustomCarrierCode_weight_eqv
    1 qAll markA badB Gamma label0 entryBare emptyBits emptyBits
      (by rfl) (by rfl) (by
        dsimp only
        intro X _ T hT
        cases hT) (by rfl) (by rfl)
  dsimp only at h
  refine Q'.eqv_trans _ _ _ h ?_
  rw [walkActivity_label0_one, familyActivity_label0_one]
  rfl

theorem branchMovedCode_weight_eqv_one :
    occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0
      branchMovedCode ≈ (1 : Q') := by
  have h := exceptionalCustomCarrierCode_weight_eqv
    1 qAll markA badB Gamma label0 entryBranch emptyBits cBits
      (by rfl) (by rfl) (by
        dsimp only
        intro X _ T hT
        cases hT) (by rfl) (by rfl)
  dsimp only at h
  refine Q'.eqv_trans _ _ _ h ?_
  rw [walkActivity_label0_one, familyActivity_label0_one]
  rfl

inductive BranchCase : Type
  | bare
  | branch
deriving DecidableEq

private def sourceEntry : BranchCase →
    ExceptionalSourceEntry Gamma qAll markA badB
  | .bare => entryBare
  | .branch => entryBranch

private def sourceWeight (c : BranchCase) : Q' :=
  occurrencePairWeight 1 qAll markA badB Gamma label0 (sourceEntry c).1

private def movedCode : BranchCase → OccCarrierXiCodeAt Gamma
  | .bare => bareMovedCode
  | .branch => branchMovedCode

private def movedBlock (c : BranchCase) : List (OccCarrierXiCodeAt Gamma) :=
  [movedCode c]

theorem moved_blocks_global_bound :
    qListSum sourceWeight [BranchCase.bare, BranchCase.branch] ≤
      qListSum
        (occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks
    [BranchCase.bare, BranchCase.branch]
    (occurrenceCarrierXiCodes Gamma) sourceWeight
    (occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0)
    movedBlock
  · simp only [List.flatMap_cons, List.flatMap_nil, movedBlock,
      movedCode, List.append_nil]
    change List.Nodup [bareMovedCode, branchMovedCode]
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rw [List.mem_singleton] at hmem
      exact movedCodes_ne hmem
    · apply List.nodup_cons.mpr
      constructor
      · intro hmem
        cases hmem
      · exact List.nodup_nil
  · intro code hcode
    change code ∈ [bareMovedCode, branchMovedCode] at hcode
    rcases List.mem_cons.mp hcode with hbare | hbranch
    · subst code
      exact bareMovedCode_mem
    · rw [List.mem_singleton] at hbranch
      subst code
      exact branchMovedCode_mem
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · change occurrencePairWeight 1 qAll markA badB Gamma label0 pairBare ≤
        qListSum
          (occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0)
          [bareMovedCode]
      simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
      rw [pairBare_weight_one]
      exact Q'.ge_of_eqv bareMovedCode_weight_eqv_one
    · rw [List.mem_singleton] at hc
      subst c
      change occurrencePairWeight 1 qAll markA badB Gamma label0 pairBranch ≤
        qListSum
          (occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0)
          [branchMovedCode]
      simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
      rw [pairBranch_weight_one]
      exact Q'.ge_of_eqv branchMovedCode_weight_eqv_one
  · intro code hcode
    exact occurrenceCarrierXiCodeWeight_nonnegative
      (by decide) qAll markA badB Gamma label0 code

#print axioms movedCodes_ne
#print axioms bareMovedCode_weight_eqv_one
#print axioms branchMovedCode_weight_eqv_one
#print axioms moved_blocks_global_bound

end YMGap.Continuum.XiExceptionalBranchMovedExample
