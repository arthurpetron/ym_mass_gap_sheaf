/-
# Fourth exceptional branch: certified mixed-repair blocks

The three structural singleton branches leave the balanced six-cycle.  Its
two pair-bounced ears are genuine members of the unchanged occurrence target
and their exact square weights dominate the source monomial.  This file
packages such repairs behind a Boolean classifier, including the block-level
disjointness needed to sum many certified sources without paying a target
code twice.  The old three-branch residual is then split exactly into the
fourth branch and a new residual.

The bounced-ear construction is not universal: its exact fuel invariant is
balance of selected and reserve interior-pair counts.  The already checked
four-occurrence unequal-ear obstruction is exposed as the false Boolean
corner of that invariant.
-/

import YMGap.Continuum.XiExceptionalThreeBranchClassificationFence
import YMGap.Continuum.XiExceptionalTargetBlocks
import YMGap.Continuum.XiExceptionalBlockCutFuel
import YMGap.Continuum.XiExceptionalUnequalEarFuelFence

namespace YMGap.Continuum.XiExceptionalFourthMixedRepair

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalThreeBranchClassificationFence
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalBlockCutFuel

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## A general Boolean mixed-repair allocator -/

/-- A fourth-branch classifier together with a finite block in the unchanged
occurrence target.  Pairwise block disjointness is part of the certificate,
so a global sum cannot silently reuse a target code. -/
structure MixedRepairAllocator
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) where
  test : ExceptionalSourceEntry Gamma qP b1 b2 → Bool
  block : ExceptionalSourceEntry Gamma qP b1 b2 →
    List (OccCarrierXiCodeAt Gamma)
  block_nodup : ∀ entry, test entry = true → (block entry).Nodup
  block_mem : ∀ entry, test entry = true → ∀ code,
    code ∈ block entry → code ∈ occurrenceCarrierXiCodes Gamma
  blocks_disjoint : ∀ a, test a = true → ∀ b, test b = true →
    a ≠ b → ∀ code, code ∈ block a → code ∉ block b
  source_le_block : ∀ {w : Q'}, (0 : Q') ≤ w →
    ∀ (label : L.Plaquette → Rep) entry, test entry = true →
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 ≤
        qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
          (block entry)

def mixedRepairSource
    {Gamma : List (Polymer L)} {qP b1 b2 : Polymer L → Bool}
    (repair : MixedRepairAllocator Gamma qP b1 b2) :=
  (threeBranchResidualSource Gamma qP b1 b2).filter repair.test

def fourBranchResidualSource
    {Gamma : List (Polymer L)} {qP b1 b2 : Polymer L → Bool}
    (repair : MixedRepairAllocator Gamma qP b1 b2) :=
  (threeBranchResidualSource Gamma qP b1 b2).filter
    (fun entry => !(repair.test entry))

def fourBranchCoveredB
    {Gamma : List (Polymer L)} {qP b1 b2 : Polymer L → Bool}
    (repair : MixedRepairAllocator Gamma qP b1 b2)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  threeBranchCoveredB Gamma qP b1 b2 entry || repair.test entry

private theorem threeBranchResidualSource_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (threeBranchResidualSource Gamma qP b1 b2).Nodup := by
  unfold threeBranchResidualSource afterComponentRightSource
    afterRoutedPathSafeSource
  exact nodup_filter_bool _ _
    (nodup_filter_bool _ _
      (nodup_filter_bool _ _
        (fullExceptionalSource_nodup Gamma qP b1 b2)))

/-- Exact five-region source partition.  The nesting makes the three old
branches, the mixed repair, and the remaining source mutually exclusive. -/
theorem exceptionalSource_fourBranch_residual_partition
    (repair : MixedRepairAllocator Gamma qP b1 b2)
    (w : Q') (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (fullExceptionalSource Gamma qP b1 b2) ≈
      qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (routedPathSafeBranchSource Gamma qP b1 b2) +
        (qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
            entry.1) (componentRightOnlySource Gamma qP b1 b2) +
          (qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
              entry.1) (componentLeftOnlySource Gamma qP b1 b2) +
            (qListSum (fun entry => occurrencePairWeight w qP b1 b2
                Gamma label entry.1) (mixedRepairSource repair) +
              qListSum (fun entry => occurrencePairWeight w qP b1 b2
                Gamma label entry.1) (fourBranchResidualSource repair)))) := by
  let weight := fun entry : ExceptionalSourceEntry Gamma qP b1 b2 =>
    occurrencePairWeight w qP b1 b2 Gamma label entry.1
  have hbase := exceptionalSource_threeBranch_residual_partition
    w Gamma qP b1 b2 label
  have hrepair := qListSum_filter_partition weight repair.test
    (threeBranchResidualSource Gamma qP b1 b2)
  change qListSum weight (fullExceptionalSource Gamma qP b1 b2) ≈
    qListSum weight (routedPathSafeBranchSource Gamma qP b1 b2) +
      (qListSum weight (componentRightOnlySource Gamma qP b1 b2) +
        (qListSum weight (componentLeftOnlySource Gamma qP b1 b2) +
          qListSum weight (threeBranchResidualSource Gamma qP b1 b2)))
    at hbase
  change qListSum weight (threeBranchResidualSource Gamma qP b1 b2) ≈
    qListSum weight (mixedRepairSource repair) +
      qListSum weight (fourBranchResidualSource repair) at hrepair
  exact Q'.eqv_trans _ _ _ hbase
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_left _ _ _ hrepair)))

theorem fourBranchResidualSource_tests
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (repair : MixedRepairAllocator Gamma qP b1 b2)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ fourBranchResidualSource repair) :
    routedExternalCompatibleB Gamma qP b1 b2 entry = false ∧
      componentRightSafeB Gamma qP b1 b2 entry = false ∧
      componentLeftSafeB Gamma qP b1 b2 entry = false ∧
      repair.test entry = false := by
  have hrepair := (List.mem_filter.mp hentry).2
  have hold := (List.mem_filter.mp hentry).1
  obtain ⟨hpath, hright, hleft⟩ :=
    threeBranchResidualSource_tests Gamma qP b1 b2 entry hold
  cases ht : repair.test entry <;> simp_all

/-- Every source selected by a certified mixed repair is paid by a genuinely
duplicate-free sublist of the unchanged occurrence target. -/
theorem mixedRepairSource_global_bound
    (repair : MixedRepairAllocator Gamma qP b1 b2)
    {w : Q'} (hw : (0 : Q') ≤ w) (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (mixedRepairSource repair) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  let source := mixedRepairSource repair
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    repair.block
  · apply nodup_flatMap_of_pairwise_disjoint source repair.block
      (nodup_filter_bool _ _
        (threeBranchResidualSource_nodup Gamma qP b1 b2))
    · intro entry hentry
      exact repair.block_nodup entry (List.mem_filter.mp hentry).2
    · intro a ha b hb hab code hcode
      exact repair.blocks_disjoint a (List.mem_filter.mp ha).2
        b (List.mem_filter.mp hb).2 hab code hcode
  · intro code hcode
    obtain ⟨entry, hentry, hcodeMem⟩ := List.mem_flatMap.mp hcode
    exact repair.block_mem entry (List.mem_filter.mp hentry).2
      code hcodeMem
  · intro entry hentry
    exact repair.source_le_block hw label entry
      (List.mem_filter.mp hentry).2
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

/-! ## Sharp Boolean fuel invariant for pair-bounced repairs -/

def complementaryFuelBalancedB (fuel : BlockCutFuel) : Bool :=
  decide (fuel.selectedPairs = fuel.reservePairs)

theorem complementaryFuelBalancedB_true_iff (fuel : BlockCutFuel) :
    complementaryFuelBalancedB fuel = true ↔
      (fuel.bouncedVertexLength ≤ fuel.availableOccurrenceCount ∧
        fuel.swap.bouncedVertexLength ≤
          fuel.swap.availableOccurrenceCount) := by
  constructor
  · intro h
    apply (BlockCutFuel.both_complementary_codes_fit_iff_balanced fuel).mpr
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true
      ((BlockCutFuel.both_complementary_codes_fit_iff_balanced fuel).mp h)

theorem balanced_six_cycle_fuel :
    complementaryFuelBalancedB (.leaf 1 1) = true := by rfl

theorem unequal_four_occurrence_fuel :
    complementaryFuelBalancedB (.leaf 1 0) = false := by rfl

/-- The false Boolean corner is an actual target-membership failure, not only
a failure of a sufficient constructor premise. -/
theorem unequal_long_arm_absent_from_unchanged_target
    (Gamma : List (Polymer L))
    (background external : OccBitVec Gamma.length)
    (hcount : Gamma.length = 4) :
    YMGap.Continuum.XiExceptionalEarOccurrenceCarrier.pairedBounceCarrierCode
        Gamma
        YMGap.Continuum.XiExceptionalUnequalEarFuelFence.longArm
        YMGap.Continuum.XiExceptionalUnequalEarFuelFence.lineEdge_symm
        background external ∉ occurrenceCarrierXiCodes Gamma :=
  YMGap.Continuum.XiExceptionalUnequalEarFuelFence.longArm_carrier_not_mem
    Gamma background external hcount

/-! ## The checked six-cycle as the fourth branch -/

namespace SixCycle

open YMGap.Continuum.XiExceptionalMixedEarAbsorption
open YMGap.Continuum.XiExceptionalThreeBranchClassificationFence.SixCycle

def mixedRepairB
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) : Bool :=
  decide (other.1 = pair)

theorem mixedRepairB_true_iff
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) :
    mixedRepairB other = true ↔ other = entry := by
  constructor
  · intro h
    apply Subtype.ext
    exact of_decide_eq_true h
  · intro h
    subst other
    rfl

def allocator : MixedRepairAllocator Gamma qAll markV0 badV3 where
  test := mixedRepairB
  block := fun _ => mixedEarBlock
  block_nodup := by
    intro _ _
    exact mixedEarBlock_nodup
  block_mem := by
    intro _ _ code hcode
    exact mixedEarBlock_mem code hcode
  blocks_disjoint := by
    intro a ha b hb hab
    have hae : a = entry := (mixedRepairB_true_iff a).mp ha
    have hbe : b = entry := (mixedRepairB_true_iff b).mp hb
    exact False.elim (hab (hae.trans hbe.symm))
  source_le_block := by
    intro w hw label other htest
    have hother : other = entry := (mixedRepairB_true_iff other).mp htest
    subst other
    exact mixedSource_le_mixedEarBlock hw label

theorem entry_test_true : allocator.test entry = true := by rfl

theorem entry_mem_mixedRepairSource :
    entry ∈ mixedRepairSource allocator := by
  apply List.mem_filter.mpr
  exact ⟨entry_mem_residual, entry_test_true⟩

theorem entry_not_mem_fourBranchResidual :
    entry ∉ fourBranchResidualSource allocator := by
  intro hentry
  have htest := (fourBranchResidualSource_tests Gamma qAll markV0 badV3
    allocator entry hentry).2.2.2
  rw [entry_test_true] at htest
  cases htest

/-- Exact source factorization used by the fourth-branch payment. -/
theorem source_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label entry.1 ≈
      commonWeight w label * (leftArm w label * rightArm w label) := by
  exact mixedSource_weight_eqv w label

/-- Exact two-code square weight used by the fourth-branch payment. -/
theorem block_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        (allocator.block entry) ≈
      commonWeight w label *
        (leftArm w label * leftArm w label +
          rightArm w label * rightArm w label) := by
  exact mixedEarBlock_weight_eqv w label

theorem entry_paid_by_unchanged_target
    {w : Q'} (hw : (0 : Q') ≤ w)
    (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label entry.1 ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        (allocator.block entry) :=
  allocator.source_le_block hw label entry entry_test_true

theorem repair_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (label : TL.Plaquette → Rep) :
    qListSum (fun other => occurrencePairWeight w qAll markV0 badV3
        Gamma label other.1) (mixedRepairSource allocator) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qAll markV0 badV3
        Gamma label) (occurrenceCarrierXiCodes Gamma) :=
  mixedRepairSource_global_bound allocator hw label

end SixCycle

#print axioms exceptionalSource_fourBranch_residual_partition
#print axioms fourBranchResidualSource_tests
#print axioms mixedRepairSource_global_bound
#print axioms complementaryFuelBalancedB_true_iff
#print axioms balanced_six_cycle_fuel
#print axioms unequal_four_occurrence_fuel
#print axioms unequal_long_arm_absent_from_unchanged_target
#print axioms SixCycle.mixedRepairB_true_iff
#print axioms SixCycle.entry_mem_mixedRepairSource
#print axioms SixCycle.entry_not_mem_fourBranchResidual
#print axioms SixCycle.source_weight_eqv
#print axioms SixCycle.block_weight_eqv
#print axioms SixCycle.entry_paid_by_unchanged_target
#print axioms SixCycle.repair_region_global_bound

end YMGap.Continuum.XiExceptionalFourthMixedRepair
