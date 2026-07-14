/-
# Global paid-block allocation and the constant-block collision fence

Given local long-arm normalizations, one obtains one paid block per selected
source.  A global mixed-repair allocator additionally needs those blocks to
be disjoint across distinct accepted sources.  This file isolates that exact
invariant, builds the corresponding disjoint allocator from it, and proves
that the canonical fixed-index block cannot satisfy it for two different
source entries.  The structures below do not themselves require `test` to
accept any source; coverage and multi-source non-vacuity remain separate
obligations for each concrete instance.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmUnderdetermination

namespace YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalThreeBranchClassificationFence
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmUnderdetermination
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence

variable {L : Lattice} [DecidableEq L.Plaquette]

/-- The minimal global strengthening of local paid blocks: select a source
region, provide a paid target block for every selected source, and prove that
different selected sources never reuse a target occurrence code. -/
structure GlobalPaidResidualFamily
    (qP b1 b2 : Polymer L → Bool) (Gamma : List (Polymer L)) where
  test : ExceptionalSourceEntry Gamma qP b1 b2 → Bool
  cert : (entry : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      test entry = true }) →
    PaidResidualBlock qP b1 b2 Gamma entry.1
  blocks_disjoint : ∀ a b,
    a.1 ≠ b.1 → ∀ code, code ∈ (cert a).block →
      code ∉ (cert b).block

def GlobalPaidResidualFamily.block
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (family : GlobalPaidResidualFamily qP b1 b2 Gamma)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    List (OccCarrierXiCodeAt Gamma) :=
  if h : family.test entry = true then family.cert ⟨entry, h⟩ |>.block
  else []

/-- A global family supplies the disjoint paid-block data needed by the
fourth-branch allocator on every source accepted by its test.  This
construction does not assert that the accepted region is nonempty. -/
def GlobalPaidResidualFamily.allocator
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (family : GlobalPaidResidualFamily qP b1 b2 Gamma) :
    MixedRepairAllocator Gamma qP b1 b2 where
  test := family.test
  block := family.block
  block_nodup := by
    intro entry ht
    simp only [GlobalPaidResidualFamily.block, dif_pos ht]
    exact (family.cert ⟨entry, ht⟩).block_nodup
  block_mem := by
    intro entry ht code hcode
    simp only [GlobalPaidResidualFamily.block, dif_pos ht] at hcode
    exact (family.cert ⟨entry, ht⟩).block_mem code hcode
  blocks_disjoint := by
    intro a ha b hb hab code hca hcb
    simp only [GlobalPaidResidualFamily.block, dif_pos ha] at hca
    simp only [GlobalPaidResidualFamily.block, dif_pos hb] at hcb
    exact family.blocks_disjoint ⟨a, ha⟩ ⟨b, hb⟩ hab code hca hcb
  source_le_block := by
    intro w hw label entry ht
    simp only [GlobalPaidResidualFamily.block, dif_pos ht]
    exact (family.cert ⟨entry, ht⟩).source_le w hw label

/-! ## A checkable ownership criterion for cross-source disjointness -/

/-- A paid residual family whose target codes carry a deterministic source
owner.  Unlike `GlobalPaidResidualFamily`, this structure does not assume
pairwise block disjointness.  It proves it from the stronger local fact that
every code in a selected block has that block's source as its owner.  This is
the useful global invariant for source-dependent carrier constructions: the
owner is computational data, while disjointness is a derived theorem. -/
structure OwnedPaidResidualFamily
    (qP b1 b2 : Polymer L → Bool) (Gamma : List (Polymer L)) where
  test : ExceptionalSourceEntry Gamma qP b1 b2 → Bool
  cert : (entry : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      test entry = true }) →
    PaidResidualBlock qP b1 b2 Gamma entry.1
  owner : OccCarrierXiCodeAt Gamma → ExceptionalSourceEntry Gamma qP b1 b2
  block_owner : ∀ entry code, code ∈ (cert entry).block →
    owner code = entry.1

/-- Deterministic ownership derives the cross-source block separation needed
by the mixed-repair target sum. -/
def OwnedPaidResidualFamily.toGlobal
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma) :
    GlobalPaidResidualFamily qP b1 b2 Gamma where
  test := family.test
  cert := family.cert
  blocks_disjoint := by
    intro a b hab code hca hcb
    have ha := family.block_owner a code hca
    have hb := family.block_owner b code hcb
    exact hab (Eq.trans ha.symm hb)

/-- A source-owned paid family therefore constructs a globally disjoint
allocator on its tested region without a separate disjointness hypothesis.
Nonempty or multi-source coverage is not implied by this definition. -/
def OwnedPaidResidualFamily.allocator
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma) :
    MixedRepairAllocator Gamma qP b1 b2 :=
  family.toGlobal.allocator

theorem tested_entry_mem_mixedRepairSource
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (family : GlobalPaidResidualFamily qP b1 b2 Gamma)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hresidual : entry ∈ threeBranchResidualSource Gamma qP b1 b2)
    (htest : family.test entry = true) :
    entry ∈ mixedRepairSource family.allocator := by
  apply List.mem_filter.mpr
  exact ⟨hresidual, htest⟩

theorem tested_entry_not_mem_fourBranchResidual
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (family : GlobalPaidResidualFamily qP b1 b2 Gamma)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (htest : family.test entry = true) :
    entry ∉ fourBranchResidualSource family.allocator := by
  intro hmem
  have ht := (fourBranchResidualSource_tests Gamma qP b1 b2
    family.allocator entry hmem).2.2.2
  change family.test entry = false at ht
  rw [htest] at ht
  cases ht

/-! ## The fixed canonical family cannot be global -/

theorem canonical_block_allocator_accepts_at_most_one
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)} {k : Nat}
    (hGamma : Gamma.length = ambientCount k)
    (repair : MixedRepairAllocator Gamma qP b1 b2)
    (hblock : ∀ entry, repair.test entry = true →
      repair.block entry = repairCarrierFamily Gamma k hGamma)
    {a b : ExceptionalSourceEntry Gamma qP b1 b2}
    (ha : repair.test a = true) (hb : repair.test b = true) : a = b := by
  cases heq : decide (a = b) with
  | true => exact of_decide_eq_true heq
  | false =>
      have hab : a ≠ b := of_decide_eq_false heq
      let code := shortCarrierCode Gamma k hGamma
      have hca : code ∈ repair.block a := by
        rw [hblock a ha]
        exact List.mem_cons_self
      have hcb : code ∈ repair.block b := by
        rw [hblock b hb]
        exact List.mem_cons_self
      exact False.elim
        (repair.blocks_disjoint a ha b hb hab code hca hcb)

/-! ## A closed two-source witness for the collision -/

def pairBare : MaskPair GammaSwap.length :=
  (bits12 false true false true false false false false false false false false,
    bits12 true false true false false false false false false false false false)

theorem pairBare_mem :
    pairBare ∈ exceptionalSourceCodes GammaSwap qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  exact ⟨maskPairs_complete pairBare, rfl⟩

def entryBare : ExceptionalSourceEntry GammaSwap qAll markV0 badV3 :=
  ⟨pairBare, pairBare_mem⟩

theorem entrySwap_ne_entryBare : entrySwap ≠ entryBare := by decide

theorem no_two_source_canonical_allocator :
    ¬ ∃ repair : MixedRepairAllocator GammaSwap qAll markV0 badV3,
      repair.test entrySwap = true ∧ repair.test entryBare = true ∧
        ∀ entry, repair.test entry = true →
          repair.block entry =
            repairCarrierFamily GammaSwap 1 GammaSwap_length := by
  rintro ⟨repair, hswap, hbare, hblock⟩
  have heq := canonical_block_allocator_accepts_at_most_one
    GammaSwap_length repair hblock hswap hbare
  exact entrySwap_ne_entryBare heq

#print axioms GlobalPaidResidualFamily.allocator
#print axioms OwnedPaidResidualFamily.toGlobal
#print axioms OwnedPaidResidualFamily.allocator
#print axioms tested_entry_mem_mixedRepairSource
#print axioms tested_entry_not_mem_fourBranchResidual
#print axioms canonical_block_allocator_accepts_at_most_one
#print axioms pairBare_mem
#print axioms entrySwap_ne_entryBare
#print axioms no_two_source_canonical_allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
