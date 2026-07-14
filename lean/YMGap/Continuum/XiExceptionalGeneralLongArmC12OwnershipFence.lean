/-
# The canonical C12 block cannot own two actual sources

The native C12 word normalization pays the canonical alternating source, but
its nine target codes carry no source-dependent tag.  This file makes the
resulting global obstruction concrete on the standard ordered C12 ambient
family.  Besides the canonical source, the four-vertex short-ear truncation
is itself an actual exceptional source.  A constructive two-source test can
recognize both entries, but the shared short carrier cannot be owned by both.

Thus no `OwnedPaidResidualFamily` accepting these two sources can retain the
same canonical repair block for each source.  Any genuine multi-source
extension must change the target codes (or otherwise add a recoverable
source-dependent tag); merely widening the canonical source test is
machine-refuted here.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12Native

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Native

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

/-- The short marked-to-bad ear, without either long-arm tail, is already an
actual exceptional source in the same ordered C12 ambient family. -/
def shortEarPair : MaskPair G.length :=
  (bits12 false true false true false false false false false false false false,
    bits12 true false true false false false false false false false false false)

theorem shortEarPair_mem :
    shortEarPair ∈ exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  exact ⟨maskPairs_complete shortEarPair, rfl⟩

def shortEarEntry : ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨shortEarPair, shortEarPair_mem⟩

theorem canonical_ne_shortEar : entry ≠ shortEarEntry := by
  decide

/-- A finite constructive source test recognizing exactly the two concrete
entries under study.  Its existence is not the obstruction. -/
def twoSourceTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = entry) || decide (other = shortEarEntry)

theorem twoSourceTest_canonical : twoSourceTest entry = true := by
  rfl

theorem twoSourceTest_shortEar : twoSourceTest shortEarEntry = true := by
  rfl

theorem twoSourceTest_cases
    (other : ExceptionalSourceEntry G qAll markV0 badV3)
    (htest : twoSourceTest other = true) :
    other = entry ∨ other = shortEarEntry := by
  unfold twoSourceTest at htest
  cases hcanonical : decide (other = entry) with
  | true => exact Or.inl (of_decide_eq_true hcanonical)
  | false =>
      have hshort : decide (other = shortEarEntry) = true := by
        simpa [hcanonical] using htest
      exact Or.inr (of_decide_eq_true hshort)

abbrev canonicalRepairBlock : List (OccCarrierXiCodeAt G) :=
  repairCarrierFamily G 1 (by rfl)

abbrev sharedShortCode : OccCarrierXiCodeAt G :=
  shortCarrierCode G 1 (by rfl)

theorem sharedShortCode_mem : sharedShortCode ∈ canonicalRepairBlock :=
  List.mem_cons_self

/-- The fixed C12 carrier tags have no deterministic owner assigning the
whole canonical block to both actual sources.  The first short carrier is an
explicit collision witness. -/
theorem no_two_source_owner_on_canonical_block :
    ¬ ∃ owner : OccCarrierXiCodeAt G →
        ExceptionalSourceEntry G qAll markV0 badV3,
      (∀ code, code ∈ canonicalRepairBlock → owner code = entry) ∧
      (∀ code, code ∈ canonicalRepairBlock → owner code = shortEarEntry) := by
  rintro ⟨owner, hcanonical, hshort⟩
  have hc := hcanonical sharedShortCode sharedShortCode_mem
  have hs := hshort sharedShortCode sharedShortCode_mem
  exact canonical_ne_shortEar (Eq.trans hc.symm hs)

/-- Ownership itself forces the selected blocks of the two distinct sources
to be disjoint, independently of how their local payment certificates were
constructed. -/
theorem owned_two_source_blocks_have_no_common_code
    (family : OwnedPaidResidualFamily qAll markV0 badV3 G)
    (hcanonical : family.test entry = true)
    (hshort : family.test shortEarEntry = true)
    (code : OccCarrierXiCodeAt G)
    (hc : code ∈ (family.cert ⟨entry, hcanonical⟩).block)
    (hs : code ∈ (family.cert ⟨shortEarEntry, hshort⟩).block) : False := by
  have ownerCanonical :=
    family.block_owner ⟨entry, hcanonical⟩ code hc
  have ownerShort :=
    family.block_owner ⟨shortEarEntry, hshort⟩ code hs
  exact canonical_ne_shortEar (Eq.trans ownerCanonical.symm ownerShort)

/-- Exact C12 obstruction: there is no owned paid family which accepts both
actual sources while assigning the unchanged canonical nine-code repair
block to every selected source. -/
theorem no_owned_two_source_canonical_blocks :
    ¬ ∃ family : OwnedPaidResidualFamily qAll markV0 badV3 G,
      family.test entry = true ∧
      family.test shortEarEntry = true ∧
      ∀ selected,
        (family.cert selected).block = canonicalRepairBlock := by
  rintro ⟨family, hcanonical, hshort, hblock⟩
  apply owned_two_source_blocks_have_no_common_code family
    hcanonical hshort sharedShortCode
  · rw [hblock ⟨entry, hcanonical⟩]
    exact sharedShortCode_mem
  · rw [hblock ⟨shortEarEntry, hshort⟩]
    exact sharedShortCode_mem

/-- In particular the native one-source family genuinely rejects the second
actual source; widening only its test would violate ownership. -/
theorem native_family_rejects_shortEar :
    c12OwnedFamily.test shortEarEntry = false := by
  rfl

#print axioms shortEarPair_mem
#print axioms canonical_ne_shortEar
#print axioms twoSourceTest_cases
#print axioms no_two_source_owner_on_canonical_block
#print axioms owned_two_source_blocks_have_no_common_code
#print axioms no_owned_two_source_canonical_blocks
#print axioms native_family_rejects_shortEar

end YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
