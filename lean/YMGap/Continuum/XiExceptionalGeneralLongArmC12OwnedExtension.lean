/-
# Reconstructing the genuine two-source C12 family by one-source extension

This module validates the generic owned-family extension on the existing C12
data.  Starting with the native canonical source and its nine-code block, it
adds the distinct short-ear source and its source-specific singleton block.
The required disjointness is the already machine-checked fact that the short
ear carrier does not occur in the canonical block.

This reconstructs two-source coverage through the reusable inductive API.  It
does not yet synthesize paid blocks for every remaining C12 source.
-/

import YMGap.Continuum.XiExceptionalOwnedFamilyExtension
import YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension

open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Native
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned
open YMGap.Continuum.XiExceptionalOwnedFamilyExtension

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma
abbrev qP := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.qAll
abbrev b1 := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.markV0
abbrev b2 := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.badV3
abbrev canonicalEntry :=
  YMGap.Continuum.XiExceptionalExternalReserveLimitFence.entry

set_option maxRecDepth 1000000

private theorem native_selected_eq_canonical
    (old : { other : ExceptionalSourceEntry G qP b1 b2 //
      c12OwnedFamily.test other = true }) :
    old.1 = canonicalEntry := by
  exact (c12Test_true_iff old.1).mp old.2

private theorem canonical_block_disjoint_shortEar
    (old : { other : ExceptionalSourceEntry G qP b1 b2 //
      c12OwnedFamily.test other = true })
    (code : OccCarrierXiCodeAt G)
    (hcode : code ∈ (c12OwnedFamily.cert old).block) :
    code ∉ shortEarPaidResidualBlock.block := by
  have hold : old.1 = canonicalEntry := native_selected_eq_canonical old
  have hcanonical : code ∈ canonicalRepairBlock := by
    have hcert : (c12OwnedFamily.cert old).block = canonicalRepairBlock := by
      cases old with
      | mk value property =>
          dsimp only at hold
          subst value
          rfl
    exact hcert ▸ hcode
  intro hshort
  have hcodeEq : code = shortEarCarrierCode := by
    simpa [shortEarPaidResidualBlock] using hshort
  subst code
  exact shortEarCarrierCode_not_mem_canonical hcanonical

/-- The generic one-source extension reconstructs a genuine owned C12 family
accepting both the canonical source and the short ear. -/
def extendedC12TwoSource : OwnedPaidResidualFamily qP b1 b2 G :=
  extendOwnedFamily c12OwnedFamily shortEarEntry shortEarPaidResidualBlock
    canonical_block_disjoint_shortEar

theorem extendedC12_accepts_canonical :
    extendedC12TwoSource.test canonicalEntry = true := by
  exact extendOwnedFamily_preserves_old
    c12OwnedFamily shortEarEntry shortEarPaidResidualBlock
      canonical_block_disjoint_shortEar canonicalEntry c12_entry_test_true

theorem extendedC12_accepts_shortEar :
    extendedC12TwoSource.test shortEarEntry = true :=
  extendOwnedFamily_accepts_fresh
    c12OwnedFamily shortEarEntry shortEarPaidResidualBlock
      canonical_block_disjoint_shortEar

theorem extendedC12_canonical_block :
    (extendedC12TwoSource.cert
      ⟨canonicalEntry, extendedC12_accepts_canonical⟩).block =
        canonicalRepairBlock := by
  rfl

theorem extendedC12_shortEar_block :
    (extendedC12TwoSource.cert
      ⟨shortEarEntry, extendedC12_accepts_shortEar⟩).block =
        [shortEarCarrierCode] := by
  rfl

end YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension.extendedC12TwoSource
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension.extendedC12_accepts_canonical
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension.extendedC12_accepts_shortEar
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension.extendedC12_canonical_block
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension.extendedC12_shortEar_block
