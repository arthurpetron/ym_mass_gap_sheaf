/-
# Constructive one-source extension of an owned paid family

The C12 allocator already has a genuine two-source instance, but its ownership
proof is written as a bespoke case split.  This module factors out the exact
inductive operation needed for arbitrary finite source coverage.

Given an owned paid family, a new source-specific paid block, and a proof that
the new block is disjoint from every old selected block, the construction below
extends the Boolean source test and derives a new deterministic owner.  No
payment certificate or disjointness is assumed for a source that was not
explicitly supplied: this is bookkeeping infrastructure, not an inhabitant of
the remaining C12 analytic frontier.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator

namespace YMGap.Continuum.XiExceptionalOwnedFamilyExtension

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator

variable {L : Lattice} [DecidableEq L.Plaquette]
variable {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}

/-- The old source region together with one distinguished new source. -/
def extendedTest
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh : ExceptionalSourceEntry Gamma qP b1 b2)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  if decide (entry = fresh) then true else family.test entry

theorem extendedTest_fresh
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh : ExceptionalSourceEntry Gamma qP b1 b2) :
    extendedTest family fresh fresh = true := by
  simp [extendedTest]

theorem old_test_of_extended_of_ne
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hne : entry ≠ fresh) (htest : extendedTest family fresh entry = true) :
    family.test entry = true := by
  simpa [extendedTest, hne] using htest

/-- Select the fresh paid block at the new source and retain the old
certificate everywhere else. -/
def extendedCert
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh : ExceptionalSourceEntry Gamma qP b1 b2)
    (freshCert : PaidResidualBlock qP b1 b2 Gamma fresh)
    (selected : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      extendedTest family fresh entry = true }) :
    PaidResidualBlock qP b1 b2 Gamma selected.1 := by
  if h : selected.1 = fresh then
    exact h.symm ▸ freshCert
  else
    exact family.cert
      ⟨selected.1, old_test_of_extended_of_ne family fresh selected.1 h selected.2⟩

/-- Codes in the fresh block acquire the fresh owner; every other code keeps
its previous deterministic owner. -/
def extendedOwner
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh : ExceptionalSourceEntry Gamma qP b1 b2)
    (freshCert : PaidResidualBlock qP b1 b2 Gamma fresh)
    (code : OccCarrierXiCodeAt Gamma) :
    ExceptionalSourceEntry Gamma qP b1 b2 :=
  if decide (code ∈ freshCert.block) then fresh else family.owner code

/-- Add one paid source-specific block to an owned family.  The only global
premise is the genuinely necessary one: no code of an old selected block may
occur in the fresh block. -/
def extendOwnedFamily
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh : ExceptionalSourceEntry Gamma qP b1 b2)
    (freshCert : PaidResidualBlock qP b1 b2 Gamma fresh)
    (hdisjoint : ∀ old : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
        family.test entry = true }, ∀ code,
      code ∈ (family.cert old).block → code ∉ freshCert.block) :
    OwnedPaidResidualFamily qP b1 b2 Gamma where
  test := extendedTest family fresh
  cert := extendedCert family fresh freshCert
  owner := extendedOwner family fresh freshCert
  block_owner := by
    rintro ⟨entry, htest⟩ code hcode
    by_cases hfresh : entry = fresh
    · subst entry
      have hmem : code ∈ freshCert.block := by
        simpa [extendedCert] using hcode
      simp [extendedOwner, hmem]
    · have hold : family.test entry = true :=
        old_test_of_extended_of_ne family fresh entry hfresh htest
      have hmemOld : code ∈ (family.cert ⟨entry, hold⟩).block := by
        simpa [extendedCert, hfresh] using hcode
      have hnotFresh : code ∉ freshCert.block :=
        hdisjoint ⟨entry, hold⟩ code hmemOld
      simp only [extendedOwner, hnotFresh, decide_false]
      exact family.block_owner ⟨entry, hold⟩ code hmemOld

theorem extendOwnedFamily_accepts_fresh
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh : ExceptionalSourceEntry Gamma qP b1 b2)
    (freshCert : PaidResidualBlock qP b1 b2 Gamma fresh)
    (hdisjoint : ∀ old : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
        family.test entry = true }, ∀ code,
      code ∈ (family.cert old).block → code ∉ freshCert.block) :
    (extendOwnedFamily family fresh freshCert hdisjoint).test fresh = true :=
  extendedTest_fresh family fresh

theorem extendOwnedFamily_preserves_old
    (family : OwnedPaidResidualFamily qP b1 b2 Gamma)
    (fresh : ExceptionalSourceEntry Gamma qP b1 b2)
    (freshCert : PaidResidualBlock qP b1 b2 Gamma fresh)
    (hdisjoint : ∀ old : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
        family.test entry = true }, ∀ code,
      code ∈ (family.cert old).block → code ∉ freshCert.block)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hold : family.test entry = true) :
    (extendOwnedFamily family fresh freshCert hdisjoint).test entry = true := by
  change extendedTest family fresh entry = true
  unfold extendedTest
  by_cases h : entry = fresh
  · simp [h]
  · simp [h, hold]

end YMGap.Continuum.XiExceptionalOwnedFamilyExtension

#print axioms YMGap.Continuum.XiExceptionalOwnedFamilyExtension.extendedTest_fresh
#print axioms YMGap.Continuum.XiExceptionalOwnedFamilyExtension.old_test_of_extended_of_ne
#print axioms YMGap.Continuum.XiExceptionalOwnedFamilyExtension.extendOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalOwnedFamilyExtension.extendOwnedFamily_accepts_fresh
#print axioms YMGap.Continuum.XiExceptionalOwnedFamilyExtension.extendOwnedFamily_preserves_old
