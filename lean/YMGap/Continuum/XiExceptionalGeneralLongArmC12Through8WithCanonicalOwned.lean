/-
# Joining the seven-bit chart to the native canonical C12 block

The seven-bit parity chart gives 128 source-specific singleton blocks.  The
unique full alternating C12 source already has the native nine-code
multi-reserve block.  These blocks are disjoint: every parity-chart code uses
the three-step short ear `V0,V1,V2,V3`, while none occurs in the canonical
repair family.  The generic owned-family extension therefore joins both
regions without changing either payment certificate.
-/

import YMGap.Continuum.XiExceptionalOwnedFamilyExtension
import YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned

open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalOwnedFamilyExtension
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Native
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

set_option maxRecDepth 1000000 in
theorem outward8CarrierCode_not_mem_canonical
    (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    outward8CarrierCode x4 x5 x6 x7 x8 x9 x11 ∉ canonicalRepairBlock := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;> decide

private theorem outward8_blocks_disjoint_canonical
    (old : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      outward8OwnedFamily.test other = true })
    (code : OccCarrierXiCodeAt G)
    (hcode : code ∈ (outward8OwnedFamily.cert old).block) :
    code ∉ c12PaidResidualBlock.block := by
  have hc : code = outward8CarrierCode
      (sourceTag4 old.1) (sourceTag5 old.1) (sourceTag6 old.1)
      (sourceTag7 old.1) (sourceTag8 old.1) (sourceTag9 old.1)
      (sourceTag11 old.1) := by
    change code ∈ (outward8ChartCert old).block at hcode
    rw [outward8ChartCert_block] at hcode
    simpa using hcode
  subst code
  exact outward8CarrierCode_not_mem_canonical _ _ _ _ _ _ _

/-- The 128 singleton sources and the native canonical source coexist in one
owned family with disjoint target blocks. -/
def through8WithCanonicalOwned :
    OwnedPaidResidualFamily qAll markV0 badV3 G :=
  extendOwnedFamily outward8OwnedFamily entry c12PaidResidualBlock
    outward8_blocks_disjoint_canonical

theorem through8WithCanonical_accepts_canonical :
    through8WithCanonicalOwned.test entry = true :=
  extendOwnedFamily_accepts_fresh outward8OwnedFamily entry
    c12PaidResidualBlock outward8_blocks_disjoint_canonical

theorem through8WithCanonical_accepts_chart
    (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    through8WithCanonicalOwned.test
      (outward8Entry x4 x5 x6 x7 x8 x9 x11) = true := by
  apply extendOwnedFamily_preserves_old outward8OwnedFamily entry
    c12PaidResidualBlock outward8_blocks_disjoint_canonical
  exact outward8OwnedFamily_accepts x4 x5 x6 x7 x8 x9 x11

def through8WithCanonicalGlobal :
    GlobalPaidResidualFamily qAll markV0 badV3 G :=
  through8WithCanonicalOwned.toGlobal

def through8WithCanonicalAllocator :
    MixedRepairAllocator G qAll markV0 badV3 :=
  through8WithCanonicalOwned.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned.outward8CarrierCode_not_mem_canonical
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned.through8WithCanonicalOwned
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned.through8WithCanonical_accepts_canonical
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned.through8WithCanonical_accepts_chart
