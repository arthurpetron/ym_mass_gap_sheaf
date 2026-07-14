/-
# Owned allocation for the complete tagged-ear chart

The three external tag bits are decoded directly from a source's left mask and
from a target code's external mask.  A Boolean test accepts exactly sources
equal to the tagged-ear template reconstructed from their own three bits.  This
turns the parametric exact singleton payments into one computationally owned
family covering all eight tagged ears; pairwise target disjointness is then a
derived theorem of `OwnedPaidResidualFamily`, not an added assumption.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned

open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def sourceTag5
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.1.at 5

def sourceTag7
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.1.at 7

def sourceTag9
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.1.at 9

def decodedTaggedEar
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  taggedEarFamilyEntry (sourceTag5 other) (sourceTag7 other) (sourceTag9 other)

/-- The chart test is computational and recognizes exactly a source reconstructed
from its three off-path tag bits. -/
def taggedEarChartTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = decodedTaggedEar other)

theorem taggedEarChartTest_accepts (x5 x7 x9 : Bool) :
    taggedEarChartTest (taggedEarFamilyEntry x5 x7 x9) = true := by
  cases x5 <;> cases x7 <;> cases x9 <;> rfl

private def transportPaidResidualBlock
    {a b : ExceptionalSourceEntry G qAll markV0 badV3} (h : a = b)
    (block : PaidResidualBlock qAll markV0 badV3 G b) :
    PaidResidualBlock qAll markV0 badV3 G a := by
  cases h
  exact block

private theorem transportPaidResidualBlock_block
    {a b : ExceptionalSourceEntry G qAll markV0 badV3} (h : a = b)
    (block : PaidResidualBlock qAll markV0 badV3 G b) :
    (transportPaidResidualBlock h block).block = block.block := by
  cases h
  rfl

def taggedEarChartCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      taggedEarChartTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 := by
  have hselected : selected.1 = decodedTaggedEar selected.1 :=
    of_decide_eq_true selected.2
  exact transportPaidResidualBlock hselected
    (taggedEarFamilyPaidBlock (sourceTag5 selected.1)
      (sourceTag7 selected.1) (sourceTag9 selected.1))

theorem taggedEarChartCert_block
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      taggedEarChartTest other = true }) :
    (taggedEarChartCert selected).block =
      [taggedEarFamilyCarrierCode (sourceTag5 selected.1)
        (sourceTag7 selected.1) (sourceTag9 selected.1)] := by
  unfold taggedEarChartCert
  rw [transportPaidResidualBlock_block]
  rfl

/-- Decode target ownership from the same genuine external occurrence bits. -/
def taggedEarChartOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  taggedEarFamilyEntry (code.external.at 5) (code.external.at 7)
    (code.external.at 9)

theorem taggedEarChartOwner_carrier (x5 x7 x9 : Bool) :
    taggedEarChartOwner (taggedEarFamilyCarrierCode x5 x7 x9) =
      taggedEarFamilyEntry x5 x7 x9 := by
  rfl

/-- One owned paid family covering every one of the eight tagged-ear sources. -/
def taggedEarOwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := taggedEarChartTest
  cert := taggedEarChartCert
  owner := taggedEarChartOwner
  block_owner := by
    intro selected code hcode
    have hselected : selected.1 = decodedTaggedEar selected.1 :=
      of_decide_eq_true selected.2
    have hcodeEq : code =
        taggedEarFamilyCarrierCode (sourceTag5 selected.1)
          (sourceTag7 selected.1) (sourceTag9 selected.1) := by
      rw [taggedEarChartCert_block] at hcode
      simpa using hcode
    rw [hcodeEq, taggedEarChartOwner_carrier]
    exact hselected.symm

theorem taggedEarOwnedFamily_accepts (x5 x7 x9 : Bool) :
    taggedEarOwnedFamily.test (taggedEarFamilyEntry x5 x7 x9) = true :=
  taggedEarChartTest_accepts x5 x7 x9

/-- The global allocator and all cross-source block-disjointness are now derived
for the full tagged-ear chart. -/
def taggedEarGlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  taggedEarOwnedFamily.toGlobal

def taggedEarAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  taggedEarOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned.taggedEarChartTest_accepts
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned.taggedEarChartCert
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned.taggedEarChartOwner_carrier
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned.taggedEarOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned.taggedEarOwnedFamily_accepts
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned.taggedEarGlobalFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned.taggedEarAllocator
