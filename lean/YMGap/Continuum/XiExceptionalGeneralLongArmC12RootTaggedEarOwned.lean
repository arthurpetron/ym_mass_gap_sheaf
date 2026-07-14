/-
# A root-attached fourth tag for the owned C12 ear chart

The existing tagged short-ear chart records arbitrary compatible subsets of
`V5,V7,V9`.  The next odd C12 occurrence, `V11`, is compatible with every
polymer in that left family but meets the marked right-family polymer `V0`.
It therefore creates a genuinely new root-attached ear in the disagreement
geometry and is rejected by the old three-bit source decoder.

This file records `V11` in the genuine external occurrence mask.  All four
bits give an exact singleton payment, the carrier map is injective, and the
four-bit decoder constructs one owned family covering all sixteen sources.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Native
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

/-- The old three tag bits together with the new root-attached `V11` bit. -/
def rootTaggedEarFamilyPair (x5 x7 x9 x11 : Bool) : MaskPair G.length :=
  (bits12 false true false true false x5 false x7 false x9 false x11,
    bits12 true false true false false false false false false false false false)

theorem rootTaggedEarFamilyPair_mem (x5 x7 x9 x11 : Bool) :
    rootTaggedEarFamilyPair x5 x7 x9 x11 ∈
      exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete _, ?_⟩
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> rfl

def rootTaggedEarFamilyEntry (x5 x7 x9 x11 : Bool) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨rootTaggedEarFamilyPair x5 x7 x9 x11,
    rootTaggedEarFamilyPair_mem x5 x7 x9 x11⟩

def rootTaggedEarFamilyExternal (x5 x7 x9 x11 : Bool) :
    OccBitVec G.length :=
  bits12 false false false false false x5 false x7 false x9 false x11

def rootTaggedEarFamilyList (x5 x7 x9 x11 : Bool) : List (Polymer TL) :=
  (if x5 then [V5] else []) ++
    (if x7 then [V7] else []) ++
      (if x9 then [V9] else []) ++
        (if x11 then [V11] else [])

theorem rootTaggedEarFamilyExternal_selection (x5 x7 x9 x11 : Bool) :
    selectByBits G (rootTaggedEarFamilyExternal x5 x7 x9 x11) =
      rootTaggedEarFamilyList x5 x7 x9 x11 := by
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem rootTaggedEarFamily_left (x5 x7 x9 x11 : Bool) :
    leftFamily G (rootTaggedEarFamilyPair x5 x7 x9 x11) =
      [V1, V3] ++ rootTaggedEarFamilyList x5 x7 x9 x11 := by
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem rootTaggedEarFamily_right (x5 x7 x9 x11 : Bool) :
    rightFamily G (rootTaggedEarFamilyPair x5 x7 x9 x11) = [V0, V2] := by
  rfl

def rootTaggedEarFamilyCarrierCode (x5 x7 x9 x11 : Bool) :
    OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits G) shortEarTail }
    external := rootTaggedEarFamilyExternal x5 x7 x9 x11 }

theorem rootTaggedEarFamilyCarrierCode_mem (x5 x7 x9 x11 : Bool) :
    rootTaggedEarFamilyCarrierCode x5 x7 x9 x11 ∈
      occurrenceCarrierXiCodes G := by
  unfold rootTaggedEarFamilyCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨rootTaggedEarFamilyExternal x5 x7 x9 x11,
    bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, chainFromIndices (emptyBits G) shortEarTail⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨chainFromIndices (emptyBits G) shortEarTail, ?_, rfl⟩
  apply chainFromIndices_mem G (emptyBits G) shortEarTail G.length
  · decide
  · intro i hi
    simp only [shortEarTail, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

theorem rootTaggedEarFamilyCarrierCode_erasure (x5 x7 x9 x11 : Bool) :
    eraseOccCarrierXiCode G
        (rootTaggedEarFamilyCarrierCode x5 x7 x9 x11) =
      ((V0, shortEarErasedChain),
        rootTaggedEarFamilyList x5 x7 x9 x11) := by
  change ((V0, shortEarErasedChain),
      selectByBits G (rootTaggedEarFamilyExternal x5 x7 x9 x11)) = _
  rw [rootTaggedEarFamilyExternal_selection]

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c57 : compatibleB V5 V7 = true := by rfl
private theorem c59 : compatibleB V5 V9 = true := by rfl
private theorem c511 : compatibleB V5 V11 = true := by rfl
private theorem c79 : compatibleB V7 V9 = true := by rfl
private theorem c711 : compatibleB V7 V11 = true := by rfl
private theorem c911 : compatibleB V9 V11 = true := by rfl

/-- The new root-attached class is paid exactly, with the fourth bit stored in
the actual external occurrence mask. -/
theorem rootTaggedEarFamilyCarrierCode_weight_eqv_source
    (x5 x7 x9 x11 : Bool) (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (rootTaggedEarFamilyCarrierCode x5 x7 x9 x11) ≈
      occurrencePairWeight w qAll markV0 badV3 G label
        (rootTaggedEarFamilyPair x5 x7 x9 x11) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (rootTaggedEarFamilyCarrierCode x5 x7 x9 x11) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (rootTaggedEarFamilyCarrierCode x5 x7 x9 x11)) from rfl]
  rw [rootTaggedEarFamilyCarrierCode_erasure]
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label
      (rootTaggedEarFamilyPair x5 x7 x9 x11)
      (rootTaggedEarFamilyPair_mem x5 x7 x9 x11)]
  rw [rootTaggedEarFamily_left, rootTaggedEarFamily_right]
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;>
    simp [rootTaggedEarFamilyList, shortEarErasedChain, carrierXiCodeWeight,
      carrierCodeWeight, qAll, mark_start, chainCodeWeight, c01, c12, c23,
      Bool.not_false, bad_finish, admissibleFamilyWeight,
      familyCompatibleB_cons, familyCompatibleB_nil, List.all_cons,
      List.all_nil, c57, c59, c511, c79, c711, c911,
      familyActivity_cons, familyActivity_nil] <;>
    ring_qeqv

def rootTaggedEarFamilyPaidBlock (x5 x7 x9 x11 : Bool) :
    PaidResidualBlock qAll markV0 badV3 G
      (rootTaggedEarFamilyEntry x5 x7 x9 x11) where
  block := [rootTaggedEarFamilyCarrierCode x5 x7 x9 x11]
  block_nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact rootTaggedEarFamilyCarrierCode_mem x5 x7 x9 x11
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (rootTaggedEarFamilyCarrierCode_weight_eqv_source
        x5 x7 x9 x11 w label)

private theorem external_at5 (x5 x7 x9 x11 : Bool) :
    (rootTaggedEarFamilyExternal x5 x7 x9 x11).at 5 = x5 := by rfl

private theorem external_at7 (x5 x7 x9 x11 : Bool) :
    (rootTaggedEarFamilyExternal x5 x7 x9 x11).at 7 = x7 := by rfl

private theorem external_at9 (x5 x7 x9 x11 : Bool) :
    (rootTaggedEarFamilyExternal x5 x7 x9 x11).at 9 = x9 := by rfl

private theorem external_at11 (x5 x7 x9 x11 : Bool) :
    (rootTaggedEarFamilyExternal x5 x7 x9 x11).at 11 = x11 := by rfl

theorem rootTaggedEarFamilyCarrierCode_injective
    {x5 x7 x9 x11 y5 y7 y9 y11 : Bool}
    (h : rootTaggedEarFamilyCarrierCode x5 x7 x9 x11 =
      rootTaggedEarFamilyCarrierCode y5 y7 y9 y11) :
    x5 = y5 ∧ x7 = y7 ∧ x9 = y9 ∧ x11 = y11 := by
  have hext := congrArg (fun code => code.external) h
  have h5 := congrArg (fun bits => bits.at 5) hext
  have h7 := congrArg (fun bits => bits.at 7) hext
  have h9 := congrArg (fun bits => bits.at 9) hext
  have h11 := congrArg (fun bits => bits.at 11) hext
  simpa [external_at5, external_at7, external_at9, external_at11] using
    And.intro h5 (And.intro h7 (And.intro h9 h11))

/-- Distinct four-bit source tags have disjoint singleton target blocks. -/
theorem rootTaggedEarFamilyBlocks_disjoint
    {x5 x7 x9 x11 y5 y7 y9 y11 : Bool}
    (hne : x5 ≠ y5 ∨ x7 ≠ y7 ∨ x9 ≠ y9 ∨ x11 ≠ y11)
    (code : OccCarrierXiCodeAt G)
    (hx : code ∈ (rootTaggedEarFamilyPaidBlock x5 x7 x9 x11).block)
    (hy : code ∈ (rootTaggedEarFamilyPaidBlock y5 y7 y9 y11).block) :
    False := by
  have hcx : code = rootTaggedEarFamilyCarrierCode x5 x7 x9 x11 := by
    simpa [rootTaggedEarFamilyPaidBlock] using hx
  have hcy : code = rootTaggedEarFamilyCarrierCode y5 y7 y9 y11 := by
    simpa [rootTaggedEarFamilyPaidBlock] using hy
  have hs := rootTaggedEarFamilyCarrierCode_injective (hcx.symm.trans hcy)
  rcases hne with h5 | h7 | h9 | h11
  · exact h5 hs.1
  · exact h7 hs.2.1
  · exact h9 hs.2.2.1
  · exact h11 hs.2.2.2

set_option maxRecDepth 1000000 in
theorem rootTaggedEarFamilyCarrierCode_not_mem_canonical
    (x5 x7 x9 x11 : Bool) :
    rootTaggedEarFamilyCarrierCode x5 x7 x9 x11 ∉ canonicalRepairBlock := by
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> decide

theorem rootTaggedEarFamilyEntry_false (x5 x7 x9 : Bool) :
    rootTaggedEarFamilyEntry x5 x7 x9 false =
      taggedEarFamilyEntry x5 x7 x9 := by
  rfl

theorem rootTaggedEarFamilyCarrierCode_false (x5 x7 x9 : Bool) :
    rootTaggedEarFamilyCarrierCode x5 x7 x9 false =
      taggedEarFamilyCarrierCode x5 x7 x9 := by
  rfl

/-- The old three-bit chart genuinely misses every source with the new root
tag set. -/
theorem oldTaggedEarChart_rejects_root_tag (x5 x7 x9 : Bool) :
    taggedEarChartTest (rootTaggedEarFamilyEntry x5 x7 x9 true) = false := by
  cases x5 <;> cases x7 <;> cases x9 <;> decide

/-! ## One computational owner for all sixteen sources -/

def sourceTag11
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.1.at 11

def decodedRootTaggedEar
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  rootTaggedEarFamilyEntry (sourceTag5 other) (sourceTag7 other)
    (sourceTag9 other) (sourceTag11 other)

def rootTaggedEarChartTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = decodedRootTaggedEar other)

theorem rootTaggedEarChartTest_accepts (x5 x7 x9 x11 : Bool) :
    rootTaggedEarChartTest
      (rootTaggedEarFamilyEntry x5 x7 x9 x11) = true := by
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> rfl

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

def rootTaggedEarChartCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      rootTaggedEarChartTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 := by
  have hselected : selected.1 = decodedRootTaggedEar selected.1 :=
    of_decide_eq_true selected.2
  exact transportPaidResidualBlock hselected
    (rootTaggedEarFamilyPaidBlock (sourceTag5 selected.1)
      (sourceTag7 selected.1) (sourceTag9 selected.1)
      (sourceTag11 selected.1))

theorem rootTaggedEarChartCert_block
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      rootTaggedEarChartTest other = true }) :
    (rootTaggedEarChartCert selected).block =
      [rootTaggedEarFamilyCarrierCode (sourceTag5 selected.1)
        (sourceTag7 selected.1) (sourceTag9 selected.1)
        (sourceTag11 selected.1)] := by
  unfold rootTaggedEarChartCert
  rw [transportPaidResidualBlock_block]
  rfl

def rootTaggedEarChartOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  rootTaggedEarFamilyEntry (code.external.at 5) (code.external.at 7)
    (code.external.at 9) (code.external.at 11)

theorem rootTaggedEarChartOwner_carrier (x5 x7 x9 x11 : Bool) :
    rootTaggedEarChartOwner
        (rootTaggedEarFamilyCarrierCode x5 x7 x9 x11) =
      rootTaggedEarFamilyEntry x5 x7 x9 x11 := by
  rfl

/-- One owned paid family covering the old chart and all eight new
root-attached ears. -/
def rootTaggedEarOwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := rootTaggedEarChartTest
  cert := rootTaggedEarChartCert
  owner := rootTaggedEarChartOwner
  block_owner := by
    intro selected code hcode
    have hselected : selected.1 = decodedRootTaggedEar selected.1 :=
      of_decide_eq_true selected.2
    have hcodeEq : code =
        rootTaggedEarFamilyCarrierCode (sourceTag5 selected.1)
          (sourceTag7 selected.1) (sourceTag9 selected.1)
          (sourceTag11 selected.1) := by
      rw [rootTaggedEarChartCert_block] at hcode
      simpa using hcode
    rw [hcodeEq, rootTaggedEarChartOwner_carrier]
    exact hselected.symm

theorem rootTaggedEarOwnedFamily_accepts (x5 x7 x9 x11 : Bool) :
    rootTaggedEarOwnedFamily.test
      (rootTaggedEarFamilyEntry x5 x7 x9 x11) = true :=
  rootTaggedEarChartTest_accepts x5 x7 x9 x11

theorem rootTaggedEarOwnedFamily_accepts_old (x5 x7 x9 : Bool) :
    rootTaggedEarOwnedFamily.test (taggedEarFamilyEntry x5 x7 x9) = true := by
  exact rootTaggedEarOwnedFamily_accepts x5 x7 x9 false

theorem rootTaggedEarOwnedFamily_accepts_new (x5 x7 x9 : Bool) :
    rootTaggedEarOwnedFamily.test
      (rootTaggedEarFamilyEntry x5 x7 x9 true) = true :=
  rootTaggedEarOwnedFamily_accepts x5 x7 x9 true

def rootTaggedEarGlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  rootTaggedEarOwnedFamily.toGlobal

def rootTaggedEarAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  rootTaggedEarOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.rootTaggedEarFamilyPair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.rootTaggedEarFamilyCarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.rootTaggedEarFamilyPaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.rootTaggedEarFamilyCarrierCode_injective
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.rootTaggedEarFamilyBlocks_disjoint
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.oldTaggedEarChart_rejects_root_tag
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.rootTaggedEarOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned.rootTaggedEarOwnedFamily_accepts_new
