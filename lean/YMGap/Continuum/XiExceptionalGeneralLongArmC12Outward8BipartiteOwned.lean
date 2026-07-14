/-
# The seven-bit C12 ear chart through V8

The `V6` parity-split carrier extends once more: `V8` is compatible with the
entire external target family `V4,V6,V11`.  Thus `V5,V7,V9` remain in the
terminal background and `V4,V6,V8,V11` occupy the external Xi mask.  This
file banks the predecessor's rejection of every `V8` source and constructs
one exact owned/global allocator for all 128 choices of the seven source
bits.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned

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
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def outward8Pair
    (x4 x5 x6 x7 x8 x9 x11 : Bool) : MaskPair G.length :=
  (bits12 false true false true false x5 false x7 false x9 false x11,
    bits12 true false true false x4 false x6 false x8 false false false)

set_option maxRecDepth 1000000 in
theorem outward8Pair_mem (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    outward8Pair x4 x5 x6 x7 x8 x9 x11 ∈
      exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete _, ?_⟩
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;> rfl

def outward8Entry (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨outward8Pair x4 x5 x6 x7 x8 x9 x11,
    outward8Pair_mem x4 x5 x6 x7 x8 x9 x11⟩

def outward8TerminalBits (x5 x7 x9 : Bool) : OccBitVec G.length :=
  bits12 false false false false false x5 false x7 false x9 false false

def outward8ExternalBits (x4 x6 x8 x11 : Bool) : OccBitVec G.length :=
  bits12 false false false false x4 false x6 false x8 false false x11

def outward8TerminalList (x5 x7 x9 : Bool) : List (Polymer TL) :=
  (if x5 then [V5] else []) ++
    (if x7 then [V7] else []) ++
      (if x9 then [V9] else [])

def outward8ExternalList (x4 x6 x8 x11 : Bool) : List (Polymer TL) :=
  (if x4 then [V4] else []) ++
    (if x6 then [V6] else []) ++
      (if x8 then [V8] else []) ++
        (if x11 then [V11] else [])

theorem outward8Terminal_selection (x5 x7 x9 : Bool) :
    selectByBits G (outward8TerminalBits x5 x7 x9) =
      outward8TerminalList x5 x7 x9 := by
  cases x5 <;> cases x7 <;> cases x9 <;> rfl

theorem outward8External_selection (x4 x6 x8 x11 : Bool) :
    selectByBits G (outward8ExternalBits x4 x6 x8 x11) =
      outward8ExternalList x4 x6 x8 x11 := by
  cases x4 <;> cases x6 <;> cases x8 <;> cases x11 <;> rfl

def outward8CarrierCode (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (outward8TerminalBits x5 x7 x9)
          shortEarTail }
    external := outward8ExternalBits x4 x6 x8 x11 }

theorem outward8CarrierCode_mem (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    outward8CarrierCode x4 x5 x6 x7 x8 x9 x11 ∈
      occurrenceCarrierXiCodes G := by
  unfold outward8CarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨outward8ExternalBits x4 x6 x8 x11, bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, chainFromIndices (outward8TerminalBits x5 x7 x9)
    shortEarTail⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨chainFromIndices (outward8TerminalBits x5 x7 x9)
    shortEarTail, ?_, rfl⟩
  apply chainFromIndices_mem G (outward8TerminalBits x5 x7 x9)
    shortEarTail G.length
  · decide
  · intro i hi
    simp only [shortEarTail, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

def outward8ErasedChain (x5 x7 x9 : Bool) : ChainCode TL.Plaquette :=
  .step V1 (.step V2 (.step V3
    (.terminal (outward8TerminalList x5 x7 x9))))

theorem outward8CarrierCode_erasure (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    eraseOccCarrierXiCode G
        (outward8CarrierCode x4 x5 x6 x7 x8 x9 x11) =
      ((V0, outward8ErasedChain x5 x7 x9),
        outward8ExternalList x4 x6 x8 x11) := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;> rfl

theorem outward8_left (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    leftFamily G (outward8Pair x4 x5 x6 x7 x8 x9 x11) =
      [V1, V3] ++ outward8TerminalList x5 x7 x9 ++
        (if x11 then [V11] else []) := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;> rfl

theorem outward8_right (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    rightFamily G (outward8Pair x4 x5 x6 x7 x8 x9 x11) =
      [V0, V2] ++ (if x4 then [V4] else []) ++
        (if x6 then [V6] else []) ++ (if x8 then [V8] else []) := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;> rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c05 : compatibleB V0 V5 = true := by rfl
private theorem c15 : compatibleB V1 V5 = true := by rfl
private theorem c25 : compatibleB V2 V5 = true := by rfl
private theorem c35 : compatibleB V3 V5 = true := by rfl
private theorem c07 : compatibleB V0 V7 = true := by rfl
private theorem c17 : compatibleB V1 V7 = true := by rfl
private theorem c27 : compatibleB V2 V7 = true := by rfl
private theorem c37 : compatibleB V3 V7 = true := by rfl
private theorem c09 : compatibleB V0 V9 = true := by rfl
private theorem c19 : compatibleB V1 V9 = true := by rfl
private theorem c29 : compatibleB V2 V9 = true := by rfl
private theorem c39 : compatibleB V3 V9 = true := by rfl
private theorem c57 : compatibleB V5 V7 = true := by rfl
private theorem c59 : compatibleB V5 V9 = true := by rfl
private theorem c79 : compatibleB V7 V9 = true := by rfl
private theorem c46 : compatibleB V4 V6 = true := by rfl
private theorem c48 : compatibleB V4 V8 = true := by rfl
private theorem c411 : compatibleB V4 V11 = true := by rfl
private theorem c68 : compatibleB V6 V8 = true := by rfl
private theorem c611 : compatibleB V6 V11 = true := by rfl
private theorem c811 : compatibleB V8 V11 = true := by rfl

set_option maxRecDepth 1000000 in
/-- The extended parity split pays every seven-bit source exactly. -/
theorem outward8CarrierCode_weight_eqv_source
    (x4 x5 x6 x7 x8 x9 x11 : Bool) (w : Q')
    (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (outward8CarrierCode x4 x5 x6 x7 x8 x9 x11) ≈
      occurrencePairWeight w qAll markV0 badV3 G label
        (outward8Pair x4 x5 x6 x7 x8 x9 x11) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (outward8CarrierCode x4 x5 x6 x7 x8 x9 x11) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (outward8CarrierCode x4 x5 x6 x7 x8 x9 x11)) from rfl]
  rw [outward8CarrierCode_erasure]
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label
      (outward8Pair x4 x5 x6 x7 x8 x9 x11)
      (outward8Pair_mem x4 x5 x6 x7 x8 x9 x11)]
  rw [outward8_left, outward8_right]
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;>
    simp [outward8ErasedChain, outward8TerminalList,
      outward8ExternalList, carrierXiCodeWeight, carrierCodeWeight,
      qAll, mark_start, chainCodeWeight, c01, c12, c23, Bool.not_false,
      bad_finish, admissibleFamilyWeight, familyCompatibleB_cons,
      familyCompatibleB_nil, List.all_cons, List.all_nil,
      c05, c15, c25, c35, c07, c17, c27, c37,
      c09, c19, c29, c39, c57, c59, c79,
      c46, c48, c411, c68, c611, c811,
      familyActivity_cons, familyActivity_nil] <;>
    ring_qeqv

def outward8PaidBlock (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    PaidResidualBlock qAll markV0 badV3 G
      (outward8Entry x4 x5 x6 x7 x8 x9 x11) where
  block := [outward8CarrierCode x4 x5 x6 x7 x8 x9 x11]
  block_nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact outward8CarrierCode_mem x4 x5 x6 x7 x8 x9 x11
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (outward8CarrierCode_weight_eqv_source
        x4 x5 x6 x7 x8 x9 x11 w label)

def sourceTag8
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.2.at 8

set_option maxRecDepth 1000000 in
/-- The six-bit chart rejects every source carrying the new `V8` tag. -/
theorem bipartiteEarChart_rejects_outward8
    (x4 x5 x6 x7 x9 x11 : Bool) :
    bipartiteEarChartTest
      (outward8Entry x4 x5 x6 x7 true x9 x11) = false := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;> decide

def decodedOutward8
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  outward8Entry (sourceTag4 other) (sourceTag5 other)
    (sourceTag6 other) (sourceTag7 other) (sourceTag8 other)
    (sourceTag9 other) (sourceTag11 other)

def outward8ChartTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = decodedOutward8 other)

set_option maxRecDepth 1000000 in
theorem outward8ChartTest_accepts (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    outward8ChartTest (outward8Entry x4 x5 x6 x7 x8 x9 x11) = true := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;> rfl

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

def outward8ChartCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      outward8ChartTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 := by
  have hs : selected.1 = decodedOutward8 selected.1 :=
    of_decide_eq_true selected.2
  exact transportPaidResidualBlock hs
    (outward8PaidBlock (sourceTag4 selected.1) (sourceTag5 selected.1)
      (sourceTag6 selected.1) (sourceTag7 selected.1)
      (sourceTag8 selected.1) (sourceTag9 selected.1)
      (sourceTag11 selected.1))

theorem outward8ChartCert_block
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      outward8ChartTest other = true }) :
    (outward8ChartCert selected).block =
      [outward8CarrierCode (sourceTag4 selected.1)
        (sourceTag5 selected.1) (sourceTag6 selected.1)
        (sourceTag7 selected.1) (sourceTag8 selected.1)
        (sourceTag9 selected.1) (sourceTag11 selected.1)] := by
  simp [outward8ChartCert, transportPaidResidualBlock_block]
  rfl

def outward8ChartOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  outward8Entry (code.external.at 4)
    ((terminalBitsOf code.carrier.chain).at 5) (code.external.at 6)
    ((terminalBitsOf code.carrier.chain).at 7) (code.external.at 8)
    ((terminalBitsOf code.carrier.chain).at 9) (code.external.at 11)

theorem outward8ChartOwner_carrier (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    outward8ChartOwner (outward8CarrierCode x4 x5 x6 x7 x8 x9 x11) =
      outward8Entry x4 x5 x6 x7 x8 x9 x11 := by
  rfl

def outward8OwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := outward8ChartTest
  cert := outward8ChartCert
  owner := outward8ChartOwner
  block_owner := by
    intro selected code hcode
    have hs : selected.1 = decodedOutward8 selected.1 :=
      of_decide_eq_true selected.2
    have hc : code = outward8CarrierCode
        (sourceTag4 selected.1) (sourceTag5 selected.1)
        (sourceTag6 selected.1) (sourceTag7 selected.1)
        (sourceTag8 selected.1) (sourceTag9 selected.1)
        (sourceTag11 selected.1) := by
      rw [outward8ChartCert_block] at hcode
      simpa using hcode
    rw [hc, outward8ChartOwner_carrier]
    exact hs.symm

theorem outward8OwnedFamily_accepts (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    outward8OwnedFamily.test
      (outward8Entry x4 x5 x6 x7 x8 x9 x11) = true :=
  outward8ChartTest_accepts x4 x5 x6 x7 x8 x9 x11

def outward8GlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  outward8OwnedFamily.toGlobal

def outward8Allocator : MixedRepairAllocator G qAll markV0 badV3 :=
  outward8OwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned.outward8Pair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned.outward8CarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned.outward8PaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned.bipartiteEarChart_rejects_outward8
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned.outward8OwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned.outward8OwnedFamily_accepts
