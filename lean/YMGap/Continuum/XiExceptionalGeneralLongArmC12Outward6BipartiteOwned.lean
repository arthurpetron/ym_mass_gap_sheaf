/-
# The six-bit bipartite C12 ear chart

The first outward right-family occurrence `V6` touches both `V5` and `V7`,
so it cannot be inserted into either of the mixed target families used by the
five-bit chart.  The source has a stronger invariant: its optional odd
occurrences all belong to the left family and its optional even occurrences
all belong to the right family.  Put `V5,V7,V9` in the terminal background
of the connecting chain and `V4,V6,V11` in the external Xi mask.  The
wraparound tag `V11` must stay external because it touches the marked start
`V0`; it is compatible with both even external tags.  Both target layers are
therefore compatible, and their product is exactly the source monomial;
cross-layer contacts need no compatibility assumption.

This gives exact singleton payments for all sixty-four choices of the six
bits.  A computational decoder and owner turn them into one owned/global
allocator.  Before extending the chart, the file banks that every source
with `V6` present is rejected by the preceding five-bit owner.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned

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
open YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def bipartiteEarPair
    (x4 x5 x6 x7 x9 x11 : Bool) : MaskPair G.length :=
  (bits12 false true false true false x5 false x7 false x9 false x11,
    bits12 true false true false x4 false x6 false false false false false)

set_option maxRecDepth 1000000 in
theorem bipartiteEarPair_mem (x4 x5 x6 x7 x9 x11 : Bool) :
    bipartiteEarPair x4 x5 x6 x7 x9 x11 ∈
      exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete _, ?_⟩
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;> rfl

def bipartiteEarEntry (x4 x5 x6 x7 x9 x11 : Bool) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨bipartiteEarPair x4 x5 x6 x7 x9 x11,
    bipartiteEarPair_mem x4 x5 x6 x7 x9 x11⟩

def bipartiteEarTerminalBits (x5 x7 x9 : Bool) :
    OccBitVec G.length :=
  bits12 false false false false false x5 false x7 false x9 false false

def bipartiteEarExternalBits (x4 x6 x11 : Bool) : OccBitVec G.length :=
  bits12 false false false false x4 false x6 false false false false x11

def bipartiteEarTerminalList (x5 x7 x9 : Bool) : List (Polymer TL) :=
  (if x5 then [V5] else []) ++
    (if x7 then [V7] else []) ++
      (if x9 then [V9] else [])

def bipartiteEarExternalList (x4 x6 x11 : Bool) : List (Polymer TL) :=
  (if x4 then [V4] else []) ++
    (if x6 then [V6] else []) ++
      (if x11 then [V11] else [])

theorem bipartiteEarTerminal_selection (x5 x7 x9 : Bool) :
    selectByBits G (bipartiteEarTerminalBits x5 x7 x9) =
      bipartiteEarTerminalList x5 x7 x9 := by
  cases x5 <;> cases x7 <;> cases x9 <;> rfl

theorem bipartiteEarExternal_selection (x4 x6 x11 : Bool) :
    selectByBits G (bipartiteEarExternalBits x4 x6 x11) =
      bipartiteEarExternalList x4 x6 x11 := by
  cases x4 <;> cases x6 <;> cases x11 <;> rfl

def bipartiteEarCarrierCode (x4 x5 x6 x7 x9 x11 : Bool) :
    OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices
          (bipartiteEarTerminalBits x5 x7 x9) shortEarTail }
    external := bipartiteEarExternalBits x4 x6 x11 }

theorem bipartiteEarCarrierCode_mem (x4 x5 x6 x7 x9 x11 : Bool) :
    bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11 ∈
      occurrenceCarrierXiCodes G := by
  unfold bipartiteEarCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨bipartiteEarExternalBits x4 x6 x11, bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, chainFromIndices
    (bipartiteEarTerminalBits x5 x7 x9) shortEarTail⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨chainFromIndices
    (bipartiteEarTerminalBits x5 x7 x9) shortEarTail, ?_, rfl⟩
  apply chainFromIndices_mem G
    (bipartiteEarTerminalBits x5 x7 x9) shortEarTail G.length
  · decide
  · intro i hi
    simp only [shortEarTail, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

def bipartiteEarErasedChain (x5 x7 x9 : Bool) :
    ChainCode TL.Plaquette :=
  .step V1 (.step V2 (.step V3
    (.terminal (bipartiteEarTerminalList x5 x7 x9))))

theorem bipartiteEarCarrierCode_erasure (x4 x5 x6 x7 x9 x11 : Bool) :
    eraseOccCarrierXiCode G
        (bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11) =
      ((V0, bipartiteEarErasedChain x5 x7 x9),
        bipartiteEarExternalList x4 x6 x11) := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;> rfl

theorem bipartiteEar_left (x4 x5 x6 x7 x9 x11 : Bool) :
    leftFamily G (bipartiteEarPair x4 x5 x6 x7 x9 x11) =
      [V1, V3] ++ bipartiteEarTerminalList x5 x7 x9 ++
        (if x11 then [V11] else []) := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;> rfl

theorem bipartiteEar_right (x4 x5 x6 x7 x9 x11 : Bool) :
    rightFamily G (bipartiteEarPair x4 x5 x6 x7 x9 x11) =
      [V0, V2] ++ (if x4 then [V4] else []) ++
        (if x6 then [V6] else []) := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;> rfl

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
private theorem c411 : compatibleB V4 V11 = true := by rfl
private theorem c611 : compatibleB V6 V11 = true := by rfl

set_option maxRecDepth 1000000 in
/-- The parity split pays every one of the sixty-four six-bit sources by one
target code.  No cross-layer compatibility claim is used. -/
theorem bipartiteEarCarrierCode_weight_eqv_source
    (x4 x5 x6 x7 x9 x11 : Bool) (w : Q')
    (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11) ≈
      occurrencePairWeight w qAll markV0 badV3 G label
        (bipartiteEarPair x4 x5 x6 x7 x9 x11) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11)) from rfl]
  rw [bipartiteEarCarrierCode_erasure]
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label
      (bipartiteEarPair x4 x5 x6 x7 x9 x11)
      (bipartiteEarPair_mem x4 x5 x6 x7 x9 x11)]
  rw [bipartiteEar_left, bipartiteEar_right]
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;>
    simp [bipartiteEarErasedChain, bipartiteEarTerminalList,
      bipartiteEarExternalList, carrierXiCodeWeight, carrierCodeWeight,
      qAll, mark_start, chainCodeWeight, c01, c12, c23, Bool.not_false,
      bad_finish, admissibleFamilyWeight, familyCompatibleB_cons,
      familyCompatibleB_nil, List.all_cons, List.all_nil,
      c05, c15, c25, c35, c07, c17, c27, c37,
      c09, c19, c29, c39, c57, c59, c79, c46, c411, c611,
      familyActivity_cons, familyActivity_nil] <;>
    ring_qeqv

def bipartiteEarPaidBlock (x4 x5 x6 x7 x9 x11 : Bool) :
    PaidResidualBlock qAll markV0 badV3 G
      (bipartiteEarEntry x4 x5 x6 x7 x9 x11) where
  block := [bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11]
  block_nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact bipartiteEarCarrierCode_mem x4 x5 x6 x7 x9 x11
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (bipartiteEarCarrierCode_weight_eqv_source
        x4 x5 x6 x7 x9 x11 w label)

private theorem terminal_at5 (x5 x7 x9 : Bool) :
    (bipartiteEarTerminalBits x5 x7 x9).at 5 = x5 := by rfl
private theorem terminal_at7 (x5 x7 x9 : Bool) :
    (bipartiteEarTerminalBits x5 x7 x9).at 7 = x7 := by rfl
private theorem terminal_at9 (x5 x7 x9 : Bool) :
    (bipartiteEarTerminalBits x5 x7 x9).at 9 = x9 := by rfl
private theorem external_at4 (x4 x6 x11 : Bool) :
    (bipartiteEarExternalBits x4 x6 x11).at 4 = x4 := by rfl
private theorem external_at6 (x4 x6 x11 : Bool) :
    (bipartiteEarExternalBits x4 x6 x11).at 6 = x6 := by rfl
private theorem external_at11 (x4 x6 x11 : Bool) :
    (bipartiteEarExternalBits x4 x6 x11).at 11 = x11 := by rfl

theorem bipartiteEarCarrierCode_injective
    {x4 x5 x6 x7 x9 x11 y4 y5 y6 y7 y9 y11 : Bool}
    (h : bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11 =
      bipartiteEarCarrierCode y4 y5 y6 y7 y9 y11) :
    x4 = y4 ∧ x5 = y5 ∧ x6 = y6 ∧ x7 = y7 ∧ x9 = y9 ∧ x11 = y11 := by
  have ht := congrArg (fun code => terminalBitsOf code.carrier.chain) h
  have he := congrArg (fun code => code.external) h
  have h4 := congrArg (fun bits => bits.at 4) he
  have h5 := congrArg (fun bits => bits.at 5) ht
  have h6 := congrArg (fun bits => bits.at 6) he
  have h7 := congrArg (fun bits => bits.at 7) ht
  have h9 := congrArg (fun bits => bits.at 9) ht
  have h11 := congrArg (fun bits => bits.at 11) he
  simpa [terminal_at5, terminal_at7, terminal_at9,
    external_at4, external_at6, external_at11] using
      And.intro h4 (And.intro h5 (And.intro h6
        (And.intro h7 (And.intro h9 h11))))

set_option maxRecDepth 1000000 in
theorem bipartiteEarCarrierCode_not_mem_canonical
    (x4 x5 x6 x7 x9 x11 : Bool) :
    bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11 ∉
      canonicalRepairBlock := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;> decide

/-! ## Rejection fence and the sixty-four-source owner -/

def sourceTag6
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.2.at 6

set_option maxRecDepth 1000000 in
/-- The preceding chart has no `V6` coordinate and rejects every new outward
source, independent of its other five local bits. -/
theorem fullLocalEarChart_rejects_outward6
    (x4 x5 x7 x9 x11 : Bool) :
    fullLocalEarChartTest
      (bipartiteEarEntry x4 x5 true x7 x9 x11) = false := by
  cases x4 <;> cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> decide

def decodedBipartiteEar
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  bipartiteEarEntry (sourceTag4 other) (sourceTag5 other)
    (sourceTag6 other) (sourceTag7 other) (sourceTag9 other)
    (sourceTag11 other)

def bipartiteEarChartTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = decodedBipartiteEar other)

set_option maxRecDepth 1000000 in
theorem bipartiteEarChartTest_accepts (x4 x5 x6 x7 x9 x11 : Bool) :
    bipartiteEarChartTest
      (bipartiteEarEntry x4 x5 x6 x7 x9 x11) = true := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x9 <;> cases x11 <;> rfl

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

def bipartiteEarChartCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      bipartiteEarChartTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 := by
  have hs : selected.1 = decodedBipartiteEar selected.1 :=
    of_decide_eq_true selected.2
  exact transportPaidResidualBlock hs
    (bipartiteEarPaidBlock (sourceTag4 selected.1) (sourceTag5 selected.1)
      (sourceTag6 selected.1) (sourceTag7 selected.1)
      (sourceTag9 selected.1) (sourceTag11 selected.1))

theorem bipartiteEarChartCert_block
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      bipartiteEarChartTest other = true }) :
    (bipartiteEarChartCert selected).block =
      [bipartiteEarCarrierCode (sourceTag4 selected.1)
        (sourceTag5 selected.1) (sourceTag6 selected.1)
        (sourceTag7 selected.1) (sourceTag9 selected.1)
        (sourceTag11 selected.1)] := by
  simp [bipartiteEarChartCert, transportPaidResidualBlock_block]
  rfl

def bipartiteEarChartOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  bipartiteEarEntry (code.external.at 4)
    ((terminalBitsOf code.carrier.chain).at 5) (code.external.at 6)
    ((terminalBitsOf code.carrier.chain).at 7)
    ((terminalBitsOf code.carrier.chain).at 9)
    (code.external.at 11)

theorem bipartiteEarChartOwner_carrier (x4 x5 x6 x7 x9 x11 : Bool) :
    bipartiteEarChartOwner
        (bipartiteEarCarrierCode x4 x5 x6 x7 x9 x11) =
      bipartiteEarEntry x4 x5 x6 x7 x9 x11 := by
  rfl

def bipartiteEarOwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := bipartiteEarChartTest
  cert := bipartiteEarChartCert
  owner := bipartiteEarChartOwner
  block_owner := by
    intro selected code hcode
    have hs : selected.1 = decodedBipartiteEar selected.1 :=
      of_decide_eq_true selected.2
    have hc : code = bipartiteEarCarrierCode
        (sourceTag4 selected.1) (sourceTag5 selected.1)
        (sourceTag6 selected.1) (sourceTag7 selected.1)
        (sourceTag9 selected.1) (sourceTag11 selected.1) := by
      rw [bipartiteEarChartCert_block] at hcode
      simpa using hcode
    rw [hc, bipartiteEarChartOwner_carrier]
    exact hs.symm

theorem bipartiteEarOwnedFamily_accepts (x4 x5 x6 x7 x9 x11 : Bool) :
    bipartiteEarOwnedFamily.test
      (bipartiteEarEntry x4 x5 x6 x7 x9 x11) = true :=
  bipartiteEarChartTest_accepts x4 x5 x6 x7 x9 x11

def bipartiteEarGlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  bipartiteEarOwnedFamily.toGlobal

def bipartiteEarAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  bipartiteEarOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned.bipartiteEarPair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned.bipartiteEarCarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned.bipartiteEarPaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned.bipartiteEarCarrierCode_injective
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned.fullLocalEarChart_rejects_outward6
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned.bipartiteEarOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned.bipartiteEarOwnedFamily_accepts
