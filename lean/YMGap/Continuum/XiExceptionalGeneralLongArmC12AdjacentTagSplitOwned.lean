/-
# Splitting adjacent C12 tags across the two target family layers

The adjacent source tags `V4,V5` cannot share one external family.  The target
carrier, however, has two independent compatible-family layers: the terminal
background of the connecting chain and the external Xi factor.  This file
places `V5,V7,V9` in the terminal background and `V4,V11` in the external
mask.  Their product is exactly the source monomial.

The split carrier pays all eight adjacent-collision sources.  A decoder reads
the collision flag and the `V7,V9` tags from the terminal mask and the `V4,V11`
tags from the external mask.  The resulting owned/global allocator covers all
thirty-two patterns in the local five-bit C12 ear chart.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned

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
open YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def adjacentSplitPair (x7 x9 x11 : Bool) : MaskPair G.length :=
  (bits12 false true false true false true false x7 false x9 false x11,
    bits12 true false true false true false false false false false false false)

theorem adjacentSplitPair_mem (x7 x9 x11 : Bool) :
    adjacentSplitPair x7 x9 x11 ∈
      exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete _, ?_⟩
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

def adjacentSplitEntry (x7 x9 x11 : Bool) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨adjacentSplitPair x7 x9 x11, adjacentSplitPair_mem x7 x9 x11⟩

def adjacentSplitTerminalBits (x7 x9 : Bool) : OccBitVec G.length :=
  bits12 false false false false false true false x7 false x9 false false

def adjacentSplitExternalBits (x11 : Bool) : OccBitVec G.length :=
  bits12 false false false false true false false false false false false x11

def adjacentSplitTerminalList (x7 x9 : Bool) : List (Polymer TL) :=
  [V5] ++ (if x7 then [V7] else []) ++ (if x9 then [V9] else [])

def adjacentSplitExternalList (x11 : Bool) : List (Polymer TL) :=
  [V4] ++ (if x11 then [V11] else [])

theorem adjacentSplitTerminal_selection (x7 x9 : Bool) :
    selectByBits G (adjacentSplitTerminalBits x7 x9) =
      adjacentSplitTerminalList x7 x9 := by
  cases x7 <;> cases x9 <;> rfl

theorem adjacentSplitExternal_selection (x11 : Bool) :
    selectByBits G (adjacentSplitExternalBits x11) =
      adjacentSplitExternalList x11 := by
  cases x11 <;> rfl

def adjacentSplitCarrierCode (x7 x9 x11 : Bool) : OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (adjacentSplitTerminalBits x7 x9)
          shortEarTail }
    external := adjacentSplitExternalBits x11 }

theorem adjacentSplitCarrierCode_mem (x7 x9 x11 : Bool) :
    adjacentSplitCarrierCode x7 x9 x11 ∈ occurrenceCarrierXiCodes G := by
  unfold adjacentSplitCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨adjacentSplitExternalBits x11, bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, chainFromIndices (adjacentSplitTerminalBits x7 x9)
    shortEarTail⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨chainFromIndices (adjacentSplitTerminalBits x7 x9)
    shortEarTail, ?_, rfl⟩
  apply chainFromIndices_mem G (adjacentSplitTerminalBits x7 x9)
    shortEarTail G.length
  · decide
  · intro i hi
    simp only [shortEarTail, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

def adjacentSplitErasedChain (x7 x9 : Bool) : ChainCode TL.Plaquette :=
  .step V1 (.step V2 (.step V3
    (.terminal (adjacentSplitTerminalList x7 x9))))

theorem adjacentSplitCarrierCode_erasure (x7 x9 x11 : Bool) :
    eraseOccCarrierXiCode G (adjacentSplitCarrierCode x7 x9 x11) =
      ((V0, adjacentSplitErasedChain x7 x9),
        adjacentSplitExternalList x11) := by
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem adjacentSplit_left (x7 x9 x11 : Bool) :
    leftFamily G (adjacentSplitPair x7 x9 x11) =
      [V1, V3, V5] ++
        ((if x7 then [V7] else []) ++
          (if x9 then [V9] else []) ++
            (if x11 then [V11] else [])) := by
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem adjacentSplit_right (x7 x9 x11 : Bool) :
    rightFamily G (adjacentSplitPair x7 x9 x11) = [V0, V2, V4] := by
  rfl

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
private theorem c411 : compatibleB V4 V11 = true := by rfl

/-- Splitting the two adjacent tags across the terminal and external family
layers restores exact source weight for every scale and labeling. -/
theorem adjacentSplitCarrierCode_weight_eqv_source
    (x7 x9 x11 : Bool) (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (adjacentSplitCarrierCode x7 x9 x11) ≈
      occurrencePairWeight w qAll markV0 badV3 G label
        (adjacentSplitPair x7 x9 x11) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (adjacentSplitCarrierCode x7 x9 x11) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (adjacentSplitCarrierCode x7 x9 x11)) from rfl]
  rw [adjacentSplitCarrierCode_erasure]
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label (adjacentSplitPair x7 x9 x11)
      (adjacentSplitPair_mem x7 x9 x11)]
  rw [adjacentSplit_left, adjacentSplit_right]
  cases x7 <;> cases x9 <;> cases x11 <;>
    simp [adjacentSplitErasedChain, adjacentSplitTerminalList,
      adjacentSplitExternalList, carrierXiCodeWeight, carrierCodeWeight,
      qAll, mark_start, chainCodeWeight, c01, c12, c23, Bool.not_false,
      bad_finish, admissibleFamilyWeight, familyCompatibleB_cons,
      familyCompatibleB_nil, List.all_cons, List.all_nil,
      c05, c15, c25, c35, c07, c17, c27, c37,
      c09, c19, c29, c39, c57, c59, c79, c411,
      familyActivity_cons, familyActivity_nil] <;>
    ring_qeqv

def adjacentSplitPaidBlock (x7 x9 x11 : Bool) :
    PaidResidualBlock qAll markV0 badV3 G (adjacentSplitEntry x7 x9 x11) where
  block := [adjacentSplitCarrierCode x7 x9 x11]
  block_nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact adjacentSplitCarrierCode_mem x7 x9 x11
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (adjacentSplitCarrierCode_weight_eqv_source x7 x9 x11 w label)

def terminalBitsOf {N : Nat} : OccChainCode N → OccBitVec N
  | .terminal bits => bits
  | .step _ rest => terminalBitsOf rest

private theorem terminal_at7 (x7 x9 : Bool) :
    (adjacentSplitTerminalBits x7 x9).at 7 = x7 := by rfl

private theorem terminal_at9 (x7 x9 : Bool) :
    (adjacentSplitTerminalBits x7 x9).at 9 = x9 := by rfl

private theorem external_at11 (x11 : Bool) :
    (adjacentSplitExternalBits x11).at 11 = x11 := by rfl

theorem adjacentSplitCarrierCode_injective
    {x7 x9 x11 y7 y9 y11 : Bool}
    (h : adjacentSplitCarrierCode x7 x9 x11 =
      adjacentSplitCarrierCode y7 y9 y11) :
    x7 = y7 ∧ x9 = y9 ∧ x11 = y11 := by
  have hterminal := congrArg
    (fun code => terminalBitsOf code.carrier.chain) h
  have h7 := congrArg (fun bits => bits.at 7) hterminal
  have h9 := congrArg (fun bits => bits.at 9) hterminal
  have hext := congrArg (fun code => code.external) h
  have h11 := congrArg (fun bits => bits.at 11) hext
  simpa [terminal_at7, terminal_at9, external_at11] using
    And.intro h7 (And.intro h9 h11)

theorem adjacentSplitBlocks_disjoint
    {x7 x9 x11 y7 y9 y11 : Bool}
    (hne : x7 ≠ y7 ∨ x9 ≠ y9 ∨ x11 ≠ y11)
    (code : OccCarrierXiCodeAt G)
    (hx : code ∈ (adjacentSplitPaidBlock x7 x9 x11).block)
    (hy : code ∈ (adjacentSplitPaidBlock y7 y9 y11).block) : False := by
  have hcx : code = adjacentSplitCarrierCode x7 x9 x11 := by
    simpa [adjacentSplitPaidBlock] using hx
  have hcy : code = adjacentSplitCarrierCode y7 y9 y11 := by
    simpa [adjacentSplitPaidBlock] using hy
  have hs := adjacentSplitCarrierCode_injective (hcx.symm.trans hcy)
  rcases hne with h7 | h9 | h11
  · exact h7 hs.1
  · exact h9 hs.2.1
  · exact h11 hs.2.2

set_option maxRecDepth 1000000 in
theorem adjacentSplitCarrierCode_not_mem_canonical (x7 x9 x11 : Bool) :
    adjacentSplitCarrierCode x7 x9 x11 ∉ canonicalRepairBlock := by
  cases x7 <;> cases x9 <;> cases x11 <;> decide

/-! ## One owner for all thirty-two five-bit patterns -/

def decodedFullLocalEar
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  if sourceTag4 other then
    if sourceTag5 other then
      adjacentSplitEntry (sourceTag7 other) (sourceTag9 other)
        (sourceTag11 other)
    else
      badEndTaggedEarEntry (sourceTag7 other) (sourceTag9 other)
        (sourceTag11 other)
  else
    rootTaggedEarFamilyEntry (sourceTag5 other) (sourceTag7 other)
      (sourceTag9 other) (sourceTag11 other)

def fullLocalEarChartTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = decodedFullLocalEar other)

theorem fullLocalEarChartTest_accepts_root (x5 x7 x9 x11 : Bool) :
    fullLocalEarChartTest (rootTaggedEarFamilyEntry x5 x7 x9 x11) = true := by
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem fullLocalEarChartTest_accepts_badEnd (x7 x9 x11 : Bool) :
    fullLocalEarChartTest (badEndTaggedEarEntry x7 x9 x11) = true := by
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem fullLocalEarChartTest_accepts_split (x7 x9 x11 : Bool) :
    fullLocalEarChartTest (adjacentSplitEntry x7 x9 x11) = true := by
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

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

def fullLocalEarChartCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      fullLocalEarChartTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 := by
  have hselected : selected.1 = decodedFullLocalEar selected.1 :=
    of_decide_eq_true selected.2
  by_cases h4 : sourceTag4 selected.1 = true
  · by_cases h5 : sourceTag5 selected.1 = true
    · have hs : selected.1 =
          adjacentSplitEntry (sourceTag7 selected.1)
            (sourceTag9 selected.1) (sourceTag11 selected.1) := by
        simpa [decodedFullLocalEar, h4, h5] using hselected
      exact transportPaidResidualBlock hs
        (adjacentSplitPaidBlock (sourceTag7 selected.1)
          (sourceTag9 selected.1) (sourceTag11 selected.1))
    · have hs : selected.1 =
          badEndTaggedEarEntry (sourceTag7 selected.1)
            (sourceTag9 selected.1) (sourceTag11 selected.1) := by
        simpa [decodedFullLocalEar, h4, h5] using hselected
      exact transportPaidResidualBlock hs
        (badEndTaggedEarPaidBlock (sourceTag7 selected.1)
          (sourceTag9 selected.1) (sourceTag11 selected.1))
  · have hs : selected.1 =
        rootTaggedEarFamilyEntry (sourceTag5 selected.1)
          (sourceTag7 selected.1) (sourceTag9 selected.1)
          (sourceTag11 selected.1) := by
      simpa [decodedFullLocalEar, h4] using hselected
    exact transportPaidResidualBlock hs
      (rootTaggedEarFamilyPaidBlock (sourceTag5 selected.1)
        (sourceTag7 selected.1) (sourceTag9 selected.1)
        (sourceTag11 selected.1))

theorem fullLocalEarChartCert_block
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      fullLocalEarChartTest other = true }) :
    (fullLocalEarChartCert selected).block =
      [if sourceTag4 selected.1 then
        if sourceTag5 selected.1 then
          adjacentSplitCarrierCode (sourceTag7 selected.1)
            (sourceTag9 selected.1) (sourceTag11 selected.1)
        else
          badEndTaggedEarCarrierCode (sourceTag7 selected.1)
            (sourceTag9 selected.1) (sourceTag11 selected.1)
      else
        rootTaggedEarFamilyCarrierCode (sourceTag5 selected.1)
          (sourceTag7 selected.1) (sourceTag9 selected.1)
          (sourceTag11 selected.1)] := by
  by_cases h4 : sourceTag4 selected.1 = true
  · by_cases h5 : sourceTag5 selected.1 = true
    · simp [fullLocalEarChartCert, h4, h5, transportPaidResidualBlock_block]
      rfl
    · simp [fullLocalEarChartCert, h4, h5, transportPaidResidualBlock_block]
      rfl
  · simp [fullLocalEarChartCert, h4, transportPaidResidualBlock_block]
    rfl

def fullLocalEarChartOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  if code.external.at 4 then
    if (terminalBitsOf code.carrier.chain).at 5 then
      adjacentSplitEntry ((terminalBitsOf code.carrier.chain).at 7)
        ((terminalBitsOf code.carrier.chain).at 9) (code.external.at 11)
    else
      badEndTaggedEarEntry (code.external.at 7) (code.external.at 9)
        (code.external.at 11)
  else
    rootTaggedEarFamilyEntry (code.external.at 5) (code.external.at 7)
      (code.external.at 9) (code.external.at 11)

theorem fullLocalEarChartOwner_root (x5 x7 x9 x11 : Bool) :
    fullLocalEarChartOwner
        (rootTaggedEarFamilyCarrierCode x5 x7 x9 x11) =
      rootTaggedEarFamilyEntry x5 x7 x9 x11 := by
  rfl

theorem fullLocalEarChartOwner_badEnd (x7 x9 x11 : Bool) :
    fullLocalEarChartOwner (badEndTaggedEarCarrierCode x7 x9 x11) =
      badEndTaggedEarEntry x7 x9 x11 := by
  rfl

theorem fullLocalEarChartOwner_split (x7 x9 x11 : Bool) :
    fullLocalEarChartOwner (adjacentSplitCarrierCode x7 x9 x11) =
      adjacentSplitEntry x7 x9 x11 := by
  rfl

def fullLocalEarOwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := fullLocalEarChartTest
  cert := fullLocalEarChartCert
  owner := fullLocalEarChartOwner
  block_owner := by
    intro selected code hcode
    have hselected : selected.1 = decodedFullLocalEar selected.1 :=
      of_decide_eq_true selected.2
    by_cases h4 : sourceTag4 selected.1 = true
    · by_cases h5 : sourceTag5 selected.1 = true
      · have hs : selected.1 =
            adjacentSplitEntry (sourceTag7 selected.1)
              (sourceTag9 selected.1) (sourceTag11 selected.1) := by
          simpa [decodedFullLocalEar, h4, h5] using hselected
        have hc : code =
            adjacentSplitCarrierCode (sourceTag7 selected.1)
              (sourceTag9 selected.1) (sourceTag11 selected.1) := by
          rw [fullLocalEarChartCert_block] at hcode
          simp only [h4, h5, ↓reduceIte] at hcode
          simpa using hcode
        rw [hc, fullLocalEarChartOwner_split]
        exact hs.symm
      · have hs : selected.1 =
            badEndTaggedEarEntry (sourceTag7 selected.1)
              (sourceTag9 selected.1) (sourceTag11 selected.1) := by
          simpa [decodedFullLocalEar, h4, h5] using hselected
        have hc : code =
            badEndTaggedEarCarrierCode (sourceTag7 selected.1)
              (sourceTag9 selected.1) (sourceTag11 selected.1) := by
          rw [fullLocalEarChartCert_block] at hcode
          simp only [h4, h5, ↓reduceIte] at hcode
          simpa using hcode
        rw [hc, fullLocalEarChartOwner_badEnd]
        exact hs.symm
    · have hs : selected.1 =
          rootTaggedEarFamilyEntry (sourceTag5 selected.1)
            (sourceTag7 selected.1) (sourceTag9 selected.1)
            (sourceTag11 selected.1) := by
        simpa [decodedFullLocalEar, h4] using hselected
      have hc : code =
          rootTaggedEarFamilyCarrierCode (sourceTag5 selected.1)
            (sourceTag7 selected.1) (sourceTag9 selected.1)
            (sourceTag11 selected.1) := by
        rw [fullLocalEarChartCert_block] at hcode
        simp only [h4] at hcode
        simpa using hcode
      rw [hc, fullLocalEarChartOwner_root]
      exact hs.symm

theorem fullLocalEarOwnedFamily_accepts_root (x5 x7 x9 x11 : Bool) :
    fullLocalEarOwnedFamily.test
      (rootTaggedEarFamilyEntry x5 x7 x9 x11) = true :=
  fullLocalEarChartTest_accepts_root x5 x7 x9 x11

theorem fullLocalEarOwnedFamily_accepts_badEnd (x7 x9 x11 : Bool) :
    fullLocalEarOwnedFamily.test (badEndTaggedEarEntry x7 x9 x11) = true :=
  fullLocalEarChartTest_accepts_badEnd x7 x9 x11

theorem fullLocalEarOwnedFamily_accepts_split (x7 x9 x11 : Bool) :
    fullLocalEarOwnedFamily.test (adjacentSplitEntry x7 x9 x11) = true :=
  fullLocalEarChartTest_accepts_split x7 x9 x11

def fullLocalEarGlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  fullLocalEarOwnedFamily.toGlobal

def fullLocalEarAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  fullLocalEarOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned.adjacentSplitPair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned.adjacentSplitCarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned.adjacentSplitPaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned.adjacentSplitCarrierCode_injective
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned.adjacentSplitBlocks_disjoint
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned.fullLocalEarOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned.fullLocalEarOwnedFamily_accepts_split
