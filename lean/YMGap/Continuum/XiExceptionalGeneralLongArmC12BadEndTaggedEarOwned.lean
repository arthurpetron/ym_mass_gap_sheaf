/-
# A bad-end attached class for the owned C12 ear chart

After the root tag `V11`, the next missing short-ear geometry attaches `V4`
across the bad endpoint `V3`.  When `V5` is absent, `V4` is compatible with
the remaining external tags `V7,V9,V11`; the genuine external occurrence mask
therefore gives another exact singleton payment.

The predecessor's four-bit decoder is first proved to reject all eight such
sources.  A fifth source/target tag then constructs one owned family covering
the predecessor's sixteen sources and the eight new bad-end sources.  The
still-missing simultaneous `V4,V5` collision is deliberately not accepted.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned

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

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

/-- `V4` is placed on the right of the short ear; the optional external
left-family tags begin at `V7`, so the external target family is compatible. -/
def badEndTaggedEarPair (x7 x9 x11 : Bool) : MaskPair G.length :=
  (bits12 false true false true false false false x7 false x9 false x11,
    bits12 true false true false true false false false false false false false)

theorem badEndTaggedEarPair_mem (x7 x9 x11 : Bool) :
    badEndTaggedEarPair x7 x9 x11 ∈
      exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete _, ?_⟩
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

def badEndTaggedEarEntry (x7 x9 x11 : Bool) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨badEndTaggedEarPair x7 x9 x11,
    badEndTaggedEarPair_mem x7 x9 x11⟩

def badEndTaggedEarExternal (x7 x9 x11 : Bool) : OccBitVec G.length :=
  bits12 false false false false true false false x7 false x9 false x11

def badEndTaggedEarList (x7 x9 x11 : Bool) : List (Polymer TL) :=
  [V4] ++
    (if x7 then [V7] else []) ++
      (if x9 then [V9] else []) ++
        (if x11 then [V11] else [])

theorem badEndTaggedEarExternal_selection (x7 x9 x11 : Bool) :
    selectByBits G (badEndTaggedEarExternal x7 x9 x11) =
      badEndTaggedEarList x7 x9 x11 := by
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem badEndTaggedEar_left (x7 x9 x11 : Bool) :
    leftFamily G (badEndTaggedEarPair x7 x9 x11) =
      [V1, V3] ++
        ((if x7 then [V7] else []) ++
          (if x9 then [V9] else []) ++
            (if x11 then [V11] else [])) := by
  cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem badEndTaggedEar_right (x7 x9 x11 : Bool) :
    rightFamily G (badEndTaggedEarPair x7 x9 x11) = [V0, V2, V4] := by
  rfl

def badEndTaggedEarCarrierCode (x7 x9 x11 : Bool) : OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits G) shortEarTail }
    external := badEndTaggedEarExternal x7 x9 x11 }

theorem badEndTaggedEarCarrierCode_mem (x7 x9 x11 : Bool) :
    badEndTaggedEarCarrierCode x7 x9 x11 ∈ occurrenceCarrierXiCodes G := by
  unfold badEndTaggedEarCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨badEndTaggedEarExternal x7 x9 x11, bitVectors_complete _, ?_⟩
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

theorem badEndTaggedEarCarrierCode_erasure (x7 x9 x11 : Bool) :
    eraseOccCarrierXiCode G (badEndTaggedEarCarrierCode x7 x9 x11) =
      ((V0, shortEarErasedChain), badEndTaggedEarList x7 x9 x11) := by
  change ((V0, shortEarErasedChain),
      selectByBits G (badEndTaggedEarExternal x7 x9 x11)) = _
  rw [badEndTaggedEarExternal_selection]

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c47 : compatibleB V4 V7 = true := by rfl
private theorem c49 : compatibleB V4 V9 = true := by rfl
private theorem c411 : compatibleB V4 V11 = true := by rfl
private theorem c79 : compatibleB V7 V9 = true := by rfl
private theorem c711 : compatibleB V7 V11 = true := by rfl
private theorem c911 : compatibleB V9 V11 = true := by rfl

theorem badEndTaggedEarCarrierCode_weight_eqv_source
    (x7 x9 x11 : Bool) (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (badEndTaggedEarCarrierCode x7 x9 x11) ≈
      occurrencePairWeight w qAll markV0 badV3 G label
        (badEndTaggedEarPair x7 x9 x11) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (badEndTaggedEarCarrierCode x7 x9 x11) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (badEndTaggedEarCarrierCode x7 x9 x11)) from rfl]
  rw [badEndTaggedEarCarrierCode_erasure]
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label (badEndTaggedEarPair x7 x9 x11)
      (badEndTaggedEarPair_mem x7 x9 x11)]
  rw [badEndTaggedEar_left, badEndTaggedEar_right]
  cases x7 <;> cases x9 <;> cases x11 <;>
    simp [badEndTaggedEarList, shortEarErasedChain, carrierXiCodeWeight,
      carrierCodeWeight, qAll, mark_start, chainCodeWeight, c01, c12, c23,
      Bool.not_false, bad_finish, admissibleFamilyWeight,
      familyCompatibleB_cons, familyCompatibleB_nil, List.all_cons,
      List.all_nil, c47, c49, c411, c79, c711, c911,
      familyActivity_cons, familyActivity_nil] <;>
    ring_qeqv

def badEndTaggedEarPaidBlock (x7 x9 x11 : Bool) :
    PaidResidualBlock qAll markV0 badV3 G
      (badEndTaggedEarEntry x7 x9 x11) where
  block := [badEndTaggedEarCarrierCode x7 x9 x11]
  block_nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact badEndTaggedEarCarrierCode_mem x7 x9 x11
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (badEndTaggedEarCarrierCode_weight_eqv_source x7 x9 x11 w label)

private theorem external_at7 (x7 x9 x11 : Bool) :
    (badEndTaggedEarExternal x7 x9 x11).at 7 = x7 := by rfl

private theorem external_at9 (x7 x9 x11 : Bool) :
    (badEndTaggedEarExternal x7 x9 x11).at 9 = x9 := by rfl

private theorem external_at11 (x7 x9 x11 : Bool) :
    (badEndTaggedEarExternal x7 x9 x11).at 11 = x11 := by rfl

theorem badEndTaggedEarCarrierCode_injective
    {x7 x9 x11 y7 y9 y11 : Bool}
    (h : badEndTaggedEarCarrierCode x7 x9 x11 =
      badEndTaggedEarCarrierCode y7 y9 y11) :
    x7 = y7 ∧ x9 = y9 ∧ x11 = y11 := by
  have hext := congrArg (fun code => code.external) h
  have h7 := congrArg (fun bits => bits.at 7) hext
  have h9 := congrArg (fun bits => bits.at 9) hext
  have h11 := congrArg (fun bits => bits.at 11) hext
  simpa [external_at7, external_at9, external_at11] using
    And.intro h7 (And.intro h9 h11)

theorem badEndTaggedEarBlocks_disjoint
    {x7 x9 x11 y7 y9 y11 : Bool}
    (hne : x7 ≠ y7 ∨ x9 ≠ y9 ∨ x11 ≠ y11)
    (code : OccCarrierXiCodeAt G)
    (hx : code ∈ (badEndTaggedEarPaidBlock x7 x9 x11).block)
    (hy : code ∈ (badEndTaggedEarPaidBlock y7 y9 y11).block) : False := by
  have hcx : code = badEndTaggedEarCarrierCode x7 x9 x11 := by
    simpa [badEndTaggedEarPaidBlock] using hx
  have hcy : code = badEndTaggedEarCarrierCode y7 y9 y11 := by
    simpa [badEndTaggedEarPaidBlock] using hy
  have hs := badEndTaggedEarCarrierCode_injective (hcx.symm.trans hcy)
  rcases hne with h7 | h9 | h11
  · exact h7 hs.1
  · exact h9 hs.2.1
  · exact h11 hs.2.2

theorem badEndTaggedEarCarrierCode_ne_root
    (x7 x9 x11 y5 y7 y9 y11 : Bool) :
    badEndTaggedEarCarrierCode x7 x9 x11 ≠
      rootTaggedEarFamilyCarrierCode y5 y7 y9 y11 := by
  intro h
  have h4 := congrArg (fun code => code.external.at 4) h
  cases h4

set_option maxRecDepth 1000000 in
theorem badEndTaggedEarCarrierCode_not_mem_canonical (x7 x9 x11 : Bool) :
    badEndTaggedEarCarrierCode x7 x9 x11 ∉ canonicalRepairBlock := by
  cases x7 <;> cases x9 <;> cases x11 <;> decide

/-- Bank the predecessor rejection before extending the source decoder. -/
theorem rootTaggedEarChart_rejects_bad_end (x7 x9 x11 : Bool) :
    rootTaggedEarChartTest (badEndTaggedEarEntry x7 x9 x11) = false := by
  cases x7 <;> cases x9 <;> cases x11 <;> decide

/-! ## A combined owner for sixteen old and eight new sources -/

def sourceTag4
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.2.at 4

def decodedBadEndTaggedEar
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  if sourceTag4 other then
    badEndTaggedEarEntry (sourceTag7 other) (sourceTag9 other)
      (sourceTag11 other)
  else
    rootTaggedEarFamilyEntry (sourceTag5 other) (sourceTag7 other)
      (sourceTag9 other) (sourceTag11 other)

def badEndExpandedChartTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = decodedBadEndTaggedEar other)

theorem badEndExpandedChartTest_accepts_old (x5 x7 x9 x11 : Bool) :
    badEndExpandedChartTest
      (rootTaggedEarFamilyEntry x5 x7 x9 x11) = true := by
  cases x5 <;> cases x7 <;> cases x9 <;> cases x11 <;> rfl

theorem badEndExpandedChartTest_accepts_new (x7 x9 x11 : Bool) :
    badEndExpandedChartTest (badEndTaggedEarEntry x7 x9 x11) = true := by
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

def badEndExpandedChartCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      badEndExpandedChartTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 := by
  have hselected : selected.1 = decodedBadEndTaggedEar selected.1 :=
    of_decide_eq_true selected.2
  if h4 : sourceTag4 selected.1 = true then
    have hselected' : selected.1 =
        badEndTaggedEarEntry (sourceTag7 selected.1)
          (sourceTag9 selected.1) (sourceTag11 selected.1) := by
      simpa [decodedBadEndTaggedEar, h4] using hselected
    exact transportPaidResidualBlock hselected'
      (badEndTaggedEarPaidBlock (sourceTag7 selected.1)
        (sourceTag9 selected.1) (sourceTag11 selected.1))
  else
    have h4f : sourceTag4 selected.1 = false := by
      cases h : sourceTag4 selected.1 with
      | false => rfl
      | true => exact False.elim (h4 h)
    have hselected' : selected.1 =
        rootTaggedEarFamilyEntry (sourceTag5 selected.1)
          (sourceTag7 selected.1) (sourceTag9 selected.1)
          (sourceTag11 selected.1) := by
      simpa [decodedBadEndTaggedEar, h4f] using hselected
    exact transportPaidResidualBlock hselected'
      (rootTaggedEarFamilyPaidBlock (sourceTag5 selected.1)
        (sourceTag7 selected.1) (sourceTag9 selected.1)
        (sourceTag11 selected.1))

theorem badEndExpandedChartCert_block
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      badEndExpandedChartTest other = true }) :
    (badEndExpandedChartCert selected).block =
      [if sourceTag4 selected.1 then
        badEndTaggedEarCarrierCode (sourceTag7 selected.1)
          (sourceTag9 selected.1) (sourceTag11 selected.1)
      else
        rootTaggedEarFamilyCarrierCode (sourceTag5 selected.1)
          (sourceTag7 selected.1) (sourceTag9 selected.1)
          (sourceTag11 selected.1)] := by
  by_cases h4 : sourceTag4 selected.1 = true
  · simp [badEndExpandedChartCert, h4, transportPaidResidualBlock_block]
    rfl
  · have h4f : sourceTag4 selected.1 = false := by
      cases h : sourceTag4 selected.1 with
      | false => rfl
      | true => exact False.elim (h4 h)
    simp [badEndExpandedChartCert, h4, transportPaidResidualBlock_block]
    rfl

def badEndExpandedChartOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  if code.external.at 4 then
    badEndTaggedEarEntry (code.external.at 7) (code.external.at 9)
      (code.external.at 11)
  else
    rootTaggedEarFamilyEntry (code.external.at 5) (code.external.at 7)
      (code.external.at 9) (code.external.at 11)

theorem badEndExpandedChartOwner_root (x5 x7 x9 x11 : Bool) :
    badEndExpandedChartOwner
        (rootTaggedEarFamilyCarrierCode x5 x7 x9 x11) =
      rootTaggedEarFamilyEntry x5 x7 x9 x11 := by
  rfl

theorem badEndExpandedChartOwner_badEnd (x7 x9 x11 : Bool) :
    badEndExpandedChartOwner (badEndTaggedEarCarrierCode x7 x9 x11) =
      badEndTaggedEarEntry x7 x9 x11 := by
  rfl

/-- The exact owned/global allocator interface is preserved while the chart
grows from sixteen to twenty-four source patterns. -/
def badEndExpandedOwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := badEndExpandedChartTest
  cert := badEndExpandedChartCert
  owner := badEndExpandedChartOwner
  block_owner := by
    intro selected code hcode
    have hselected : selected.1 = decodedBadEndTaggedEar selected.1 :=
      of_decide_eq_true selected.2
    cases h4 : sourceTag4 selected.1 with
    | false =>
        have hselected' : selected.1 =
            rootTaggedEarFamilyEntry (sourceTag5 selected.1)
              (sourceTag7 selected.1) (sourceTag9 selected.1)
              (sourceTag11 selected.1) := by
          simpa [decodedBadEndTaggedEar, h4] using hselected
        have hcodeEq : code =
            rootTaggedEarFamilyCarrierCode (sourceTag5 selected.1)
              (sourceTag7 selected.1) (sourceTag9 selected.1)
              (sourceTag11 selected.1) := by
          rw [badEndExpandedChartCert_block] at hcode
          simp only [h4, Bool.false_eq_true, ↓reduceIte] at hcode
          simpa using hcode
        rw [hcodeEq, badEndExpandedChartOwner_root]
        exact hselected'.symm
    | true =>
        have hselected' : selected.1 =
            badEndTaggedEarEntry (sourceTag7 selected.1)
              (sourceTag9 selected.1) (sourceTag11 selected.1) := by
          simpa [decodedBadEndTaggedEar, h4] using hselected
        have hcodeEq : code =
            badEndTaggedEarCarrierCode (sourceTag7 selected.1)
              (sourceTag9 selected.1) (sourceTag11 selected.1) := by
          rw [badEndExpandedChartCert_block] at hcode
          simp only [h4, ↓reduceIte] at hcode
          simpa using hcode
        rw [hcodeEq, badEndExpandedChartOwner_badEnd]
        exact hselected'.symm

theorem badEndExpandedOwnedFamily_accepts_old (x5 x7 x9 x11 : Bool) :
    badEndExpandedOwnedFamily.test
      (rootTaggedEarFamilyEntry x5 x7 x9 x11) = true :=
  badEndExpandedChartTest_accepts_old x5 x7 x9 x11

theorem badEndExpandedOwnedFamily_accepts_new (x7 x9 x11 : Bool) :
    badEndExpandedOwnedFamily.test
      (badEndTaggedEarEntry x7 x9 x11) = true :=
  badEndExpandedChartTest_accepts_new x7 x9 x11

def badEndExpandedGlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  badEndExpandedOwnedFamily.toGlobal

def badEndExpandedAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  badEndExpandedOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.badEndTaggedEarPair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.badEndTaggedEarCarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.badEndTaggedEarPaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.badEndTaggedEarBlocks_disjoint
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.badEndTaggedEarCarrierCode_ne_root
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.rootTaggedEarChart_rejects_bad_end
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.badEndExpandedOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned.badEndExpandedOwnedFamily_accepts_new
