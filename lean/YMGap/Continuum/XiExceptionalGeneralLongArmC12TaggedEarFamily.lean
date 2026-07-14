/-
# A source-tagged C12 ear family

The marked-to-bad short ear admits three mutually compatible off-path polymers
`V5,V7,V9`.  Every subset gives an actual exceptional source.  The same subset,
stored in the genuine external occurrence mask of the short path carrier, gives
an exact singleton payment.  Distinct subsets give distinct target codes, and
none collides with the canonical long-arm block.

This is a uniform eight-source chart derived from the physical carrier syntax.
It does not classify all C12 sources, but it replaces isolated examples by a
nontrivial source-dependent family with exact payment and disjointness.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Native
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def taggedEarFamilyPair (x5 x7 x9 : Bool) : MaskPair G.length :=
  (bits12 false true false true false x5 false x7 false x9 false false,
    bits12 true false true false false false false false false false false false)

theorem taggedEarFamilyPair_mem (x5 x7 x9 : Bool) :
    taggedEarFamilyPair x5 x7 x9 ∈
      exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete _, ?_⟩
  cases x5 <;> cases x7 <;> cases x9 <;> rfl

def taggedEarFamilyEntry (x5 x7 x9 : Bool) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨taggedEarFamilyPair x5 x7 x9, taggedEarFamilyPair_mem x5 x7 x9⟩

def taggedEarFamilyExternal (x5 x7 x9 : Bool) : OccBitVec G.length :=
  bits12 false false false false false x5 false x7 false x9 false false

def taggedEarFamilyList (x5 x7 x9 : Bool) : List (Polymer TL) :=
  (if x5 then [V5] else []) ++
    (if x7 then [V7] else []) ++
      (if x9 then [V9] else [])

theorem taggedEarFamilyExternal_selection (x5 x7 x9 : Bool) :
    selectByBits G (taggedEarFamilyExternal x5 x7 x9) =
      taggedEarFamilyList x5 x7 x9 := by
  cases x5 <;> cases x7 <;> cases x9 <;> rfl

theorem taggedEarFamily_left (x5 x7 x9 : Bool) :
    leftFamily G (taggedEarFamilyPair x5 x7 x9) =
      [V1, V3] ++ taggedEarFamilyList x5 x7 x9 := by
  cases x5 <;> cases x7 <;> cases x9 <;> rfl

theorem taggedEarFamily_right (x5 x7 x9 : Bool) :
    rightFamily G (taggedEarFamilyPair x5 x7 x9) = [V0, V2] := by
  rfl

def taggedEarFamilyCarrierCode (x5 x7 x9 : Bool) : OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits G) shortEarTail }
    external := taggedEarFamilyExternal x5 x7 x9 }

theorem taggedEarFamilyCarrierCode_mem (x5 x7 x9 : Bool) :
    taggedEarFamilyCarrierCode x5 x7 x9 ∈ occurrenceCarrierXiCodes G := by
  unfold taggedEarFamilyCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨taggedEarFamilyExternal x5 x7 x9, bitVectors_complete _, ?_⟩
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

theorem taggedEarFamilyCarrierCode_erasure (x5 x7 x9 : Bool) :
    eraseOccCarrierXiCode G (taggedEarFamilyCarrierCode x5 x7 x9) =
      ((V0, shortEarErasedChain), taggedEarFamilyList x5 x7 x9) := by
  change ((V0, shortEarErasedChain),
      selectByBits G (taggedEarFamilyExternal x5 x7 x9)) = _
  rw [taggedEarFamilyExternal_selection]

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c57 : compatibleB V5 V7 = true := by rfl
private theorem c59 : compatibleB V5 V9 = true := by rfl
private theorem c79 : compatibleB V7 V9 = true := by rfl

theorem taggedEarFamilyCarrierCode_weight_eqv_source
    (x5 x7 x9 : Bool) (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (taggedEarFamilyCarrierCode x5 x7 x9) ≈
      occurrencePairWeight w qAll markV0 badV3 G label
        (taggedEarFamilyPair x5 x7 x9) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (taggedEarFamilyCarrierCode x5 x7 x9) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (taggedEarFamilyCarrierCode x5 x7 x9)) from rfl]
  rw [taggedEarFamilyCarrierCode_erasure]
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label (taggedEarFamilyPair x5 x7 x9)
      (taggedEarFamilyPair_mem x5 x7 x9)]
  rw [taggedEarFamily_left, taggedEarFamily_right]
  cases x5 <;> cases x7 <;> cases x9 <;>
    simp [taggedEarFamilyList, shortEarErasedChain, carrierXiCodeWeight,
      carrierCodeWeight, qAll, mark_start,
      chainCodeWeight, c01, c12, c23, Bool.not_false, bad_finish,
      admissibleFamilyWeight, familyCompatibleB_cons, familyCompatibleB_nil,
      List.all_cons, List.all_nil, c57, c59, c79, familyActivity_cons,
      familyActivity_nil] <;>
    ring_qeqv

def taggedEarFamilyPaidBlock (x5 x7 x9 : Bool) :
    PaidResidualBlock qAll markV0 badV3 G
      (taggedEarFamilyEntry x5 x7 x9) where
  block := [taggedEarFamilyCarrierCode x5 x7 x9]
  block_nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact taggedEarFamilyCarrierCode_mem x5 x7 x9
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (taggedEarFamilyCarrierCode_weight_eqv_source x5 x7 x9 w label)

private theorem external_at5 (x5 x7 x9 : Bool) :
    (taggedEarFamilyExternal x5 x7 x9).at 5 = x5 := by rfl

private theorem external_at7 (x5 x7 x9 : Bool) :
    (taggedEarFamilyExternal x5 x7 x9).at 7 = x7 := by rfl

private theorem external_at9 (x5 x7 x9 : Bool) :
    (taggedEarFamilyExternal x5 x7 x9).at 9 = x9 := by rfl

theorem taggedEarFamilyCarrierCode_injective
    {x5 x7 x9 y5 y7 y9 : Bool}
    (h : taggedEarFamilyCarrierCode x5 x7 x9 =
      taggedEarFamilyCarrierCode y5 y7 y9) :
    x5 = y5 ∧ x7 = y7 ∧ x9 = y9 := by
  have hext := congrArg (fun code => code.external) h
  have h5 := congrArg (fun bits => bits.at 5) hext
  have h7 := congrArg (fun bits => bits.at 7) hext
  have h9 := congrArg (fun bits => bits.at 9) hext
  simpa [external_at5, external_at7, external_at9] using And.intro h5 (And.intro h7 h9)

theorem taggedEarFamilyBlocks_disjoint
    {x5 x7 x9 y5 y7 y9 : Bool}
    (hne : x5 ≠ y5 ∨ x7 ≠ y7 ∨ x9 ≠ y9) (code : OccCarrierXiCodeAt G)
    (hx : code ∈ (taggedEarFamilyPaidBlock x5 x7 x9).block)
    (hy : code ∈ (taggedEarFamilyPaidBlock y5 y7 y9).block) : False := by
  have hcx : code = taggedEarFamilyCarrierCode x5 x7 x9 := by
    simpa [taggedEarFamilyPaidBlock] using hx
  have hcy : code = taggedEarFamilyCarrierCode y5 y7 y9 := by
    simpa [taggedEarFamilyPaidBlock] using hy
  have hs := taggedEarFamilyCarrierCode_injective (hcx.symm.trans hcy)
  rcases hne with h5 | h7 | h9
  · exact h5 hs.1
  · exact h7 hs.2.1
  · exact h9 hs.2.2

set_option maxRecDepth 1000000 in
theorem taggedEarFamilyCarrierCode_not_mem_canonical (x5 x7 x9 : Bool) :
    taggedEarFamilyCarrierCode x5 x7 x9 ∉ canonicalRepairBlock := by
  cases x5 <;> cases x7 <;> cases x9 <;> decide

end YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily.taggedEarFamilyPair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily.taggedEarFamilyCarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily.taggedEarFamilyPaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily.taggedEarFamilyCarrierCode_injective
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily.taggedEarFamilyBlocks_disjoint
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarFamily.taggedEarFamilyCarrierCode_not_mem_canonical
