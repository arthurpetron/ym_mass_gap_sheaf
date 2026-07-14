/-
# A third genuine owned C12 source

The short-ear source can be enlarged by the compatible off-path polymer `V5`.
Its source monomial is represented exactly by the same marked-to-bad occurrence
path together with the genuine external occurrence mask selecting `V5`.  That
external mask is a recoverable source tag: the resulting singleton is disjoint
from both the canonical nine-code block and the untagged short-ear singleton.

This gives a third actual source-specific paid block and extends the owned C12
family constructively.  It is finite evidence for the source-tagging mechanism,
not the still-open uniform arbitrary-source synthesis.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned

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
open YMGap.Continuum.XiExceptionalOwnedFamilyExtension
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnedExtension

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

/-- The short ear with one compatible off-path left-family occurrence. -/
def taggedEarPair : MaskPair G.length :=
  (bits12 false true false true false true false false false false false false,
    bits12 true false true false false false false false false false false false)

theorem taggedEarPair_mem :
    taggedEarPair ∈ exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  exact ⟨maskPairs_complete taggedEarPair, rfl⟩

def taggedEarEntry : ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨taggedEarPair, taggedEarPair_mem⟩

theorem taggedEar_ne_canonical : taggedEarEntry ≠ entry := by
  decide

theorem taggedEar_ne_shortEar : taggedEarEntry ≠ shortEarEntry := by
  decide

/-- The external occurrence bit is the source tag; no artificial target
constructor is introduced. -/
def taggedEarExternal : OccBitVec G.length :=
  bits12 false false false false false true false false false false false false

def taggedEarCarrierCode : OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits G) shortEarTail }
    external := taggedEarExternal }

theorem taggedEarCarrierCode_mem :
    taggedEarCarrierCode ∈ occurrenceCarrierXiCodes G := by
  unfold taggedEarCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨taggedEarExternal, bitVectors_complete _, ?_⟩
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

theorem taggedEarCarrierCode_erasure :
    eraseOccCarrierXiCode G taggedEarCarrierCode =
      ((V0, shortEarErasedChain), [V5]) := by
  rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl

def taggedEarMonomial (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  ((((activity w V0 label * activity w V1 label) *
    activity w V2 label) * activity w V3 label) * activity w V5 label)

theorem taggedEarCarrierCode_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        taggedEarCarrierCode ≈ taggedEarMonomial w label := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      taggedEarCarrierCode =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G taggedEarCarrierCode) from rfl]
  rw [taggedEarCarrierCode_erasure]
  simp only [shortEarErasedChain, carrierXiCodeWeight, carrierCodeWeight,
    qAll, mark_start, Bool.true_and, if_true, chainCodeWeight, c01, c12,
    c23, Bool.not_false, bad_finish, admissibleFamilyWeight,
    familyCompatibleB_cons, familyCompatibleB_nil, List.all_cons,
    List.all_nil, familyActivity_cons, familyActivity_nil]
  unfold taggedEarMonomial
  ring_qeqv

private theorem taggedEar_left_family :
    leftFamily G taggedEarPair = [V1, V3, V5] := by
  rfl

private theorem taggedEar_right_family :
    rightFamily G taggedEarPair = [V0, V2] := by
  rfl

theorem taggedEar_source_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 G label taggedEarPair ≈
      taggedEarMonomial w label := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label taggedEarPair taggedEarPair_mem]
  rw [taggedEar_left_family, taggedEar_right_family]
  simp only [familyActivity_cons, familyActivity_nil]
  unfold taggedEarMonomial
  ring_qeqv

theorem taggedEarCarrierCode_weight_eqv_source
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        taggedEarCarrierCode ≈
      occurrencePairWeight w qAll markV0 badV3 G label taggedEarPair :=
  Q'.eqv_trans _ _ _ (taggedEarCarrierCode_weight_eqv w label)
    (Q'.eqv_symm (taggedEar_source_weight_eqv w label))

def taggedEarPaidResidualBlock :
    PaidResidualBlock qAll markV0 badV3 G taggedEarEntry where
  block := [taggedEarCarrierCode]
  block_nodup := by decide
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact taggedEarCarrierCode_mem
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv (taggedEarCarrierCode_weight_eqv_source w label)

set_option maxRecDepth 1000000 in
theorem taggedEarCarrierCode_not_mem_canonical :
    taggedEarCarrierCode ∉ canonicalRepairBlock := by
  decide

theorem taggedEarCarrierCode_ne_shortEar :
    taggedEarCarrierCode ≠ shortEarCarrierCode := by
  decide

private theorem old_selected_cases
    (old : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      extendedC12TwoSource.test other = true }) :
    old.1 = entry ∨ old.1 = shortEarEntry := by
  have htest := old.2
  change extendedTest c12OwnedFamily shortEarEntry old.1 = true at htest
  unfold extendedTest at htest
  by_cases hshort : old.1 = shortEarEntry
  · exact Or.inr hshort
  · have hold : c12OwnedFamily.test old.1 = true := by
      simpa [hshort] using htest
    exact Or.inl ((c12Test_true_iff old.1).mp hold)

private theorem old_blocks_disjoint_tagged
    (old : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      extendedC12TwoSource.test other = true })
    (code : OccCarrierXiCodeAt G)
    (hcode : code ∈ (extendedC12TwoSource.cert old).block) :
    code ∉ taggedEarPaidResidualBlock.block := by
  intro htagged
  have hcodeEq : code = taggedEarCarrierCode := by
    simpa [taggedEarPaidResidualBlock] using htagged
  subst code
  rcases old_selected_cases old with hcanonical | hshort
  · have hmem : taggedEarCarrierCode ∈ canonicalRepairBlock := by
      have hblock : (extendedC12TwoSource.cert old).block =
          canonicalRepairBlock := by
        cases old with
        | mk value property =>
            dsimp only at hcanonical
            subst value
            rfl
      exact hblock ▸ hcode
    exact taggedEarCarrierCode_not_mem_canonical hmem
  · have hmem : taggedEarCarrierCode ∈ [shortEarCarrierCode] := by
      have hblock : (extendedC12TwoSource.cert old).block =
          [shortEarCarrierCode] := by
        cases old with
        | mk value property =>
            dsimp only at hshort
            subst value
            rfl
      exact hblock ▸ hcode
    have heq : taggedEarCarrierCode = shortEarCarrierCode := by
      simpa using hmem
    exact taggedEarCarrierCode_ne_shortEar heq

/-- Three actual C12 sources with pairwise source-owned target blocks. -/
def extendedC12ThreeSource : OwnedPaidResidualFamily qAll markV0 badV3 G :=
  extendOwnedFamily extendedC12TwoSource taggedEarEntry
    taggedEarPaidResidualBlock old_blocks_disjoint_tagged

theorem extendedC12Three_accepts_canonical :
    extendedC12ThreeSource.test entry = true :=
  extendOwnedFamily_preserves_old extendedC12TwoSource taggedEarEntry
    taggedEarPaidResidualBlock old_blocks_disjoint_tagged entry
      extendedC12_accepts_canonical

theorem extendedC12Three_accepts_shortEar :
    extendedC12ThreeSource.test shortEarEntry = true :=
  extendOwnedFamily_preserves_old extendedC12TwoSource taggedEarEntry
    taggedEarPaidResidualBlock old_blocks_disjoint_tagged shortEarEntry
      extendedC12_accepts_shortEar

theorem extendedC12Three_accepts_taggedEar :
    extendedC12ThreeSource.test taggedEarEntry = true :=
  extendOwnedFamily_accepts_fresh extendedC12TwoSource taggedEarEntry
    taggedEarPaidResidualBlock old_blocks_disjoint_tagged

end YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned.taggedEarPair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned.taggedEarCarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned.taggedEarPaidResidualBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned.extendedC12ThreeSource
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned.extendedC12Three_accepts_canonical
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned.extendedC12Three_accepts_shortEar
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12ThreeSourceOwned.extendedC12Three_accepts_taggedEar
