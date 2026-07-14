/-
# A genuine two-source owned C12 allocator

The canonical alternating C12 source needs the native nine-code long-arm
repair block.  The distinct short-ear source from the ownership fence has a
smaller exact carrier: the ordinary marked-to-bad path `0,1,2,3`.  Its
three-step occurrence chain is a genuine member of the unchanged target
enumeration and has exactly the source weight at every nonnegative scale and
every label.

The short path code is not one of the nine canonical payers.  This supplies
a recoverable owner and hence a genuinely two-source
`OwnedPaidResidualFamily`, without adding any artificial code constructor.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned

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

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def shortEarTail : List Nat := [1, 2, 3]

/-- The source-specific rewiring for the short-ear entry is the actual
simple occurrence carrier following its complete disagreement path. -/
def shortEarCarrierCode : OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits G) shortEarTail }
    external := emptyBits G }

theorem shortEarCarrierCode_mem :
    shortEarCarrierCode ∈ occurrenceCarrierXiCodes G := by
  unfold shortEarCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨emptyBits G, bitVectors_complete _, ?_⟩
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

def shortEarErasedChain : ChainCode TL.Plaquette :=
  .step V1 (.step V2 (.step V3 (.terminal [])))

theorem shortEarCarrierCode_erasure :
    eraseOccCarrierXiCode G shortEarCarrierCode =
      ((V0, shortEarErasedChain), []) := by
  rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl

def shortEarMonomial (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  ((activity w V0 label * activity w V1 label) *
    activity w V2 label) * activity w V3 label

theorem shortEarCarrierCode_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        shortEarCarrierCode ≈ shortEarMonomial w label := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      shortEarCarrierCode =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G shortEarCarrierCode) from rfl]
  rw [shortEarCarrierCode_erasure]
  simp only [shortEarErasedChain, carrierXiCodeWeight, carrierCodeWeight,
    qAll, mark_start, Bool.true_and, if_true, chainCodeWeight, c01, c12,
    c23, Bool.not_false, bad_finish, admissibleFamilyWeight, List.all_nil,
    familyCompatibleB_nil, familyActivity_nil]
  unfold shortEarMonomial
  ring_qeqv

private theorem shortEar_left_family :
    leftFamily G shortEarPair = [V1, V3] := by
  rfl

private theorem shortEar_right_family :
    rightFamily G shortEarPair = [V0, V2] := by
  rfl

theorem shortEar_source_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 G label shortEarPair ≈
      shortEarMonomial w label := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label shortEarPair shortEarPair_mem]
  rw [shortEar_left_family, shortEar_right_family]
  simp only [familyActivity_cons, familyActivity_nil]
  unfold shortEarMonomial
  ring_qeqv

/-- The rewired simple carrier has exactly the short-ear source weight, for
all scales and labels. -/
theorem shortEarCarrierCode_weight_eqv_source
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        shortEarCarrierCode ≈
      occurrencePairWeight w qAll markV0 badV3 G label shortEarPair :=
  Q'.eqv_trans _ _ _ (shortEarCarrierCode_weight_eqv w label)
    (Q'.eqv_symm (shortEar_source_weight_eqv w label))

def shortEarPaidResidualBlock :
    PaidResidualBlock qAll markV0 badV3 G shortEarEntry where
  block := [shortEarCarrierCode]
  block_nodup := by decide
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact shortEarCarrierCode_mem
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv (shortEarCarrierCode_weight_eqv_source w label)

set_option maxRecDepth 1000000 in
theorem shortEarCarrierCode_not_mem_canonical :
    shortEarCarrierCode ∉ canonicalRepairBlock := by
  decide

def twoSourceOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  if decide (code = shortEarCarrierCode) then shortEarEntry else entry

theorem twoSourceOwner_shortEar :
    twoSourceOwner shortEarCarrierCode = shortEarEntry := by
  rfl

theorem twoSourceOwner_canonical
    (code : OccCarrierXiCodeAt G) (hcode : code ∈ canonicalRepairBlock) :
    twoSourceOwner code = entry := by
  unfold twoSourceOwner
  split
  next heq =>
    have hcodeEq : code = shortEarCarrierCode := of_decide_eq_true heq
    exact False.elim
      (shortEarCarrierCode_not_mem_canonical (hcodeEq ▸ hcode))
  next _ => rfl

def twoSourceCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      twoSourceTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 := by
  if hcanonical : selected.1 = entry then
    exact hcanonical.symm ▸ c12PaidResidualBlock
  else
    have hshort : selected.1 = shortEarEntry := by
      rcases twoSourceTest_cases selected.1 selected.2 with h | h
      · exact False.elim (hcanonical h)
      · exact h
    exact hshort.symm ▸ shortEarPaidResidualBlock

def twoSourceOwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := twoSourceTest
  cert := twoSourceCert
  owner := twoSourceOwner
  block_owner := by
    rintro ⟨other, htest⟩ code hcode
    by_cases hcanonical : other = entry
    · subst other
      apply twoSourceOwner_canonical code
      simpa [twoSourceCert] using hcode
    · have hshort : other = shortEarEntry := by
        rcases twoSourceTest_cases other htest with h | h
        · exact False.elim (hcanonical h)
        · exact h
      subst other
      have hsingleton : code = shortEarCarrierCode := by
        have hshortNe : shortEarEntry ≠ entry :=
          fun h => canonical_ne_shortEar h.symm
        simpa [twoSourceCert, hshortNe, shortEarPaidResidualBlock] using hcode
      subst code
      exact twoSourceOwner_shortEar

def twoSourceGlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  twoSourceOwnedFamily.toGlobal

def twoSourceAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  twoSourceOwnedFamily.allocator

theorem twoSourceOwnedFamily_accepts_canonical :
    twoSourceOwnedFamily.test entry = true := twoSourceTest_canonical

theorem twoSourceOwnedFamily_accepts_shortEar :
    twoSourceOwnedFamily.test shortEarEntry = true := twoSourceTest_shortEar

theorem twoSource_canonical_block_eq :
    (twoSourceOwnedFamily.cert
      ⟨entry, twoSourceOwnedFamily_accepts_canonical⟩).block =
        canonicalRepairBlock := by
  rfl

theorem twoSource_shortEar_block_eq :
    (twoSourceOwnedFamily.cert
      ⟨shortEarEntry, twoSourceOwnedFamily_accepts_shortEar⟩).block =
        [shortEarCarrierCode] := by
  rfl

theorem twoSource_canonical_source_le
    (w : Q') (hw : (0 : Q') ≤ w) (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 G label entry.1 ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label)
        canonicalRepairBlock := by
  rw [← twoSource_canonical_block_eq]
  exact (twoSourceOwnedFamily.cert
    ⟨entry, twoSourceOwnedFamily_accepts_canonical⟩).source_le w hw label

theorem twoSource_shortEar_source_le
    (w : Q') (hw : (0 : Q') ≤ w) (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 G label shortEarEntry.1 ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label)
        [shortEarCarrierCode] := by
  rw [← twoSource_shortEar_block_eq]
  exact (twoSourceOwnedFamily.cert
    ⟨shortEarEntry, twoSourceOwnedFamily_accepts_shortEar⟩).source_le
      w hw label

theorem twoSource_blocks_disjoint :
    ∀ code,
      code ∈ (twoSourceOwnedFamily.cert
        ⟨entry, twoSourceOwnedFamily_accepts_canonical⟩).block →
      code ∉ (twoSourceOwnedFamily.cert
        ⟨shortEarEntry, twoSourceOwnedFamily_accepts_shortEar⟩).block := by
  intro code hcanonical hshort
  exact owned_two_source_blocks_have_no_common_code twoSourceOwnedFamily
    twoSourceOwnedFamily_accepts_canonical
    twoSourceOwnedFamily_accepts_shortEar code hcanonical hshort

#print axioms shortEarCarrierCode_mem
#print axioms shortEarCarrierCode_weight_eqv
#print axioms shortEar_source_weight_eqv
#print axioms shortEarCarrierCode_weight_eqv_source
#print axioms shortEarPaidResidualBlock
#print axioms shortEarCarrierCode_not_mem_canonical
#print axioms twoSourceOwner_canonical
#print axioms twoSourceOwnedFamily
#print axioms twoSource_canonical_source_le
#print axioms twoSource_shortEar_source_le
#print axioms twoSource_blocks_disjoint

end YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned
