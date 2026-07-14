/-
# The first adjacent-tag collision beyond the owned C12 ear chart

The twenty-four-source chart covers a bad-end tag `V4` only when the adjacent
left tag `V5` is absent.  Here both occur.  The source is still admissible
because `V4` and `V5` lie on opposite source sides, but putting both into the
single external target family makes that target weight zero.

More strongly, the complete natural short-chain block obtained by choosing
none, either, or both of the two external bits fails at the exact rational
test point `w=1`, constant fundamental label.  Its weight is `2304`, while the
source weight is `4096`.  Thus this first collision cannot be added by merely
widening the decoder or taking all external submasks; a new chain/resummation
mechanism is required.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence

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
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned

local infix:50 " ≈ " => Q'.eqv

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

/-- The minimal adjacent collision: `V5` on the left and `V4` on the right. -/
def adjacentCollisionPair : MaskPair G.length :=
  (bits12 false true false true false true false false false false false false,
    bits12 true false true false true false false false false false false false)

theorem adjacentCollisionPair_mem :
    adjacentCollisionPair ∈ exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  exact ⟨maskPairs_complete _, rfl⟩

def adjacentCollisionEntry : ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨adjacentCollisionPair, adjacentCollisionPair_mem⟩

/-- Bank that the current twenty-four-source chart really stops here. -/
theorem badEndExpandedChart_rejects_adjacent_collision :
    badEndExpandedChartTest adjacentCollisionEntry = false := by
  decide

def adjacentExternal (x4 x5 : Bool) : OccBitVec G.length :=
  bits12 false false false false x4 x5 false false false false false false

def adjacentCarrierCode (x4 x5 : Bool) : OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices (emptyBits G) shortEarTail }
    external := adjacentExternal x4 x5 }

theorem adjacentCarrierCode_mem (x4 x5 : Bool) :
    adjacentCarrierCode x4 x5 ∈ occurrenceCarrierXiCodes G := by
  unfold adjacentCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨adjacentExternal x4 x5, bitVectors_complete _, ?_⟩
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

theorem adjacentCarrierCode_erasure (x4 x5 : Bool) :
    eraseOccCarrierXiCode G (adjacentCarrierCode x4 x5) =
      ((V0, shortEarErasedChain),
        (if x4 then [V4] else []) ++ (if x5 then [V5] else [])) := by
  cases x4 <;> cases x5 <;> rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c45 : compatibleB V4 V5 = false := by rfl

/-- The naive combined external tag has identically zero target weight. -/
theorem adjacentCarrierCode_both_weight_zero
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (adjacentCarrierCode true true) ≈ 0 := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (adjacentCarrierCode true true) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G (adjacentCarrierCode true true)) from rfl]
  rw [adjacentCarrierCode_erasure]
  simp [shortEarErasedChain, carrierXiCodeWeight, carrierCodeWeight,
    qAll, mark_start, chainCodeWeight, c01, c12, c23, Bool.not_false,
    bad_finish, admissibleFamilyWeight, familyCompatibleB_cons,
    familyCompatibleB_nil, List.all_cons, List.all_nil, c45]
  exact Q'.mul_zero_eqv _

/-- Every external submask of the colliding pair, on the same short chain. -/
def naturalAdjacentCollisionBlock : List (OccCarrierXiCodeAt G) :=
  [adjacentCarrierCode false false,
    adjacentCarrierCode true false,
    adjacentCarrierCode false true,
    adjacentCarrierCode true true]

theorem naturalAdjacentCollisionBlock_nodup :
    naturalAdjacentCollisionBlock.Nodup := by
  decide

theorem naturalAdjacentCollisionBlock_mem
    (code : OccCarrierXiCodeAt G)
    (hcode : code ∈ naturalAdjacentCollisionBlock) :
    code ∈ occurrenceCarrierXiCodes G := by
  simp only [naturalAdjacentCollisionBlock, List.mem_cons,
    List.not_mem_nil, or_false] at hcode
  rcases hcode with rfl | rfl | rfl | rfl
  · exact adjacentCarrierCode_mem false false
  · exact adjacentCarrierCode_mem true false
  · exact adjacentCarrierCode_mem false true
  · exact adjacentCarrierCode_mem true true

def labelOne : TL.Plaquette → Rep := fun _ => 1
def unitWeight : Q' := Q'.ofNat 1

theorem unitWeight_nonneg : (0 : Q') ≤ unitWeight := by decide

set_option maxRecDepth 1000000 in
theorem adjacentCollisionSource_weight_at_unit :
    occurrencePairWeight unitWeight qAll markV0 badV3 G labelOne
      adjacentCollisionPair = Q'.ofNat 4096 := by
  decide

set_option maxRecDepth 1000000 in
theorem naturalAdjacentCollisionBlock_weight_at_unit :
    qListSum
        (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 G labelOne)
        naturalAdjacentCollisionBlock = Q'.ofNat 2304 := by
  decide

/-- Even summing every external submask of the colliding pair does not pay the
source at the exact nonnegative unit coupling. -/
theorem naturalAdjacentCollisionBlock_payment_fails :
    ¬ (occurrencePairWeight unitWeight qAll markV0 badV3 G labelOne
          adjacentCollisionPair ≤
        qListSum
          (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 G
            labelOne)
          naturalAdjacentCollisionBlock) := by
  rw [adjacentCollisionSource_weight_at_unit,
    naturalAdjacentCollisionBlock_weight_at_unit]
  decide

/-- Consequently the complete natural short-chain submask block cannot be a
`PaidResidualBlock` for this actual source. -/
theorem no_natural_adjacent_collision_paid_block :
    ¬ ∃ block : PaidResidualBlock qAll markV0 badV3 G adjacentCollisionEntry,
      block.block = naturalAdjacentCollisionBlock := by
  rintro ⟨block, hblock⟩
  have hpay := block.source_le unitWeight unitWeight_nonneg labelOne
  rw [hblock] at hpay
  exact naturalAdjacentCollisionBlock_payment_fails hpay

end YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence.adjacentCollisionPair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence.badEndExpandedChart_rejects_adjacent_collision
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence.adjacentCarrierCode_both_weight_zero
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence.naturalAdjacentCollisionBlock_payment_fails
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagCollisionFence.no_natural_adjacent_collision_paid_block
