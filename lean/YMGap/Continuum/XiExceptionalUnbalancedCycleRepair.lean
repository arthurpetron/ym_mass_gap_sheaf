/-
# Exact unchanged-target repair for the unbalanced eight-cycle

The complete unchanged occurrence target has ample exact capacity at the
closed unit-weight witness.  More importantly, the overflowing long square
can be shortened without changing its monomial: repeat the even long-arm
vertices by self-incompatibility steps in the carrier and place the odd
long-arm reserve in the external compatible mask.  Together with the short
square this gives a duplicate-free two-code block of weights `A^2` and
`B^2`, so the same constructive `A*B <= A^2+B^2` argument pays the source
for every nonnegative exact weight and every representation label.
-/

import YMGap.Continuum.XiExceptionalUnbalancedCycleFence
import YMGap.Continuum.XiExceptionalMixedEarAbsorption

namespace YMGap.Continuum.XiExceptionalUnbalancedCycleRepair

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalUnbalancedCycleFence

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

set_option maxRecDepth 1000000 in
theorem unit_XiR_exact :
    XiR unitWeight qAll Gamma labelOne = Q'.ofNat 1889 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem unit_connectingChainMajorant_exact :
    connectingChainMajorant unitWeight qAll markV0 badV3 Gamma labelOne =
      Q'.ofNat 1055627520 := by
  decide

theorem unit_full_target_capacity :
    qListSum
        (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 Gamma
          labelOne)
        (occurrenceCarrierXiCodes Gamma) ≈ Q'.ofNat 1994080385280 := by
  refine Q'.eqv_trans _ _ _
    (occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
      unitWeight qAll markV0 badV3 Gamma labelOne) ?_
  rw [unit_connectingChainMajorant_exact, unit_XiR_exact]
  decide

/-! ## A fuel-eight long square with an external reserve -/

def allEdge : Nat → Nat → Bool := fun _ _ => true

/-- `0,7,6,6,5,4,4,3`: the base long arm, with the even reserve repeated
by self-incompatibility steps. -/
def longReserveWalk : CWalk allEdge 0 3 :=
  .cons (x := 0) (y := 7) rfl
    (.cons (x := 7) (y := 6) rfl
      (.cons (x := 6) (y := 6) rfl
        (.cons (x := 6) (y := 5) rfl
          (.cons (x := 5) (y := 4) rfl
            (.cons (x := 4) (y := 4) rfl
              (.cons (x := 4) (y := 3) rfl (.single 3)))))))

/-- The complementary odd reserve `{V5,V7}` is internally compatible and
supplies the second copies not repeated in the carrier. -/
def longReserveBits : OccBitVec Gamma.length :=
  bits8 false false false false false true false true

def longReserveCode : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := occurrenceChainCodeOfWalk longReserveWalk emptyBits }
    external := longReserveBits }

theorem longReserveWalk_length : longReserveWalk.vertices.length = 8 := by
  rfl

theorem longReserveCode_mem :
    longReserveCode ∈ occurrenceCarrierXiCodes Gamma := by
  unfold longReserveCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨longReserveBits, bitVectors_complete longReserveBits, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, occurrenceChainCodeOfWalk longReserveWalk emptyBits⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk longReserveWalk emptyBits, ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem Gamma emptyBits longReserveWalk
    Gamma.length
  · rw [longReserveWalk_length]
    simp [Gamma]
  · intro k hk
    simp [longReserveWalk, CWalk.vertices, Gamma] at hk ⊢
    omega

theorem longReserveCode_erasure :
    eraseOccCarrierXiCode Gamma longReserveCode =
      ((V0, .step V7 (.step V6 (.step V6 (.step V5
        (.step V4 (.step V4 (.step V3 (.terminal [])))))))),
        [V5, V7]) := by
  rfl

def commonWeight (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  activity w V0 label * activity w V3 label

def shortArm (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  activity w V1 label * activity w V2 label

def longArm (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  (activity w V7 label * activity w V6 label) *
    (activity w V5 label * activity w V4 label)

private theorem left_family : leftFamily Gamma pair = [V1, V3, V5, V7] := by
  rfl

private theorem right_family : rightFamily Gamma pair = [V0, V2, V4, V6] := by
  rfl

theorem source_weight_eqv (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label pair ≈
      commonWeight w label * (shortArm w label * longArm w label) := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 Gamma label pair pair_mem]
  rw [left_family, right_family]
  simp only [familyActivity_cons, familyActivity_nil]
  unfold commonWeight shortArm longArm
  ring_qeqv

theorem shortBounceCode_erasure :
    eraseOccCarrierXiCode Gamma shortBounceCode =
      ((V0, .step V1 (.step V2 (.step V1 (.step V2
        (.step V3 (.terminal [])))))), []) := by
  rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c21 : compatibleB V2 V1 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c07 : compatibleB V0 V7 = false := by rfl
private theorem c76 : compatibleB V7 V6 = false := by rfl
private theorem c66 : compatibleB V6 V6 = false := by rfl
private theorem c65 : compatibleB V6 V5 = false := by rfl
private theorem c54 : compatibleB V5 V4 = false := by rfl
private theorem c44 : compatibleB V4 V4 = false := by rfl
private theorem c43 : compatibleB V4 V3 = false := by rfl
private theorem longReserve_external_compatible :
    familyCompatibleB [V5, V7] = true := by rfl

theorem shortBounceCode_square_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        shortBounceCode ≈
      commonWeight w label * (shortArm w label * shortArm w label) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
      shortBounceCode =
        carrierXiCodeWeight w qAll markV0 badV3 Gamma label
          (eraseOccCarrierXiCode Gamma shortBounceCode) from rfl]
  rw [shortBounceCode_erasure]
  simp only [carrierXiCodeWeight, carrierCodeWeight, qAll, mark_start,
    Bool.true_and, if_true, chainCodeWeight, c01, c12, c21, c23,
    Bool.not_false, bad_finish, admissibleFamilyWeight, List.all_nil,
    familyCompatibleB_nil, familyActivity_nil]
  unfold commonWeight shortArm
  ring_qeqv

theorem longReserveCode_square_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        longReserveCode ≈
      commonWeight w label * (longArm w label * longArm w label) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
      longReserveCode =
        carrierXiCodeWeight w qAll markV0 badV3 Gamma label
          (eraseOccCarrierXiCode Gamma longReserveCode) from rfl]
  rw [longReserveCode_erasure]
  simp only [carrierXiCodeWeight, carrierCodeWeight, qAll, mark_start,
    Bool.true_and, if_true, chainCodeWeight, c07, c76, c66, c65, c54, c44,
    c43, Bool.not_false, bad_finish, admissibleFamilyWeight, List.all_cons,
    List.all_nil, Bool.and_self, familyCompatibleB_nil,
    longReserve_external_compatible,
    familyActivity_cons, familyActivity_nil]
  unfold commonWeight longArm
  ring_qeqv

def repairBlock : List (OccCarrierXiCodeAt Gamma) :=
  [shortBounceCode, longReserveCode]

theorem repairCodes_ne : shortBounceCode ≠ longReserveCode := by
  intro h
  have he := congrArg (eraseOccCarrierXiCode Gamma) h
  rw [shortBounceCode_erasure, longReserveCode_erasure] at he
  cases he

theorem repairBlock_nodup : repairBlock.Nodup := by
  simp [repairBlock, repairCodes_ne]

theorem repairBlock_mem (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ repairBlock) :
    code ∈ occurrenceCarrierXiCodes Gamma := by
  simp [repairBlock] at hcode
  rcases hcode with rfl | rfl
  · exact shortBounceCode_mem
  · exact longReserveCode_mem

theorem repairBlock_weight_eqv (w : Q') (label : TL.Plaquette → Rep) :
    qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        repairBlock ≈
      commonWeight w label *
        (shortArm w label * shortArm w label +
          longArm w label * longArm w label) := by
  simp only [repairBlock, qListSum_cons, qListSum_nil, Q'.add_zero']
  refine Q'.eqv_trans _
    (commonWeight w label * (shortArm w label * shortArm w label) +
      commonWeight w label * (longArm w label * longArm w label)) _ ?_ ?_
  · exact add_eqv_congr_both _ _ _ _
      (shortBounceCode_square_weight_eqv w label)
      (longReserveCode_square_weight_eqv w label)
  · ring_qeqv

theorem source_le_repairBlock {w : Q'} (hw : (0 : Q') ≤ w)
    (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label pair ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        repairBlock := by
  have hshort : (0 : Q') ≤ shortArm w label :=
    Q'.mul_nonneg _ _ (activity_nonneg hw V1 label)
      (activity_nonneg hw V2 label)
  have hlong : (0 : Q') ≤ longArm w label :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (activity_nonneg hw V7 label)
        (activity_nonneg hw V6 label))
      (Q'.mul_nonneg _ _ (activity_nonneg hw V5 label)
        (activity_nonneg hw V4 label))
  have hcommon : (0 : Q') ≤ commonWeight w label :=
    Q'.mul_nonneg _ _ (activity_nonneg hw V0 label)
      (activity_nonneg hw V3 label)
  have hsquares :=
    YMGap.Continuum.XiExceptionalMixedEarAbsorption.prod_le_square_sum
      hshort hlong
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (shortArm w label * longArm w label)
    (shortArm w label * shortArm w label +
      longArm w label * longArm w label)
    (commonWeight w label) hsquares hcommon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (source_weight_eqv w label))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.ge_of_eqv (repairBlock_weight_eqv w label)))

theorem unit_longReserveCode_weight :
    occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 Gamma
      labelOne longReserveCode = Q'.ofNat 1048576 := by
  decide

theorem unit_repairBlock_weight :
    qListSum
        (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 Gamma
          labelOne)
        repairBlock = Q'.ofNat 1052672 := by
  decide

theorem unit_source_le_longReserveCode :
    occurrencePairWeight unitWeight qAll markV0 badV3 Gamma labelOne pair ≤
      occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 Gamma
        labelOne longReserveCode := by
  decide

/-! ## General external-reserve fuel invariant -/

/-- A compatible external reserve covers the occurrence overflow exactly
when the full square multiplicity fits in carrier fuel plus reserve slots. -/
def externalReserveFitsB (full reserve fuel : Nat) : Bool :=
  decide (full ≤ fuel + reserve)

theorem externalReserveFitsB_true_iff (full reserve fuel : Nat) :
    externalReserveFitsB full reserve fuel = true ↔
      full ≤ fuel + reserve := by
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

theorem c8_externalReserve_fits : externalReserveFitsB 10 2 8 = true := by
  rfl

theorem longReserve_external_count :
    (selectByBits Gamma longReserveBits).length = 2 := by
  rfl

theorem longReserve_multiplicity_conservation :
    longReserveWalk.vertices.length +
        (selectByBits Gamma longReserveBits).length =
      (longArc.bounceWalk cycleEdge_symm).vertices.length := by
  rw [longReserveWalk_length, longReserve_external_count,
    longArc_bounce_length]

theorem longReserve_carrier_fits_exactly :
    longReserveWalk.vertices.length = Gamma.length := by
  rw [longReserveWalk_length]
  rfl

/-! ## The classifier is derived from an injective canonical source tag -/

def sourceTagCode : OccCarrierXiCodeAt Gamma :=
  exceptionalBranchCarrierCode Gamma qAll markV0 badV3 entry

theorem sourceTagCode_mem :
    sourceTagCode ∈ occurrenceCarrierXiCodes Gamma :=
  exceptionalBranchCarrierCode_mem Gamma qAll markV0 badV3 entry

def carriesSourceTagB
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) : Bool :=
  decide
    (exceptionalBranchCarrierCode Gamma qAll markV0 badV3 other =
      sourceTagCode)

theorem carriesSourceTagB_true_iff
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) :
    carriesSourceTagB other = true ↔ other = entry := by
  constructor
  · intro h
    exact exceptionalBranchCarrierCode_injective Gamma qAll markV0 badV3
      other entry (of_decide_eq_true h)
  · intro h
    subst other
    unfold carriesSourceTagB sourceTagCode
    exact decide_eq_true rfl

theorem sourceTagCode_recovers_entry
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3)
    (hcode : exceptionalBranchCarrierCode Gamma qAll markV0 badV3 other =
      sourceTagCode) :
    other = entry := by
  exact exceptionalBranchCarrierCode_injective Gamma qAll markV0 badV3
    other entry hcode

def allocator : MixedRepairAllocator Gamma qAll markV0 badV3 where
  test := carriesSourceTagB
  block := fun _ => repairBlock
  block_nodup := by
    intro _ _
    exact repairBlock_nodup
  block_mem := by
    intro _ _ code hcode
    exact repairBlock_mem code hcode
  blocks_disjoint := by
    intro a ha b hb hab
    have hae : a = entry := (carriesSourceTagB_true_iff a).mp ha
    have hbe : b = entry := (carriesSourceTagB_true_iff b).mp hb
    exact False.elim (hab (hae.trans hbe.symm))
  source_le_block := by
    intro w hw label other htest
    have hother : other = entry :=
      (carriesSourceTagB_true_iff other).mp htest
    subst other
    exact source_le_repairBlock hw label

theorem entry_test_true : allocator.test entry = true := by
  exact (carriesSourceTagB_true_iff entry).mpr rfl

theorem entry_mem_mixedRepairSource :
    entry ∈ mixedRepairSource allocator := by
  apply List.mem_filter.mpr
  exact ⟨entry_mem_threeBranchResidual, entry_test_true⟩

theorem entry_not_mem_fourBranchResidual :
    entry ∉ fourBranchResidualSource allocator := by
  intro hentry
  have htest := (fourBranchResidualSource_tests Gamma qAll markV0 badV3
    allocator entry hentry).2.2.2
  rw [entry_test_true] at htest
  cases htest

#print axioms unit_XiR_exact
#print axioms unit_connectingChainMajorant_exact
#print axioms unit_full_target_capacity
#print axioms longReserveWalk_length
#print axioms longReserveCode_mem
#print axioms longReserveCode_erasure
#print axioms source_weight_eqv
#print axioms shortBounceCode_square_weight_eqv
#print axioms longReserveCode_square_weight_eqv
#print axioms repairBlock_nodup
#print axioms repairBlock_mem
#print axioms repairBlock_weight_eqv
#print axioms source_le_repairBlock
#print axioms unit_longReserveCode_weight
#print axioms unit_repairBlock_weight
#print axioms unit_source_le_longReserveCode
#print axioms externalReserveFitsB_true_iff
#print axioms c8_externalReserve_fits
#print axioms longReserve_multiplicity_conservation
#print axioms longReserve_carrier_fits_exactly
#print axioms sourceTagCode_mem
#print axioms carriesSourceTagB_true_iff
#print axioms sourceTagCode_recovers_entry
#print axioms entry_mem_mixedRepairSource
#print axioms entry_not_mem_fourBranchResidual

end YMGap.Continuum.XiExceptionalUnbalancedCycleRepair
