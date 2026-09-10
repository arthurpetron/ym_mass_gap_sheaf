/-
# Exact lower-triangular kernel of the canonical spin-four packets

The maximal retained channel gives the intended coarse heat coefficient, but
the complete raw row also contains lower retained spins.  This file computes
that entire local kernel without numerical approximation.  Its coefficient
is the number of supported SU(2) pair-fusion paths with the prescribed final
spin, so every canonical packet has

  fixedFinalWeight(source, target)
    = multiplicity(source, target) * coeffW(w, target).

For sources and targets zero through four the multiplicity matrix is

  [1 0 0 0 0]
  [0 1 0 0 0]
  [1 0 1 0 0]
  [0 2 0 1 0]
  [2 0 3 0 1].

Thus the off-target terms are exactly parity-preserving downward fusion
channels.  The final section lifts the local identity through every face and
the complete shared-link product, reducing the whole raw row to an explicit
lower-triangular coarse spin-foam weight.

Constructive contract: finite exact-rational sums and decidable SU(2) fusion
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourWholeSlabTargetExact

namespace YMGap.Continuum.Z4DyadicSpinFourLoweringKernel

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
open YMGap.Continuum.Z4DyadicPairBubbleWholeSlabRawContraction
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSpinFourWholeSlabTargetExact
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Supported path multiplicity -/

/-- A supported internal pair channel ending at the selected retained spin. -/
def spinFourLoweringChannelB
    (sourceSpin targetSpin : Nat) (state : PairChannelState) : Bool :=
  packetPairChannelSupportedBool (spinFourPacket sourceSpin) state &&
    decide (state.2 = targetSpin)

/-- The literal number of supported internal paths from a canonical source
packet to a retained target spin. -/
def spinFourLoweringMultiplicity
    (sourceSpin targetSpin : Nat) : Nat :=
  ((pairChannelStateSpace 1).filter
    (spinFourLoweringChannelB sourceSpin targetSpin)).length

/-- Closed presentation of the complete cutoff-one multiplicity matrix. -/
def spinFourLoweringMultiplicityTable : Nat → Nat → Nat
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 0 => 1
  | 2, 2 => 1
  | 3, 1 => 2
  | 3, 3 => 1
  | 4, 0 => 2
  | 4, 2 => 3
  | 4, 4 => 1
  | _, _ => 0

/-- Kernel-checked evaluation of every entry in the five-by-five local
multiplicity matrix. -/
theorem spinFourLoweringMultiplicity_eq_table
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4) :
    spinFourLoweringMultiplicity sourceSpin targetSpin =
      spinFourLoweringMultiplicityTable sourceSpin targetSpin := by
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  have ht : targetSpin = 0 ∨ targetSpin = 1 ∨ targetSpin = 2 ∨
      targetSpin = 3 ∨ targetSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The exact support of the local matrix is downward and parity preserving. -/
theorem spinFourLoweringMultiplicity_pos_iff
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4) :
    0 < spinFourLoweringMultiplicity sourceSpin targetSpin ↔
      targetSpin ≤ sourceSpin ∧ targetSpin % 2 = sourceSpin % 2 := by
  rw [spinFourLoweringMultiplicity_eq_table hsource htarget]
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  have ht : targetSpin = 0 ∨ targetSpin = 1 ∨ targetSpin = 2 ∨
      targetSpin = 3 ∨ targetSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 2. Exact fixed-final weight -/

private theorem mul_eqv_zero_of_left_local
    {left right : Q'} (hleft : left ≈ 0) :
    left * right ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right left 0 right hleft)
    (Q'.zero_mul_eqv right)

private theorem mul_eqv_zero_of_right_local
    {left right : Q'} (hright : right ≈ 0) :
    left * right ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left left right 0 hright)
    (Q'.mul_zero_eqv left)

private theorem packetPairChannelRawWeight_eqv_zero_of_support_false_local
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState)
    (hsupport : packetPairChannelSupportedBool packet state = false) :
    packetPairChannelRawWeight w packet state ≈ 0 := by
  unfold packetPairChannelSupportedBool at hsupport
  cases hleft : fusionOK packet.spin0 packet.spin1 state.1.1 with
  | false =>
      have hind :
          fusionInd packet.spin0 packet.spin1 state.1.1 = (0 : Q') := by
        unfold fusionInd
        simp [hleft]
      unfold packetPairChannelRawWeight
      rw [hind]
      exact mul_eqv_zero_of_right_local
        (mul_eqv_zero_of_left_local (Q'.eqv_refl 0))
  | true =>
      cases hright : fusionOK packet.spin2 packet.spin3 state.1.2 with
      | false =>
          have hind :
              fusionInd packet.spin2 packet.spin3 state.1.2 = (0 : Q') := by
            unfold fusionInd
            simp [hright]
          unfold packetPairChannelRawWeight
          rw [hind]
          exact mul_eqv_zero_of_right_local
            (mul_eqv_zero_of_right_local
              (mul_eqv_zero_of_left_local (Q'.eqv_refl 0)))
      | true =>
          cases hcoarse : fusionOK state.1.1 state.1.2 state.2 with
          | false =>
              have hind :
                  fusionInd state.1.1 state.1.2 state.2 = (0 : Q') := by
                unfold fusionInd
                simp [hcoarse]
              unfold packetPairChannelRawWeight
              rw [hind]
              exact mul_eqv_zero_of_right_local
                (mul_eqv_zero_of_right_local
                  (mul_eqv_zero_of_right_local (Q'.eqv_refl 0)))
          | true => simp [hleft, hright, hcoarse] at hsupport

private theorem packetPairChannelRawWeight_eqv_coeffW_of_supported_local
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState)
    (hsupport : packetPairChannelSupportedBool packet state = true) :
    packetPairChannelRawWeight w packet state ≈ coeffW w state.2 := by
  unfold packetPairChannelSupportedBool at hsupport
  simp only [Bool.and_eq_true] at hsupport
  have hleft :
      fusionInd packet.spin0 packet.spin1 state.1.1 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hsupport.1.1]
  have hright :
      fusionInd packet.spin2 packet.spin3 state.1.2 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hsupport.1.2]
  have hfinal :
      fusionInd state.1.1 state.1.2 state.2 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hsupport.2]
  unfold packetPairChannelRawWeight
  rw [hleft, hright, hfinal]
  exact Q'.eqv_trans _ (coeffW w state.2 * 1) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ (1 * 1) _
        (Q'.one_mul_eqv (1 * 1)) (Q'.one_mul_eqv 1)))
    (Q'.mul_one_eqv _)

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source → test item = false → value item ≈ 0) →
      listQSum value source ≈ listQSum value (source.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false → value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv _ constant)

/-- The complete fixed-final face sum is one heat coefficient multiplied by
the exact number of supported pair-fusion paths. -/
theorem spinFourPacket_fixedFinalFaceRawWeight_eqv_multiplicity_mul_coeffW
    (w : Q') (sourceSpin targetSpin : Nat) :
    fixedFinalFaceRawWeight w (spinFourPacket sourceSpin) targetSpin ≈
      Q'.ofNat (spinFourLoweringMultiplicity sourceSpin targetSpin) *
        coeffW w targetSpin := by
  let selected := (pairChannelStateSpace 1).filter
    (spinFourLoweringChannelB sourceSpin targetSpin)
  let value : PairChannelState → Q' := fun state =>
    if state.2 = targetSpin then
      packetPairChannelRawWeight w (spinFourPacket sourceSpin) state
    else 0
  refine Q'.eqv_trans _ (listQSum value selected) _ ?_ ?_
  · unfold fixedFinalFaceRawWeight value selected
    apply listQSum_eq_filter_of_zero_local
    intro state _ hselected
    by_cases hfinal : state.2 = targetSpin
    · rw [if_pos hfinal]
      have hsfalse :
          packetPairChannelSupportedBool
              (spinFourPacket sourceSpin) state = false := by
        unfold spinFourLoweringChannelB at hselected
        rw [show decide (state.2 = targetSpin) = true from
          decide_eq_true hfinal, Bool.and_true] at hselected
        exact hselected
      exact packetPairChannelRawWeight_eqv_zero_of_support_false_local
        w (spinFourPacket sourceSpin) state hsfalse
    · rw [if_neg hfinal]
      exact Q'.eqv_refl 0
  · refine Q'.eqv_trans _
      (listQSum (fun _state => coeffW w targetSpin) selected) _ ?_ ?_
    · apply listQSum_congr_on
      intro state hstate
      have hselected := (List.mem_filter.mp hstate).2
      unfold spinFourLoweringChannelB at hselected
      simp only [Bool.and_eq_true] at hselected
      have hparts := hselected
      have hfinal : state.2 = targetSpin := of_decide_eq_true hparts.2
      unfold value
      rw [if_pos hfinal]
      exact Q'.eqv_trans _ (coeffW w state.2) _
        (packetPairChannelRawWeight_eqv_coeffW_of_supported_local
          w (spinFourPacket sourceSpin) state hparts.1)
        (Q'.eqv_of_eq (congrArg (coeffW w) hfinal))
    · simpa only [selected, spinFourLoweringMultiplicity] using
        (listQSum_const_local (coeffW w targetSpin) selected)

/-! ## 3. Whole-slab lower-triangular row -/

/-- Explicit local coefficient of the canonical lower-triangular row. -/
def spinFourLoweringFaceWeight
    (w : Q') (sourceSpin targetSpin : Nat) : Q' :=
  Q'.ofNat (spinFourLoweringMultiplicity sourceSpin targetSpin) *
    coeffW w targetSpin

/-- The resulting complete coarse spin-foam weight, including the original
globally shared coarse-link multiplicity. -/
def spinFourLoweringWholeSlabRawWeight
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling) : Q' :=
  wholeSlabFiniteQProduct
      (fun faceId => spinFourLoweringFaceWeight S.coarse.coupling
        (sourceState faceId) (targetState faceId))
      S.coarse.faceEdges *
    Q'.ofNat
      (slabExplicitLinkMultiplicityProduct
        S.coarse.cutoff S.coarse.extent targetState)

private theorem wholeSlabFiniteQProduct_congr_on_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≈ right item) →
      wholeSlabFiniteQProduct left items ≈
        wholeSlabFiniteQProduct right items
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree => by
      change
        left head * wholeSlabFiniteQProduct left tail ≈
          right head * wholeSlabFiniteQProduct right tail
      exact Q'.eqv_trans _
        (right head * wholeSlabFiniteQProduct left tail) _
        (Q'.mul_eqv_congr_right _ _ _
          (hagree head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (wholeSlabFiniteQProduct_congr_on_local left right tail
            (fun item hmem =>
              hagree item (List.mem_cons_of_mem head hmem))))

/-- A canonical packet profile identifies every entry of the complete raw
row with the explicit lower-triangular coarse spin-foam weight. -/
theorem wholeSlabRecouplingRawWeight_spinFourProfile_eqv_loweringWeight
    (S : SlabScalePair) (fineState sourceState targetState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (profile : SpinFourWholeSlabPacketProfile S fineState sourceState) :
    wholeSlabRecouplingRawWeight S fineState targetState ≈
      spinFourLoweringWholeSlabRawWeight S sourceState targetState := by
  unfold wholeSlabRecouplingRawWeight
    spinFourLoweringWholeSlabRawWeight
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight S fineState targetState)
      S.coarse.faceEdges) _
    (wholeSlabFaceRawProduct_eqv_finiteQProduct
      S fineState targetState) ?_
  apply wholeSlabFiniteQProduct_congr_on_local
  intro faceId hface
  refine Q'.eqv_trans _ _ _
    (wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
      S fineState targetState faceId
      (spinFourPacket (sourceState faceId)) hfineCutoff
      (profile.packet_eq faceId hface)) ?_
  exact
    spinFourPacket_fixedFinalFaceRawWeight_eqv_multiplicity_mul_coeffW
      S.coarse.coupling (sourceState faceId) (targetState faceId)

/-- Concrete endpoint form: the entire raw row of the canonical accepted
fine source is now an explicit lower-triangular weight on coarse states. -/
theorem wholeSlabRecouplingRawWeight_attachedEndpointSpinFour_eqv_loweringWeight
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (targetState : EdgeLabelling) :
    wholeSlabRecouplingRawWeight S
        (attachedEndpointSpinFourFineState S endpoint) targetState ≈
      spinFourLoweringWholeSlabRawWeight S endpoint.1.1 targetState :=
  wholeSlabRecouplingRawWeight_spinFourProfile_eqv_loweringWeight
    S (attachedEndpointSpinFourFineState S endpoint) endpoint.1.1
      targetState hfineCutoff
      (attachedEndpointSpinFourWholeSlabPacketProfile
        S endpoint hfineCutoff)

#print axioms spinFourLoweringMultiplicity_eq_table
#print axioms spinFourLoweringMultiplicity_pos_iff
#print axioms spinFourPacket_fixedFinalFaceRawWeight_eqv_multiplicity_mul_coeffW
#print axioms wholeSlabRecouplingRawWeight_spinFourProfile_eqv_loweringWeight
#print axioms wholeSlabRecouplingRawWeight_attachedEndpointSpinFour_eqv_loweringWeight

end YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
