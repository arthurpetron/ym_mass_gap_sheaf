/-
# Exact lowering kernel of every binary four-strand packet

The canonical spin-four packets choose one convenient placement of zero
through four fundamental strands.  A general cutoff-one fine source need not
use that placement.  This file removes that ordering dependence.

For an arbitrary binary packet, the complete fixed-final face sum is one heat
coefficient multiplied by the number of supported pair-fusion paths.  A
kernel-checked census of all sixteen binary packets and five retained spins
then proves that this multiplicity depends only on the packet's total spin and
is exactly the canonical spin-four multiplicity.

Constructive contract: finite exact-rational sums and decidable SU(2) fusion
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourLoweringKernel

namespace YMGap.Continuum.Z4DyadicBinaryPacketLoweringKernel

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The arbitrary-packet supported-path count -/

/-- A supported internal pair channel of an arbitrary packet ending at the
selected retained spin. -/
def binaryPacketLoweringChannelB
    (packet : FaceSpinPacket) (targetSpin : Nat)
    (state : PairChannelState) : Bool :=
  packetPairChannelSupportedBool packet state &&
    decide (state.2 = targetSpin)

/-- The number of supported cutoff-one pair-fusion paths from an arbitrary
binary packet to the selected retained spin. -/
def binaryPacketLoweringMultiplicity
    (packet : FaceSpinPacket) (targetSpin : Nat) : Nat :=
  ((pairChannelStateSpace 1).filter
    (binaryPacketLoweringChannelB packet targetSpin)).length

/-- A binary four-strand packet has total twice-spin at most four. -/
theorem faceSpinPacketTotal_le_four_of_binary
    {packet : FaceSpinPacket} (hbinary : PacketBinary packet) :
    faceSpinPacketTotal packet ≤ 4 := by
  rcases hbinary with ⟨h0, h1, h2, h3⟩
  unfold faceSpinPacketTotal
  omega

/-- The exact fusion-path multiplicity is insensitive to the placement of
the fundamental strands.  It depends only on their total number. -/
theorem binaryPacketLoweringMultiplicity_eq_spinFour
    (packet : FaceSpinPacket) (targetSpin : Nat)
    (hbinary : PacketBinary packet) (htarget : targetSpin ≤ 4) :
    binaryPacketLoweringMultiplicity packet targetSpin =
      spinFourLoweringMultiplicity
        (faceSpinPacketTotal packet) targetSpin := by
  obtain ⟨spin0, spin1, spin2, spin3⟩ := packet
  rcases hbinary with ⟨h0, h1, h2, h3⟩
  change spin0 ≤ 1 at h0
  change spin1 ≤ 1 at h1
  change spin2 ≤ 1 at h2
  change spin3 ≤ 1 at h3
  have hc0 : spin0 = 0 ∨ spin0 = 1 := by omega
  have hc1 : spin1 = 0 ∨ spin1 = 1 := by omega
  have hc2 : spin2 = 0 ∨ spin2 = 1 := by omega
  have hc3 : spin3 = 0 ∨ spin3 = 1 := by omega
  have ht : targetSpin = 0 ∨ targetSpin = 1 ∨ targetSpin = 2 ∨
      targetSpin = 3 ∨ targetSpin = 4 := by
    omega
  rcases hc0 with rfl | rfl <;>
    rcases hc1 with rfl | rfl <;>
    rcases hc2 with rfl | rfl <;>
    rcases hc3 with rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Closed-table presentation of the arbitrary binary-packet kernel. -/
theorem binaryPacketLoweringMultiplicity_eq_table
    (packet : FaceSpinPacket) (targetSpin : Nat)
    (hbinary : PacketBinary packet) (htarget : targetSpin ≤ 4) :
    binaryPacketLoweringMultiplicity packet targetSpin =
      spinFourLoweringMultiplicityTable
        (faceSpinPacketTotal packet) targetSpin := by
  rw [binaryPacketLoweringMultiplicity_eq_spinFour packet targetSpin
    hbinary htarget]
  exact spinFourLoweringMultiplicity_eq_table
    (faceSpinPacketTotal_le_four_of_binary hbinary) htarget

/-- The arbitrary-packet support is precisely parity-preserving lowering from
the packet's total twice-spin. -/
theorem binaryPacketLoweringMultiplicity_pos_iff
    (packet : FaceSpinPacket) (targetSpin : Nat)
    (hbinary : PacketBinary packet) (htarget : targetSpin ≤ 4) :
    0 < binaryPacketLoweringMultiplicity packet targetSpin ↔
      targetSpin ≤ faceSpinPacketTotal packet ∧
        targetSpin % 2 = faceSpinPacketTotal packet % 2 := by
  rw [binaryPacketLoweringMultiplicity_eq_spinFour packet targetSpin
    hbinary htarget]
  exact spinFourLoweringMultiplicity_pos_iff
    (faceSpinPacketTotal_le_four_of_binary hbinary) htarget

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

/-- The complete fixed-final face sum for an arbitrary packet is one heat
coefficient multiplied by its exact supported-path count. -/
theorem binaryPacket_fixedFinalFaceRawWeight_eqv_multiplicity_mul_coeffW
    (w : Q') (packet : FaceSpinPacket) (targetSpin : Nat) :
    fixedFinalFaceRawWeight w packet targetSpin ≈
      Q'.ofNat (binaryPacketLoweringMultiplicity packet targetSpin) *
        coeffW w targetSpin := by
  let selected := (pairChannelStateSpace 1).filter
    (binaryPacketLoweringChannelB packet targetSpin)
  let value : PairChannelState → Q' := fun state =>
    if state.2 = targetSpin then
      packetPairChannelRawWeight w packet state
    else 0
  refine Q'.eqv_trans _ (listQSum value selected) _ ?_ ?_
  · unfold fixedFinalFaceRawWeight value selected
    apply listQSum_eq_filter_of_zero_local
    intro state _ hselected
    by_cases hfinal : state.2 = targetSpin
    · rw [if_pos hfinal]
      have hsfalse :
          packetPairChannelSupportedBool packet state = false := by
        unfold binaryPacketLoweringChannelB at hselected
        rw [show decide (state.2 = targetSpin) = true from
          decide_eq_true hfinal, Bool.and_true] at hselected
        exact hselected
      exact packetPairChannelRawWeight_eqv_zero_of_support_false_local
        w packet state hsfalse
    · rw [if_neg hfinal]
      exact Q'.eqv_refl 0
  · refine Q'.eqv_trans _
      (listQSum (fun _state => coeffW w targetSpin) selected) _ ?_ ?_
    · apply listQSum_congr_on
      intro state hstate
      have hselected := (List.mem_filter.mp hstate).2
      unfold binaryPacketLoweringChannelB at hselected
      simp only [Bool.and_eq_true] at hselected
      have hparts := hselected
      have hfinal : state.2 = targetSpin := of_decide_eq_true hparts.2
      unfold value
      rw [if_pos hfinal]
      exact Q'.eqv_trans _ (coeffW w state.2) _
        (packetPairChannelRawWeight_eqv_coeffW_of_supported_local
          w packet state hparts.1)
        (Q'.eqv_of_eq (congrArg (coeffW w) hfinal))
    · simpa only [selected, binaryPacketLoweringMultiplicity] using
        (listQSum_const_local (coeffW w targetSpin) selected)

/-- For a binary source packet, the arbitrary fixed-final weight is exactly
the canonical spin-four coefficient indexed by total source spin. -/
theorem binaryPacket_fixedFinalFaceRawWeight_eqv_spinFourMultiplicity
    (w : Q') (packet : FaceSpinPacket) (targetSpin : Nat)
    (hbinary : PacketBinary packet) (htarget : targetSpin ≤ 4) :
    fixedFinalFaceRawWeight w packet targetSpin ≈
      Q'.ofNat
          (spinFourLoweringMultiplicity
            (faceSpinPacketTotal packet) targetSpin) *
        coeffW w targetSpin := by
  exact Q'.eqv_trans _
    (Q'.ofNat (binaryPacketLoweringMultiplicity packet targetSpin) *
      coeffW w targetSpin) _
    (binaryPacket_fixedFinalFaceRawWeight_eqv_multiplicity_mul_coeffW
      w packet targetSpin)
    (Q'.eqv_of_eq (congrArg
      (fun multiplicity => Q'.ofNat multiplicity * coeffW w targetSpin)
      (binaryPacketLoweringMultiplicity_eq_spinFour
        packet targetSpin hbinary htarget)))

/-! ## 3. Axiom audit -/

#print axioms faceSpinPacketTotal_le_four_of_binary
#print axioms binaryPacketLoweringMultiplicity_eq_spinFour
#print axioms binaryPacketLoweringMultiplicity_eq_table
#print axioms binaryPacketLoweringMultiplicity_pos_iff
#print axioms binaryPacket_fixedFinalFaceRawWeight_eqv_multiplicity_mul_coeffW
#print axioms binaryPacket_fixedFinalFaceRawWeight_eqv_spinFourMultiplicity

end YMGap.Continuum.Z4DyadicBinaryPacketLoweringKernel
