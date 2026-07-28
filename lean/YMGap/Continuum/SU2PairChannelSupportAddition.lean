/-
# Additive closure of the SU(2) four-face pair-channel support

The four-spin face packet and its retained pair-channel state form an
additive support carrier.  If two packet/channel pairs pass all three
Clebsch--Gordan guards, their componentwise sum passes the same guards:
the two pair channels add, and then the final coarse channel adds.

This module also records the exact finite-cutoff statement.  Packets bounded
by `K` and `L` add to a packet bounded by `K + L`; pair channels in the
corresponding finite state spaces add to a channel in the summed state space.
Finally, strict positivity of the literal character/fusion raw weights is
equivalent, at positive coupling, to this three-guard support.  Consequently
two positive raw channels add to a positive raw channel at any positive
target coupling.

All proofs are constructive finite arithmetic.  No classical reasoning,
`sorry`, `native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.SU2FusionSupportAddition
import YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel

namespace YMGap.Continuum.SU2PairChannelSupportAddition

set_option maxRecDepth 8000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Componentwise addition and finite cutoffs -/

/-- Componentwise addition of the four fine-face spin labels. -/
def addFaceSpinPacket
    (left right : FaceSpinPacket) : FaceSpinPacket where
  spin0 := left.spin0 + right.spin0
  spin1 := left.spin1 + right.spin1
  spin2 := left.spin2 + right.spin2
  spin3 := left.spin3 + right.spin3

/-- Componentwise addition of the two retained pair channels and the final
coarse channel. -/
def addPairChannelState
    (left right : PairChannelState) : PairChannelState :=
  ((left.1.1 + right.1.1, left.1.2 + right.1.2),
    left.2 + right.2)

/-- Four packet coordinates bounded at two cutoffs remain bounded at the
literal summed cutoff. -/
theorem addFaceSpinPacket_mem
    {leftCutoff rightCutoff : Nat}
    {left right : FaceSpinPacket}
    (hleft : left ∈ faceSpinPacketStateSpace leftCutoff)
    (hright : right ∈ faceSpinPacketStateSpace rightCutoff) :
    addFaceSpinPacket left right ∈
      faceSpinPacketStateSpace (leftCutoff + rightCutoff) := by
  obtain ⟨left0, left1, left2, left3⟩ := left
  obtain ⟨right0, right1, right2, right3⟩ := right
  have hl :=
    (mem_faceSpinPacketStateSpace_iff leftCutoff
      (⟨left0, left1, left2, left3⟩ : FaceSpinPacket)).mp hleft
  have hr :=
    (mem_faceSpinPacketStateSpace_iff rightCutoff
      (⟨right0, right1, right2, right3⟩ : FaceSpinPacket)).mp hright
  change left0 ≤ leftCutoff ∧ left1 ≤ leftCutoff ∧
    left2 ≤ leftCutoff ∧ left3 ≤ leftCutoff at hl
  change right0 ≤ rightCutoff ∧ right1 ≤ rightCutoff ∧
    right2 ≤ rightCutoff ∧ right3 ≤ rightCutoff at hr
  apply
    (mem_faceSpinPacketStateSpace_iff
      (leftCutoff + rightCutoff)
      (addFaceSpinPacket
        ⟨left0, left1, left2, left3⟩
        ⟨right0, right1, right2, right3⟩)).mpr
  change left0 + right0 ≤ leftCutoff + rightCutoff ∧
    left1 + right1 ≤ leftCutoff + rightCutoff ∧
    left2 + right2 ≤ leftCutoff + rightCutoff ∧
    left3 + right3 ≤ leftCutoff + rightCutoff
  exact
    ⟨Nat.add_le_add hl.1 hr.1,
      Nat.add_le_add hl.2.1 hr.2.1,
      Nat.add_le_add hl.2.2.1 hr.2.2.1,
      Nat.add_le_add hl.2.2.2 hr.2.2.2⟩

/-- The two intermediate `2K` windows and final `4K` window add exactly into
the corresponding windows at cutoff `K + L`. -/
theorem addPairChannelState_mem
    {leftCutoff rightCutoff : Nat}
    {left right : PairChannelState}
    (hleft : left ∈ pairChannelStateSpace leftCutoff)
    (hright : right ∈ pairChannelStateSpace rightCutoff) :
    addPairChannelState left right ∈
      pairChannelStateSpace (leftCutoff + rightCutoff) := by
  rcases left with ⟨⟨leftPair0, leftPair1⟩, leftCoarse⟩
  rcases right with ⟨⟨rightPair0, rightPair1⟩, rightCoarse⟩
  have hl :=
    (mem_pairChannelStateSpace_iff leftCutoff
      ((leftPair0, leftPair1), leftCoarse)).mp hleft
  have hr :=
    (mem_pairChannelStateSpace_iff rightCutoff
      ((rightPair0, rightPair1), rightCoarse)).mp hright
  change leftPair0 ≤ 2 * leftCutoff ∧
    leftPair1 ≤ 2 * leftCutoff ∧
    leftCoarse ≤ 4 * leftCutoff at hl
  change rightPair0 ≤ 2 * rightCutoff ∧
    rightPair1 ≤ 2 * rightCutoff ∧
    rightCoarse ≤ 4 * rightCutoff at hr
  apply
    (mem_pairChannelStateSpace_iff
      (leftCutoff + rightCutoff)
      (addPairChannelState
        ((leftPair0, leftPair1), leftCoarse)
        ((rightPair0, rightPair1), rightCoarse))).mpr
  change leftPair0 + rightPair0 ≤
      2 * (leftCutoff + rightCutoff) ∧
    leftPair1 + rightPair1 ≤
      2 * (leftCutoff + rightCutoff) ∧
    leftCoarse + rightCoarse ≤
      4 * (leftCutoff + rightCutoff)
  constructor
  · rw [Nat.mul_add]
    exact Nat.add_le_add hl.1 hr.1
  · constructor
    · rw [Nat.mul_add]
      exact Nat.add_le_add hl.2.1 hr.2.1
    · rw [Nat.mul_add]
      exact Nat.add_le_add hl.2.2 hr.2.2

/-! ## 2. Additive closure of all three face fusion guards -/

/-- The literal support predicate of the four-face pair-channel summand:
the left pair fuses, the right pair fuses, and those two channels fuse to the
retained coarse label. -/
def PacketPairChannelSupported
    (packet : FaceSpinPacket) (state : PairChannelState) : Prop :=
  fusionOK packet.spin0 packet.spin1 state.1.1 = true ∧
    fusionOK packet.spin2 packet.spin3 state.1.2 = true ∧
      fusionOK state.1.1 state.1.2 state.2 = true

/-- All three Clebsch--Gordan guards survive componentwise addition. -/
theorem packetPairChannelSupported_add
    {leftPacket rightPacket : FaceSpinPacket}
    {leftState rightState : PairChannelState}
    (hleft : PacketPairChannelSupported leftPacket leftState)
    (hright : PacketPairChannelSupported rightPacket rightState) :
    PacketPairChannelSupported
      (addFaceSpinPacket leftPacket rightPacket)
      (addPairChannelState leftState rightState) := by
  rcases hleft with ⟨hleftPair, hrightPair, hcoarse⟩
  rcases hright with ⟨hleftPair', hrightPair', hcoarse'⟩
  exact
    ⟨fusionOK_add hleftPair hleftPair',
      fusionOK_add hrightPair hrightPair',
      fusionOK_add hcoarse hcoarse'⟩

/-! ## 3. Raw-weight positivity is exactly positive-coupling support -/

private theorem mul_eqv_zero_of_left
    {left right : Q'} (hleft : left ≈ 0) :
    left * right ≈ 0 := by
  exact Q'.eqv_trans _ (0 * right) _
    (Q'.mul_eqv_congr_right left 0 right hleft)
    (Q'.zero_mul_eqv right)

private theorem mul_eqv_zero_of_right
    {left right : Q'} (hright : right ≈ 0) :
    left * right ≈ 0 := by
  exact Q'.eqv_trans _ (left * 0) _
    (Q'.mul_eqv_congr_left left right 0 hright)
    (Q'.mul_zero_eqv left)

private theorem packetPairChannelRawWeight_eqv_zero_of_left_guard_false
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState)
    (hguard :
      fusionOK packet.spin0 packet.spin1 state.1.1 = false) :
    packetPairChannelRawWeight w packet state ≈ 0 := by
  have hind :
      fusionInd packet.spin0 packet.spin1 state.1.1 = (0 : Q') := by
    unfold fusionInd
    rw [if_neg]
    simp [hguard]
  unfold packetPairChannelRawWeight
  rw [hind]
  exact mul_eqv_zero_of_right
    (mul_eqv_zero_of_left (Q'.eqv_refl 0))

private theorem packetPairChannelRawWeight_eqv_zero_of_right_guard_false
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState)
    (hguard :
      fusionOK packet.spin2 packet.spin3 state.1.2 = false) :
    packetPairChannelRawWeight w packet state ≈ 0 := by
  have hind :
      fusionInd packet.spin2 packet.spin3 state.1.2 = (0 : Q') := by
    unfold fusionInd
    rw [if_neg]
    simp [hguard]
  unfold packetPairChannelRawWeight
  rw [hind]
  exact mul_eqv_zero_of_right
    (mul_eqv_zero_of_right
      (mul_eqv_zero_of_left (Q'.eqv_refl 0)))

private theorem packetPairChannelRawWeight_eqv_zero_of_coarse_guard_false
    (w : Q') (packet : FaceSpinPacket) (state : PairChannelState)
    (hguard :
      fusionOK state.1.1 state.1.2 state.2 = false) :
    packetPairChannelRawWeight w packet state ≈ 0 := by
  have hind :
      fusionInd state.1.1 state.1.2 state.2 = (0 : Q') := by
    unfold fusionInd
    rw [if_neg]
    simp [hguard]
  unfold packetPairChannelRawWeight
  rw [hind]
  exact mul_eqv_zero_of_right
    (mul_eqv_zero_of_right
      (mul_eqv_zero_of_right (Q'.eqv_refl 0)))

/-- A strictly positive raw summand cannot have a failed fusion guard.  This
direction does not require a sign hypothesis on the coupling: a failed guard
makes the raw weight exactly zero for every coupling. -/
theorem packetPairChannelSupported_of_rawWeight_pos
    {w : Q'} {packet : FaceSpinPacket} {state : PairChannelState}
    (hraw : (0 : Q') <
      packetPairChannelRawWeight w packet state) :
    PacketPairChannelSupported packet state := by
  constructor
  · cases hguard :
      fusionOK packet.spin0 packet.spin1 state.1.1 with
    | false =>
        have hzero :=
          packetPairChannelRawWeight_eqv_zero_of_left_guard_false
            w packet state hguard
        exact False.elim
          (Int.not_lt_of_ge (Q'.le_of_eqv hzero) hraw)
    | true => rfl
  · constructor
    · cases hguard :
        fusionOK packet.spin2 packet.spin3 state.1.2 with
      | false =>
          have hzero :=
            packetPairChannelRawWeight_eqv_zero_of_right_guard_false
              w packet state hguard
          exact False.elim
            (Int.not_lt_of_ge (Q'.le_of_eqv hzero) hraw)
      | true => rfl
    · cases hguard :
        fusionOK state.1.1 state.1.2 state.2 with
      | false =>
          have hzero :=
            packetPairChannelRawWeight_eqv_zero_of_coarse_guard_false
              w packet state hguard
          exact False.elim
            (Int.not_lt_of_ge (Q'.le_of_eqv hzero) hraw)
      | true => rfl

/-- At positive coupling, the three fusion guards make the raw summand
strictly positive. -/
theorem packetPairChannelRawWeight_pos_of_supported
    {w : Q'} (hw : (0 : Q') < w)
    {packet : FaceSpinPacket} {state : PairChannelState}
    (hsupport : PacketPairChannelSupported packet state) :
    (0 : Q') < packetPairChannelRawWeight w packet state := by
  rcases hsupport with ⟨hleft, hright, hcoarse⟩
  have hleftInd :
      fusionInd packet.spin0 packet.spin1 state.1.1 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hleft]
  have hrightInd :
      fusionInd packet.spin2 packet.spin3 state.1.2 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hright]
  have hcoarseInd :
      fusionInd state.1.1 state.1.2 state.2 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hcoarse]
  unfold packetPairChannelRawWeight
  rw [hleftInd, hrightInd, hcoarseInd]
  exact Q'.mul_pos (coeffW_pos hw state.2) (by decide)

/-- Positive raw channels form an additive support monoid.  The two source
couplings need not be related to the target coupling: source positivity
extracts the discrete fusion support, and any positive target coupling gives
a positive heat coefficient on the summed coarse label. -/
theorem packetPairChannelRawWeight_add_pos
    {leftCoupling rightCoupling targetCoupling : Q'}
    (htarget : (0 : Q') < targetCoupling)
    {leftPacket rightPacket : FaceSpinPacket}
    {leftState rightState : PairChannelState}
    (hleft : (0 : Q') <
      packetPairChannelRawWeight
        leftCoupling leftPacket leftState)
    (hright : (0 : Q') <
      packetPairChannelRawWeight
        rightCoupling rightPacket rightState) :
    (0 : Q') <
      packetPairChannelRawWeight targetCoupling
        (addFaceSpinPacket leftPacket rightPacket)
        (addPairChannelState leftState rightState) := by
  apply packetPairChannelRawWeight_pos_of_supported htarget
  exact packetPairChannelSupported_add
    (packetPairChannelSupported_of_rawWeight_pos hleft)
    (packetPairChannelSupported_of_rawWeight_pos hright)

/-- The complete finite-window statement: bounded positive source channels
add to a bounded positive channel in the summed packet and pair-channel
cutoffs. -/
theorem packetPairChannel_add_mem_and_rawWeight_pos
    {leftCutoff rightCutoff : Nat}
    {leftCoupling rightCoupling targetCoupling : Q'}
    (htarget : (0 : Q') < targetCoupling)
    {leftPacket rightPacket : FaceSpinPacket}
    {leftState rightState : PairChannelState}
    (hleftPacket :
      leftPacket ∈ faceSpinPacketStateSpace leftCutoff)
    (hrightPacket :
      rightPacket ∈ faceSpinPacketStateSpace rightCutoff)
    (hleftState :
      leftState ∈ pairChannelStateSpace leftCutoff)
    (hrightState :
      rightState ∈ pairChannelStateSpace rightCutoff)
    (hleftRaw : (0 : Q') <
      packetPairChannelRawWeight
        leftCoupling leftPacket leftState)
    (hrightRaw : (0 : Q') <
      packetPairChannelRawWeight
        rightCoupling rightPacket rightState) :
    addFaceSpinPacket leftPacket rightPacket ∈
        faceSpinPacketStateSpace (leftCutoff + rightCutoff) ∧
      addPairChannelState leftState rightState ∈
        pairChannelStateSpace (leftCutoff + rightCutoff) ∧
      (0 : Q') <
        packetPairChannelRawWeight targetCoupling
          (addFaceSpinPacket leftPacket rightPacket)
          (addPairChannelState leftState rightState) := by
  exact
    ⟨addFaceSpinPacket_mem hleftPacket hrightPacket,
      addPairChannelState_mem hleftState hrightState,
      packetPairChannelRawWeight_add_pos
        htarget hleftRaw hrightRaw⟩

/-! ## 4. Finite additive stacks of bounded face layers -/

/-- One face layer carrying its own finite cutoff, packet/channel membership,
and the three constructive fusion witnesses.  The carrier is `Type`-level so
that iterated addition retains all data. -/
structure BoundedSupportedPacketPairLayer : Type where
  cutoff : Nat
  packet : FaceSpinPacket
  state : PairChannelState
  packet_mem : packet ∈ faceSpinPacketStateSpace cutoff
  state_mem : state ∈ pairChannelStateSpace cutoff
  supported : PacketPairChannelSupported packet state

/-- The vacuum layer is the additive identity, including at cutoff zero. -/
def zeroBoundedSupportedPacketPairLayer :
    BoundedSupportedPacketPairLayer where
  cutoff := 0
  packet := ⟨0, 0, 0, 0⟩
  state := ((0, 0), 0)
  packet_mem := by
    apply (mem_faceSpinPacketStateSpace_iff 0 _).mpr
    decide
  state_mem := by
    apply (mem_pairChannelStateSpace_iff 0 _).mpr
    decide
  supported := by
    unfold PacketPairChannelSupported
    decide

/-- Binary addition of bounded supported layers.  Its cutoff is the literal
sum of the two input cutoffs. -/
def addBoundedSupportedPacketPairLayer
    (left right : BoundedSupportedPacketPairLayer) :
    BoundedSupportedPacketPairLayer where
  cutoff := left.cutoff + right.cutoff
  packet := addFaceSpinPacket left.packet right.packet
  state := addPairChannelState left.state right.state
  packet_mem :=
    addFaceSpinPacket_mem left.packet_mem right.packet_mem
  state_mem :=
    addPairChannelState_mem left.state_mem right.state_mem
  supported :=
    packetPairChannelSupported_add left.supported right.supported

/-- A finite ordered stack of face layers, combined without discarding any
cutoff or support witness. -/
def sumBoundedSupportedPacketPairLayers :
    List BoundedSupportedPacketPairLayer →
      BoundedSupportedPacketPairLayer
  | [] => zeroBoundedSupportedPacketPairLayer
  | layer :: layers =>
      addBoundedSupportedPacketPairLayer layer
        (sumBoundedSupportedPacketPairLayers layers)

/-- Every finite supported layer stack has a strictly positive literal raw
weight at every positive target coupling. -/
theorem sumBoundedSupportedPacketPairLayers_rawWeight_pos
    {w : Q'} (hw : (0 : Q') < w)
    (layers : List BoundedSupportedPacketPairLayer) :
    (0 : Q') <
      packetPairChannelRawWeight w
        (sumBoundedSupportedPacketPairLayers layers).packet
        (sumBoundedSupportedPacketPairLayers layers).state := by
  exact packetPairChannelRawWeight_pos_of_supported hw
    (sumBoundedSupportedPacketPairLayers layers).supported

#print axioms addFaceSpinPacket_mem
#print axioms addPairChannelState_mem
#print axioms packetPairChannelSupported_add
#print axioms packetPairChannelSupported_of_rawWeight_pos
#print axioms packetPairChannelRawWeight_pos_of_supported
#print axioms packetPairChannelRawWeight_add_pos
#print axioms packetPairChannel_add_mem_and_rawWeight_pos
#print axioms zeroBoundedSupportedPacketPairLayer
#print axioms addBoundedSupportedPacketPairLayer
#print axioms sumBoundedSupportedPacketPairLayers
#print axioms sumBoundedSupportedPacketPairLayers_rawWeight_pos

end YMGap.Continuum.SU2PairChannelSupportAddition
