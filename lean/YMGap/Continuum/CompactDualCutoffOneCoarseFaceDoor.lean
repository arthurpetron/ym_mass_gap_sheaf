/-
# Cutoff-one coarse-face coherence door

The whole-slab recoupling carrier leaves one global existence theorem.  At
the first physical cutoff, its face part admits a canonical choice: fuse each
pair of binary fine labels to its parity and then fuse the two pair parities
to the total parity.  This module proves that channel is in the exact finite
state space and has strictly positive raw mass at every positive coupling.

Thus the cutoff-one face choices glue to the already constructed cellular
parity image.  The remaining cutoff-one coherence obligation is purely at
the coarse links: use mod-two closure of that image to exhibit a positive
vacuum-ending link fusion path.  Higher cutoffs still require the full
intertwiner recoupling theorem.
-/

import YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel

namespace YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

local infix:50 " ≈ " => Q'.eqv

def PacketBinary (packet : FaceSpinPacket) : Prop :=
  packet.spin0 ≤ 1 ∧ packet.spin1 ≤ 1 ∧
    packet.spin2 ≤ 1 ∧ packet.spin3 ≤ 1

/-- Pair parities and total parity in the same balanced channel coordinates
used by the production face kernel. -/
def binaryPacketParityChannel
    (packet : FaceSpinPacket) : PairChannelState :=
  (((packet.spin0 + packet.spin1) % 2,
      (packet.spin2 + packet.spin3) % 2),
    (packet.spin0 + packet.spin1 +
      packet.spin2 + packet.spin3) % 2)

theorem binaryPacketParityChannel_mem
    (packet : FaceSpinPacket) :
    binaryPacketParityChannel packet ∈ pairChannelStateSpace 1 := by
  apply (mem_pairChannelStateSpace_iff 1 _).mpr
  unfold binaryPacketParityChannel
  have htwo : 0 < 2 := by decide
  exact ⟨Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ htwo)) (by omega),
    Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ htwo)) (by omega),
    Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ htwo)) (by omega)⟩

theorem binaryPacketParityChannel_fusions
    (packet : FaceSpinPacket) (hbinary : PacketBinary packet) :
    fusionOK packet.spin0 packet.spin1
          (binaryPacketParityChannel packet).1.1 = true ∧
      fusionOK packet.spin2 packet.spin3
          (binaryPacketParityChannel packet).1.2 = true ∧
      fusionOK
          (binaryPacketParityChannel packet).1.1
          (binaryPacketParityChannel packet).1.2
          (binaryPacketParityChannel packet).2 = true := by
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
  rcases hc0 with rfl | rfl <;>
    rcases hc1 with rfl | rfl <;>
    rcases hc2 with rfl | rfl <;>
    rcases hc3 with rfl | rfl <;> decide

private theorem fusionInd_eq_one_of_true
    {a b c : Nat} (h : fusionOK a b c = true) :
    fusionInd a b c = 1 := by
  unfold fusionInd
  rw [if_pos h]

/-- The canonical binary parity channel is a strictly positive exact
character/fusion summand. -/
theorem binaryPacketParityChannel_rawWeight_pos
    {w : Q'} (hw : (0 : Q') < w)
    (packet : FaceSpinPacket) (hbinary : PacketBinary packet) :
    (0 : Q') <
      packetPairChannelRawWeight w packet
        (binaryPacketParityChannel packet) := by
  have hfusions := binaryPacketParityChannel_fusions packet hbinary
  unfold packetPairChannelRawWeight
  exact Q'.mul_pos
    (coeffW_pos hw (binaryPacketParityChannel packet).2)
    (Q'.mul_pos
      (by
        rw [fusionInd_eq_one_of_true hfusions.1]
        decide)
      (Q'.mul_pos
        (by
          rw [fusionInd_eq_one_of_true hfusions.2.1]
          decide)
        (by
          rw [fusionInd_eq_one_of_true hfusions.2.2]
          decide)))

def fixedFinalFaceRawWeight
    (w : Q') (packet : FaceSpinPacket) (finalSpin : Nat) : Q' :=
  listQSum
    (fun channel =>
      if channel.2 = finalSpin then
        packetPairChannelRawWeight w packet channel
      else 0)
    (pairChannelStateSpace 1)

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

/-- After marginalizing both pair channels, the parity-selected final
character still has strictly positive face mass. -/
theorem fixedFinalFaceRawWeight_parity_pos
    {w : Q'} (hw : (0 : Q') < w)
    (packet : FaceSpinPacket) (hbinary : PacketBinary packet) :
    (0 : Q') <
      fixedFinalFaceRawWeight w packet
        (binaryPacketParityChannel packet).2 := by
  let witness := binaryPacketParityChannel packet
  have hle := listQSum_member_le_local
    (fun channel =>
      if channel.2 = witness.2 then
        packetPairChannelRawWeight w packet channel
      else 0)
    (fun channel => by
      by_cases hfinal : channel.2 = witness.2
      · simp only [hfinal, if_true]
        exact packetPairChannelRawWeight_nonnegative
          (Q'.le_of_lt hw) packet channel
      · simp only [hfinal, if_false]
        exact Q'.le_refl' 0)
    (pairChannelStateSpace 1)
    (binaryPacketParityChannel_mem packet)
  have hwitness :
      (0 : Q') <
        (if witness.2 = witness.2 then
          packetPairChannelRawWeight w packet witness else 0) := by
    rw [if_pos rfl]
    exact binaryPacketParityChannel_rawWeight_pos hw packet hbinary
  exact Q'.pos_of_lt_of_le hwitness hle

#print axioms binaryPacketParityChannel_mem
#print axioms binaryPacketParityChannel_fusions
#print axioms binaryPacketParityChannel_rawWeight_pos
#print axioms fixedFinalFaceRawWeight_parity_pos

end YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
