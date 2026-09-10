/-
# No pointwise scalar contraction for a dyadic pair bubble

The closed pair bubble has packet `(1,1,0,0)` in its lower transverse layer.
That packet and the vacuum packet both have a positive final-spin-zero raw
channel, but only the pair bubble has a positive final-spin-two raw channel.
Consequently removal of the bubble cannot multiply every fixed coarse target
channel by one target-independent scalar.

This rules out the strongest premise accepted by the generic touched-product
normalization compiler.  The next exact contraction must occur only after a
finite reindexing or summation of the touched target-channel network.  It does
not rule out such an aggregate closed-network identity.

Constructive contract: exact finite SU(2) fusion data and rational order only;
no `Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
trusted external computation, or new axiom.
-/

import YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
import YMGap.Continuum.Z4DyadicClosedPairBubble

namespace YMGap.Continuum.Z4DyadicPairBubbleRawScalarNoGo

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

local infix:50 " ≈ " => Q'.eqv

/-- The fixed final-spin-zero channel used by both packets. -/
def pairBubbleVacuumChannel : PairChannelState := ((0, 0), 0)

/-- A final-spin-two channel supported by the lower pair bubble. -/
def pairBubbleExcitedChannel : PairChannelState := ((2, 0), 2)

theorem vacuumPacket_vacuumChannel_rawWeight_eqv_one (w : Q') :
    packetPairChannelRawWeight w (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        pairBubbleVacuumChannel ≈ 1 := by
  unfold packetPairChannelRawWeight pairBubbleVacuumChannel
  rw [coeffW_zero,
    show fusionInd 0 0 0 = (1 : Q') by decide]
  decide

theorem lowerPairBubblePacket_vacuumChannel_rawWeight_eqv_one (w : Q') :
    packetPairChannelRawWeight w (pairBubblePacket false)
        pairBubbleVacuumChannel ≈ 1 := by
  unfold packetPairChannelRawWeight pairBubblePacket pairBubbleVacuumChannel
  rw [coeffW_zero,
    show fusionInd 1 1 0 = (1 : Q') by decide,
    show fusionInd 0 0 0 = (1 : Q') by decide]
  decide

theorem vacuumPacket_excitedChannel_rawWeight_eqv_zero (w : Q') :
    packetPairChannelRawWeight w (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        pairBubbleExcitedChannel ≈ 0 := by
  unfold packetPairChannelRawWeight pairBubbleExcitedChannel
  rw [show fusionInd 0 0 2 = (0 : Q') by decide]
  exact Q'.eqv_trans _ (coeffW w 2 * 0) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
    (Q'.mul_zero_eqv _)

theorem lowerPairBubblePacket_excitedChannel_rawWeight_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < packetPairChannelRawWeight w (pairBubblePacket false)
      pairBubbleExcitedChannel := by
  unfold packetPairChannelRawWeight pairBubblePacket pairBubbleExcitedChannel
  rw [show fusionInd 1 1 2 = (1 : Q') by decide,
    show fusionInd 0 0 0 = (1 : Q') by decide,
    show fusionInd 2 0 2 = (1 : Q') by decide]
  exact Q'.mul_pos (FusionResidualBound.coeffW_pos hw 2) (by decide)

/-! ## 2. The obstruction survives summation over the internal pair channels -/

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

private theorem q_left_pos_of_mul_pos_local
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum :
      (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos :
      left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem fixedFinalFaceRawWeight_nonnegative_local
    {w : Q'} (hw : (0 : Q') ≤ w)
    (packet : FaceSpinPacket) (finalSpin : Nat) :
    (0 : Q') ≤ fixedFinalFaceRawWeight w packet finalSpin := by
  unfold fixedFinalFaceRawWeight
  apply listQSum_nonnegative_on
  intro channel _
  by_cases hfinal : channel.2 = finalSpin
  · rw [if_pos hfinal]
    exact packetPairChannelRawWeight_nonnegative hw packet channel
  · rw [if_neg hfinal]
    exact Q'.le_refl' 0

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

theorem vacuumPacket_finalZero_rawWeight_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      fixedFinalFaceRawWeight w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket) 0 := by
  simpa [binaryPacketParityChannel] using
    (fixedFinalFaceRawWeight_parity_pos hw
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
      (by
        unfold PacketBinary
        exact ⟨by decide, by decide, by decide, by decide⟩))

private theorem vacuumPacket_rawWeight_eqv_zero_of_finalTwo
    (w : Q') (channel : PairChannelState)
    (hfinal : channel.2 = 2) :
    packetPairChannelRawWeight w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket) channel ≈ 0 := by
  rcases channel with ⟨⟨left, right⟩, finalSpin⟩
  change finalSpin = 2 at hfinal
  subst finalSpin
  unfold packetPairChannelRawWeight
  by_cases hleft : left = 0
  · subst left
    by_cases hright : right = 0
    · subst right
      have hcoarse : fusionInd 0 0 2 = (0 : Q') :=
        YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_left_ne
          0 2 (by decide)
      exact mul_eqv_zero_of_right_local
        (mul_eqv_zero_of_right_local
          (mul_eqv_zero_of_right_local (Q'.eqv_of_eq hcoarse)))
    · have hrightFusion : fusionInd 0 0 right = (0 : Q') :=
        YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_left_ne
          0 right (fun h => hright h.symm)
      exact mul_eqv_zero_of_right_local
        (mul_eqv_zero_of_right_local
          (mul_eqv_zero_of_left_local (Q'.eqv_of_eq hrightFusion)))
  · have hleftFusion : fusionInd 0 0 left = (0 : Q') :=
      YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_left_ne
        0 left (fun h => hleft h.symm)
    exact mul_eqv_zero_of_right_local
      (mul_eqv_zero_of_left_local (Q'.eqv_of_eq hleftFusion))

theorem vacuumPacket_finalTwo_rawWeight_eqv_zero (w : Q') :
    fixedFinalFaceRawWeight w (⟨0, 0, 0, 0⟩ : FaceSpinPacket) 2 ≈ 0 := by
  unfold fixedFinalFaceRawWeight
  exact Q'.eqv_trans _ _ _
    (listQSum_congr_on _ _ (pairChannelStateSpace 1)
      (fun channel _ => by
        by_cases hfinal : channel.2 = 2
        · rw [if_pos hfinal]
          exact vacuumPacket_rawWeight_eqv_zero_of_finalTwo
            w channel hfinal
        · rw [if_neg hfinal]
          exact Q'.eqv_refl 0))
    (listQSum_zero (pairChannelStateSpace 1))

theorem lowerPairBubblePacket_finalTwo_rawWeight_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      fixedFinalFaceRawWeight w (pairBubblePacket false) 2 := by
  have hmem : pairBubbleExcitedChannel ∈ pairChannelStateSpace 1 :=
    (mem_pairChannelStateSpace_iff 1 pairBubbleExcitedChannel).mpr (by decide)
  have hle := listQSum_member_le_local
    (fun channel =>
      if channel.2 = 2 then
        packetPairChannelRawWeight w (pairBubblePacket false) channel
      else 0)
    (fun channel => by
      by_cases hfinal : channel.2 = 2
      · change (0 : Q') ≤
          if channel.2 = 2 then
            packetPairChannelRawWeight w (pairBubblePacket false) channel
          else 0
        rw [if_pos hfinal]
        exact packetPairChannelRawWeight_nonnegative
          (Q'.le_of_lt hw) (pairBubblePacket false) channel
      · change (0 : Q') ≤
          if channel.2 = 2 then
            packetPairChannelRawWeight w (pairBubblePacket false) channel
          else 0
        rw [if_neg hfinal]
        exact Q'.le_refl' 0)
    (pairChannelStateSpace 1) hmem
  have hwitness :
      (0 : Q') <
        (if pairBubbleExcitedChannel.2 = 2 then
          packetPairChannelRawWeight w (pairBubblePacket false)
            pairBubbleExcitedChannel else 0) := by
    rw [if_pos (by decide)]
    exact lowerPairBubblePacket_excitedChannel_rawWeight_pos hw
  exact Q'.pos_of_lt_of_le hwitness hle

/-- There is no target-independent scalar which turns the lower pair-bubble
packet's raw channel row into the vacuum packet's raw channel row. -/
theorem no_targetIndependentScalar_for_lowerPairBubble
    {w scalar : Q'} (hw : (0 : Q') < w)
    (hscalar : ∀ channel : PairChannelState,
      packetPairChannelRawWeight w (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
          channel ≈
        scalar * packetPairChannelRawWeight w (pairBubblePacket false)
          channel) : False := by
  have hscalarOne : (1 : Q') ≈ scalar := by
    refine Q'.eqv_trans _
      (packetPairChannelRawWeight w (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        pairBubbleVacuumChannel) _
      (Q'.eqv_symm (vacuumPacket_vacuumChannel_rawWeight_eqv_one w)) ?_
    refine Q'.eqv_trans _
      (scalar * packetPairChannelRawWeight w (pairBubblePacket false)
        pairBubbleVacuumChannel) _
      (hscalar pairBubbleVacuumChannel) ?_
    refine Q'.eqv_trans _ (scalar * 1) _
      (Q'.mul_eqv_congr_left scalar _ _
        (lowerPairBubblePacket_vacuumChannel_rawWeight_eqv_one w)) ?_
    exact Q'.mul_one_eqv scalar
  have hscalarPositive : (0 : Q') < scalar :=
    Q'.pos_of_lt_of_le (by decide) (Q'.le_of_eqv hscalarOne)
  have hproductPositive :
      (0 : Q') < scalar *
        packetPairChannelRawWeight w (pairBubblePacket false)
          pairBubbleExcitedChannel :=
    Q'.mul_pos hscalarPositive
      (lowerPairBubblePacket_excitedChannel_rawWeight_pos hw)
  have hproductZero :
      scalar * packetPairChannelRawWeight w (pairBubblePacket false)
          pairBubbleExcitedChannel ≈ 0 :=
    Q'.eqv_trans _
      (packetPairChannelRawWeight w (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        pairBubbleExcitedChannel) _
      (Q'.eqv_symm (hscalar pairBubbleExcitedChannel))
      (vacuumPacket_excitedChannel_rawWeight_eqv_zero w)
  exact Int.not_lt_of_ge (Q'.le_of_eqv hproductZero) hproductPositive

/-- Even after both internal pair channels are summed, the fixed-final-spin
face weights of a pair bubble and the vacuum are not pointwise proportional
in the retained coarse spin.  This is the direct no-go for a facewise scalar
premise in the touched-product compiler. -/
theorem no_targetIndependentScalar_for_lowerPairBubble_finalWeights
    {w scalar : Q'} (hw : (0 : Q') < w)
    (hscalar : ∀ finalSpin : Nat,
      fixedFinalFaceRawWeight w (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
          finalSpin ≈
        scalar * fixedFinalFaceRawWeight w (pairBubblePacket false)
          finalSpin) : False := by
  have hproductZeroPositive :
      (0 : Q') <
        scalar * fixedFinalFaceRawWeight w (pairBubblePacket false) 0 :=
    Q'.pos_of_lt_of_le
      (vacuumPacket_finalZero_rawWeight_pos hw)
      (Q'.le_of_eqv (hscalar 0))
  have hscalarPositive : (0 : Q') < scalar :=
    q_left_pos_of_mul_pos_local
      (fixedFinalFaceRawWeight_nonnegative_local
        (Q'.le_of_lt hw) (pairBubblePacket false) 0)
      hproductZeroPositive
  have hsourcePositive :
      (0 : Q') < fixedFinalFaceRawWeight w (pairBubblePacket false) 2 :=
    lowerPairBubblePacket_finalTwo_rawWeight_pos hw
  have hproductPositive :
      (0 : Q') < scalar *
        fixedFinalFaceRawWeight w (pairBubblePacket false) 2 :=
    Q'.mul_pos hscalarPositive hsourcePositive
  have hproductZero :
      scalar * fixedFinalFaceRawWeight w (pairBubblePacket false) 2 ≈ 0 :=
    Q'.eqv_trans _
      (fixedFinalFaceRawWeight w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket) 2) _
      (Q'.eqv_symm (hscalar 2))
      (vacuumPacket_finalTwo_rawWeight_eqv_zero w)
  exact Int.not_lt_of_ge (Q'.le_of_eqv hproductZero) hproductPositive

#print axioms vacuumPacket_vacuumChannel_rawWeight_eqv_one
#print axioms lowerPairBubblePacket_vacuumChannel_rawWeight_eqv_one
#print axioms vacuumPacket_excitedChannel_rawWeight_eqv_zero
#print axioms lowerPairBubblePacket_excitedChannel_rawWeight_pos
#print axioms no_targetIndependentScalar_for_lowerPairBubble
#print axioms vacuumPacket_finalZero_rawWeight_pos
#print axioms vacuumPacket_finalTwo_rawWeight_eqv_zero
#print axioms lowerPairBubblePacket_finalTwo_rawWeight_pos
#print axioms no_targetIndependentScalar_for_lowerPairBubble_finalWeights

end YMGap.Continuum.Z4DyadicPairBubbleRawScalarNoGo
