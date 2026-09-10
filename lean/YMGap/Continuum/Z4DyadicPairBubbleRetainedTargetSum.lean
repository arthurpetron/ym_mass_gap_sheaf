/-
# Exact retained-target sum of a dyadic pair bubble

The pointwise scalar route fails because a pair bubble opens a retained
spin-two channel absent from the vacuum packet.  This file performs the next
legitimate contraction: sum that retained coarse-face label freely.

At fine cutoff one the vacuum packet has total retained-target mass one.  A
lower or upper closed pair bubble has exactly two supported channels, of
weights one and `coeffW w 2`, so its total retained-target mass is
`1 + coeffW w 2`.

This is the exact local bubble scalar after the retained face label has been
contracted.  It is not yet a whole-slab identity: the production coarse-link
multiplicity couples retained labels on incident faces.  The remaining local
network is therefore precisely the link-glued boundary tensor.

Constructive contract: finite SU(2) fusion data and exact rational algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicPairBubbleRawScalarNoGo

namespace YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum

set_option autoImplicit false
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicPairBubbleRawScalarNoGo
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

local infix:50 " ≈ " => Q'.eqv

/-- Sum over the complete cutoff-one retained-spin range `0,...,4`. -/
def cutoffOneRetainedTargetMass
    (w : Q') (packet : FaceSpinPacket) : Q' :=
  listQSum (fixedFinalFaceRawWeight w packet) (List.range 5)

/-! ## 1. Finite Fubini: a complete retained range forgets the target pin -/

private theorem rangeNodupLocal (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = k := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl k)

private theorem listQSum_ite_single_local
    {A : Type} [DecidableEq A] (selected : A) (value : A → Q') :
    ∀ items : List A,
      items.Nodup → selected ∈ items →
      listQSum
          (fun item => if selected = item then value item else 0)
          items ≈
        value selected
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum
                (fun item => if selected = item then value item else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _item => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro item hitem
            rw [if_neg]
            exact Q'.eqv_refl 0
            intro heq
            exact hparts.1 (heq ▸ hitem)
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : selected ≠ head := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left _ _ _
            (listQSum_ite_single_local selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem listQSum_completeTargets_local
    {Source Target : Type} [DecidableEq Target]
    (targetOf : Source → Target) (value : Source → Q')
    (sources : List Source) (targets : List Target)
    (htargetsNodup : targets.Nodup)
    (hcomplete : ∀ source, source ∈ sources → targetOf source ∈ targets) :
    listQSum
        (fun retained =>
          listQSum
            (fun source =>
              if targetOf source = retained then value source else 0)
            sources)
        targets ≈
      listQSum value sources := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun retained =>
            if targetOf source = retained then value source else 0)
          targets)
      sources) _
    (listQSum_swap
      (fun source retained =>
        if targetOf source = retained then value source else 0)
      sources targets) ?_
  exact listQSum_congr_on _ _ sources
    (fun source hsource =>
      listQSum_ite_single_local (targetOf source)
        (fun _ => value source) targets htargetsNodup
        (hcomplete source hsource))

/-- Summing every possible cutoff-one retained spin turns the pinned-target
face weight back into the unpinned pair-channel partition. -/
theorem cutoffOneRetainedTargetMass_eqv_pairChannelPartition
    (w : Q') (packet : FaceSpinPacket) :
    cutoffOneRetainedTargetMass w packet ≈
      packetPairChannelPartition w 1 packet := by
  unfold cutoffOneRetainedTargetMass fixedFinalFaceRawWeight
    packetPairChannelPartition
  apply listQSum_completeTargets_local
    (fun channel : PairChannelState => channel.2)
    (packetPairChannelRawWeight w packet)
    (pairChannelStateSpace 1) (List.range 5) (rangeNodupLocal 5)
  intro channel hchannel
  have hbounds := (mem_pairChannelStateSpace_iff 1 channel).mp hchannel
  exact List.mem_range.mpr (by omega)

/-! ## 2. Exact support classification of the three packets -/

/-- Boolean presentation of the three literal SU(2) fusion guards. -/
def packetPairChannelSupportedBool
    (packet : FaceSpinPacket) (state : PairChannelState) : Bool :=
  fusionOK packet.spin0 packet.spin1 state.1.1 &&
    fusionOK packet.spin2 packet.spin3 state.1.2 &&
      fusionOK state.1.1 state.1.2 state.2

/-- The excited channel for a bubble in the upper transverse pair. -/
def pairBubbleUpperExcitedChannel : PairChannelState := ((0, 2), 2)

theorem vacuumPacket_supportedChannels :
    (pairChannelStateSpace 1).filter
        (packetPairChannelSupportedBool
          (⟨0, 0, 0, 0⟩ : FaceSpinPacket)) =
      [pairBubbleVacuumChannel] := by
  decide

theorem lowerPairBubblePacket_supportedChannels :
    (pairChannelStateSpace 1).filter
        (packetPairChannelSupportedBool (pairBubblePacket false)) =
      [pairBubbleVacuumChannel, pairBubbleExcitedChannel] := by
  decide

theorem upperPairBubblePacket_supportedChannels :
    (pairChannelStateSpace 1).filter
        (packetPairChannelSupportedBool (pairBubblePacket true)) =
      [pairBubbleVacuumChannel, pairBubbleUpperExcitedChannel] := by
  decide

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

private theorem packetPairChannelRawWeight_eqv_zero_of_support_false
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

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source → test item = false →
        value item ≈ 0) →
      listQSum value source ≈
        listQSum value (source.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false →
            value item ≈ 0 := by
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

theorem upperPairBubblePacket_vacuumChannel_rawWeight_eqv_one (w : Q') :
    packetPairChannelRawWeight w (pairBubblePacket true)
        pairBubbleVacuumChannel ≈ 1 := by
  unfold packetPairChannelRawWeight pairBubblePacket pairBubbleVacuumChannel
  rw [coeffW_zero,
    show fusionInd 0 0 0 = (1 : Q') by decide,
    show fusionInd 1 1 0 = (1 : Q') by decide]
  decide

theorem lowerPairBubblePacket_excitedChannel_rawWeight_eqv_coeffW
    (w : Q') :
    packetPairChannelRawWeight w (pairBubblePacket false)
        pairBubbleExcitedChannel ≈ coeffW w 2 := by
  unfold packetPairChannelRawWeight pairBubblePacket pairBubbleExcitedChannel
  rw [show fusionInd 1 1 2 = (1 : Q') by decide,
    show fusionInd 0 0 0 = (1 : Q') by decide,
    show fusionInd 2 0 2 = (1 : Q') by decide]
  exact Q'.eqv_trans _ (coeffW w 2 * 1) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ (1 * 1) _
        (Q'.one_mul_eqv (1 * 1)) (Q'.one_mul_eqv 1)))
    (Q'.mul_one_eqv (coeffW w 2))

theorem upperPairBubblePacket_excitedChannel_rawWeight_eqv_coeffW
    (w : Q') :
    packetPairChannelRawWeight w (pairBubblePacket true)
        pairBubbleUpperExcitedChannel ≈ coeffW w 2 := by
  unfold packetPairChannelRawWeight pairBubblePacket
    pairBubbleUpperExcitedChannel
  rw [show fusionInd 0 0 0 = (1 : Q') by decide,
    show fusionInd 1 1 2 = (1 : Q') by decide,
    show fusionInd 0 2 2 = (1 : Q') by decide]
  exact Q'.eqv_trans _ (coeffW w 2 * 1) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ (1 * 1) _
        (Q'.one_mul_eqv (1 * 1)) (Q'.one_mul_eqv 1)))
    (Q'.mul_one_eqv (coeffW w 2))

private theorem fixedFinalZero_eqv_supportedSum
    (w : Q') (packet : FaceSpinPacket) :
    fixedFinalFaceRawWeight w packet 0 ≈
      listQSum
        (fun state =>
          if state.2 = 0 then
            packetPairChannelRawWeight w packet state
          else 0)
        ((pairChannelStateSpace 1).filter
          (packetPairChannelSupportedBool packet)) := by
  unfold fixedFinalFaceRawWeight
  apply listQSum_eq_filter_of_zero_local
  intro state _ hsupport
  by_cases hfinal : state.2 = 0
  · rw [if_pos hfinal]
    exact packetPairChannelRawWeight_eqv_zero_of_support_false
      w packet state hsupport
  · rw [if_neg hfinal]
    exact Q'.eqv_refl 0

theorem vacuumPacket_fixedFinalZero_eqv_one (w : Q') :
    fixedFinalFaceRawWeight w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket) 0 ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (fixedFinalZero_eqv_supportedSum w
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket)) ?_
  rw [vacuumPacket_supportedChannels]
  simp only [listQSum]
  rw [if_pos (by decide : pairBubbleVacuumChannel.2 = 0)]
  exact Q'.eqv_trans _ (1 + 0) _
    (Q'.add_eqv_congr'
      (vacuumPacket_vacuumChannel_rawWeight_eqv_one w)
      (Q'.eqv_refl 0))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

theorem lowerPairBubblePacket_fixedFinalZero_eqv_one (w : Q') :
    fixedFinalFaceRawWeight w (pairBubblePacket false) 0 ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (fixedFinalZero_eqv_supportedSum w (pairBubblePacket false)) ?_
  rw [lowerPairBubblePacket_supportedChannels]
  simp only [listQSum]
  rw [if_pos (by decide : pairBubbleVacuumChannel.2 = 0),
    if_neg (by decide : pairBubbleExcitedChannel.2 ≠ 0)]
  exact Q'.eqv_trans _ (1 + (0 + 0)) _
    (Q'.add_eqv_congr'
      (lowerPairBubblePacket_vacuumChannel_rawWeight_eqv_one w)
      (Q'.eqv_refl (0 + 0)))
    (by decide)

theorem upperPairBubblePacket_fixedFinalZero_eqv_one (w : Q') :
    fixedFinalFaceRawWeight w (pairBubblePacket true) 0 ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (fixedFinalZero_eqv_supportedSum w (pairBubblePacket true)) ?_
  rw [upperPairBubblePacket_supportedChannels]
  simp only [listQSum]
  rw [if_pos (by decide : pairBubbleVacuumChannel.2 = 0),
    if_neg (by decide : pairBubbleUpperExcitedChannel.2 ≠ 0)]
  exact Q'.eqv_trans _ (1 + (0 + 0)) _
    (Q'.add_eqv_congr'
      (upperPairBubblePacket_vacuumChannel_rawWeight_eqv_one w)
      (Q'.eqv_refl (0 + 0)))
    (by decide)

/-! ## 3. The exact free-face bubble scalar -/

theorem vacuumPacket_pairChannelPartition_eqv_one (w : Q') :
    packetPairChannelPartition w 1
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket) ≈ 1 := by
  unfold packetPairChannelPartition
  refine Q'.eqv_trans _
    (listQSum
      (packetPairChannelRawWeight w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket))
      ((pairChannelStateSpace 1).filter
        (packetPairChannelSupportedBool
          (⟨0, 0, 0, 0⟩ : FaceSpinPacket)))) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero_local
    intro state _ hsupport
    exact packetPairChannelRawWeight_eqv_zero_of_support_false
      w (⟨0, 0, 0, 0⟩ : FaceSpinPacket) state hsupport
  · rw [vacuumPacket_supportedChannels]
    simp only [listQSum]
    exact Q'.eqv_trans _ (1 + 0) _
      (Q'.add_eqv_congr'
        (vacuumPacket_vacuumChannel_rawWeight_eqv_one w)
        (Q'.eqv_refl 0))
      (Q'.eqv_of_eq (Q'.add_zero' 1))

theorem pairBubblePacket_pairChannelPartition_eqv
    (w : Q') (upper : Bool) :
    packetPairChannelPartition w 1 (pairBubblePacket upper) ≈
      1 + coeffW w 2 := by
  cases upper with
  | false =>
      unfold packetPairChannelPartition
      refine Q'.eqv_trans _
        (listQSum
          (packetPairChannelRawWeight w (pairBubblePacket false))
          ((pairChannelStateSpace 1).filter
            (packetPairChannelSupportedBool (pairBubblePacket false)))) _ ?_ ?_
      · apply listQSum_eq_filter_of_zero_local
        intro state _ hsupport
        exact packetPairChannelRawWeight_eqv_zero_of_support_false
          w (pairBubblePacket false) state hsupport
      · rw [lowerPairBubblePacket_supportedChannels]
        simp only [listQSum]
        exact Q'.eqv_trans _ (1 + (coeffW w 2 + 0)) _
          (Q'.add_eqv_congr'
            (lowerPairBubblePacket_vacuumChannel_rawWeight_eqv_one w)
            (Q'.add_eqv_congr'
              (lowerPairBubblePacket_excitedChannel_rawWeight_eqv_coeffW w)
              (Q'.eqv_refl 0)))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_of_eq (Q'.add_zero' (coeffW w 2))))
  | true =>
      unfold packetPairChannelPartition
      refine Q'.eqv_trans _
        (listQSum
          (packetPairChannelRawWeight w (pairBubblePacket true))
          ((pairChannelStateSpace 1).filter
            (packetPairChannelSupportedBool (pairBubblePacket true)))) _ ?_ ?_
      · apply listQSum_eq_filter_of_zero_local
        intro state _ hsupport
        exact packetPairChannelRawWeight_eqv_zero_of_support_false
          w (pairBubblePacket true) state hsupport
      · rw [upperPairBubblePacket_supportedChannels]
        simp only [listQSum]
        exact Q'.eqv_trans _ (1 + (coeffW w 2 + 0)) _
          (Q'.add_eqv_congr'
            (upperPairBubblePacket_vacuumChannel_rawWeight_eqv_one w)
            (Q'.add_eqv_congr'
              (upperPairBubblePacket_excitedChannel_rawWeight_eqv_coeffW w)
              (Q'.eqv_refl 0)))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_of_eq (Q'.add_zero' (coeffW w 2))))

theorem vacuumPacket_retainedTargetMass_eqv_one (w : Q') :
    cutoffOneRetainedTargetMass w
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (cutoffOneRetainedTargetMass_eqv_pairChannelPartition w
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket))
    (vacuumPacket_pairChannelPartition_eqv_one w)

theorem pairBubblePacket_retainedTargetMass_eqv
    (w : Q') (upper : Bool) :
    cutoffOneRetainedTargetMass w (pairBubblePacket upper) ≈
      1 + coeffW w 2 :=
  Q'.eqv_trans _ _ _
    (cutoffOneRetainedTargetMass_eqv_pairChannelPartition w
      (pairBubblePacket upper))
    (pairBubblePacket_pairChannelPartition_eqv w upper)

#print axioms cutoffOneRetainedTargetMass_eqv_pairChannelPartition
#print axioms vacuumPacket_supportedChannels
#print axioms lowerPairBubblePacket_supportedChannels
#print axioms upperPairBubblePacket_supportedChannels
#print axioms upperPairBubblePacket_vacuumChannel_rawWeight_eqv_one
#print axioms lowerPairBubblePacket_excitedChannel_rawWeight_eqv_coeffW
#print axioms upperPairBubblePacket_excitedChannel_rawWeight_eqv_coeffW
#print axioms vacuumPacket_fixedFinalZero_eqv_one
#print axioms lowerPairBubblePacket_fixedFinalZero_eqv_one
#print axioms upperPairBubblePacket_fixedFinalZero_eqv_one
#print axioms vacuumPacket_pairChannelPartition_eqv_one
#print axioms pairBubblePacket_pairChannelPartition_eqv
#print axioms vacuumPacket_retainedTargetMass_eqv_one
#print axioms pairBubblePacket_retainedTargetMass_eqv

end YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
