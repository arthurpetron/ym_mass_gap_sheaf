/-
# Exact shared-link contraction of a dyadic pair bubble against vacuum

A free cutoff-one pair-bubble face has one extra retained spin-two channel.
This file glues that face to a vacuum neighbour through the literal
degree-two production link factor.  The vacuum face forces its retained
spin to zero, while the production factor is the vacuum fusion projector;
therefore the bubble's spin-two channel is annihilated.  The resulting
two-face raw boundary tensor agrees pointwise, and hence after the complete
finite retained-spin sum, with the two-vacuum tensor.

This is the smallest exact production gluing that detects the closed bubble.
It is not yet a whole-slab theorem: the remaining obligation is to expose
such a vacuum-adjacent production link in the actual geometric carrier and
transport this local equality through the rest of the boundary tensor.

Constructive contract: finite SU(2) fusion data and exact rational algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
import YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel

namespace YMGap.Continuum.Z4DyadicPairBubbleSharedLinkContraction

set_option autoImplicit false
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_eqv_zero_of_left {a b : Q'} (ha : a ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (0 * b) _
    (Q'.mul_eqv_congr_right _ _ b ha) (Q'.zero_mul_eqv b)

private theorem mul_eqv_zero_of_right {a b : Q'} (hb : b ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (a * 0) _
    (Q'.mul_eqv_congr_left a _ _ hb) (Q'.mul_zero_eqv a)

private theorem listQSum_zero_local {A : Type} {value : A → Q'}
    (hvalue : ∀ item, value item ≈ 0) :
    ∀ items : List A, listQSum value items ≈ 0
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      change value head + listQSum value tail ≈ 0
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (hvalue head) (listQSum_zero_local hvalue tail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

/-! ## 1. Fixed-final face and production-link tensors -/

/-- A retained final spin embedded in the coarse slot read by the production
link resolver.  The two internal pair-channel slots are immaterial there. -/
def coarseFinalChannel (finalSpin : Nat) : PairChannelState :=
  ((0, 0), finalSpin)

/-- The literal cutoff-one production link factor, expressed only in terms of
the retained final spins on its two incident faces. -/
def fixedFinalTwoFaceProductionLinkFactor
    (leftFinal rightFinal : Nat) : Q' :=
  twoFaceProductionLinkFactor 1
    (coarseFinalChannel leftFinal) (coarseFinalChannel rightFinal)

theorem fixedFinalTwoFaceProductionLinkFactor_eq_fusionInd
    (leftFinal rightFinal : Nat) :
    fixedFinalTwoFaceProductionLinkFactor leftFinal rightFinal ≈
      fusionInd leftFinal rightFinal 0 := by
  exact twoFaceProductionLinkFactor_eq_fusionInd 1
    (coarseFinalChannel leftFinal) (coarseFinalChannel rightFinal)

/-- Raw two-face tensor after marginalizing each face's internal pair channels
but before summing the two retained final spins. -/
def fixedFinalTwoFaceRawWeight
    (w : Q') (leftPacket rightPacket : FaceSpinPacket)
    (leftFinal rightFinal : Nat) : Q' :=
  (fixedFinalFaceRawWeight w leftPacket leftFinal *
      fixedFinalFaceRawWeight w rightPacket rightFinal) *
    fixedFinalTwoFaceProductionLinkFactor leftFinal rightFinal

/-- The vacuum packet has no fixed-final raw mass away from retained spin
zero. -/
theorem vacuumPacket_fixedFinalRawWeight_eqv_zero_of_ne
    (w : Q') (finalSpin : Nat) (hfinal : finalSpin ≠ 0) :
    fixedFinalFaceRawWeight w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket) finalSpin ≈ 0 := by
  unfold fixedFinalFaceRawWeight
  apply listQSum_zero_local
  intro channel
  by_cases hchannel : channel.2 = finalSpin
  · rw [if_pos hchannel]
    apply vacuum_raw_zero_of_coarse_ne_zero
    intro hzero
    exact hfinal (hchannel.symm.trans hzero)
  · rw [if_neg hchannel]
    exact Q'.eqv_refl 0

/-! ## 2. Pointwise annihilation of the opened spin-two channel -/

/-- A pair bubble on the left of a vacuum face gives exactly the same raw
shared-link boundary tensor as two vacuum faces, for every retained target
pair.  The proof separates the two exact mechanisms: a nonzero right target
is killed by the vacuum row, while a nonzero left target against right target
zero is killed by the production fusion projector. -/
theorem pairBubble_vacuum_sharedLinkRawWeight_eqv_vacuum
    (w : Q') (upper : Bool) (leftFinal rightFinal : Nat) :
    fixedFinalTwoFaceRawWeight w
        (pairBubblePacket upper) (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        leftFinal rightFinal ≈
      fixedFinalTwoFaceRawWeight w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        leftFinal rightFinal := by
  unfold fixedFinalTwoFaceRawWeight
  by_cases hright : rightFinal = 0
  · subst rightFinal
    by_cases hleft : leftFinal = 0
    · subst leftFinal
      have hbubble :
          fixedFinalFaceRawWeight w (pairBubblePacket upper) 0 ≈ 1 := by
        cases upper
        · exact lowerPairBubblePacket_fixedFinalZero_eqv_one w
        · exact upperPairBubblePacket_fixedFinalZero_eqv_one w
      have hvacuum :
          fixedFinalFaceRawWeight w
              (⟨0, 0, 0, 0⟩ : FaceSpinPacket) 0 ≈ 1 :=
        vacuumPacket_fixedFinalZero_eqv_one w
      have hleftRows :
          fixedFinalFaceRawWeight w (pairBubblePacket upper) 0 ≈
            fixedFinalFaceRawWeight w
              (⟨0, 0, 0, 0⟩ : FaceSpinPacket) 0 :=
        Q'.eqv_trans _ 1 _ hbubble (Q'.eqv_symm hvacuum)
      exact qmul_congr
        (qmul_congr hleftRows (Q'.eqv_refl _))
        (Q'.eqv_refl _)
    · have hfactor :
          fixedFinalTwoFaceProductionLinkFactor leftFinal 0 ≈ 0 :=
        Q'.eqv_trans _ (fusionInd leftFinal 0 0) _
          (fixedFinalTwoFaceProductionLinkFactor_eq_fusionInd leftFinal 0)
          (Q'.eqv_of_eq
            (fusionInd_zero_diag_ne leftFinal 0 hleft))
      exact Q'.eqv_trans _ 0 _
        (mul_eqv_zero_of_right hfactor)
        (Q'.eqv_symm (mul_eqv_zero_of_right hfactor))
  · have hrightZero :
        fixedFinalFaceRawWeight w
            (⟨0, 0, 0, 0⟩ : FaceSpinPacket) rightFinal ≈ 0 :=
      vacuumPacket_fixedFinalRawWeight_eqv_zero_of_ne
        w rightFinal hright
    have hbubbleRows :
        fixedFinalFaceRawWeight w (pairBubblePacket upper) leftFinal *
            fixedFinalFaceRawWeight w
              (⟨0, 0, 0, 0⟩ : FaceSpinPacket) rightFinal ≈ 0 :=
      mul_eqv_zero_of_right hrightZero
    have hvacuumRows :
        fixedFinalFaceRawWeight w
              (⟨0, 0, 0, 0⟩ : FaceSpinPacket) leftFinal *
            fixedFinalFaceRawWeight w
              (⟨0, 0, 0, 0⟩ : FaceSpinPacket) rightFinal ≈ 0 :=
      mul_eqv_zero_of_right hrightZero
    exact Q'.eqv_trans _ 0 _
      (mul_eqv_zero_of_left hbubbleRows)
      (Q'.eqv_symm (mul_eqv_zero_of_left hvacuumRows))

/-! ## 3. Complete retained-target contraction -/

/-- Complete cutoff-one retained-final mass of the two-face shared-link raw
tensor. -/
def fixedFinalTwoFaceRawMass
    (w : Q') (leftPacket rightPacket : FaceSpinPacket) : Q' :=
  listQSum
    (fun leftFinal =>
      listQSum
        (fixedFinalTwoFaceRawWeight w leftPacket rightPacket leftFinal)
        (List.range 5))
    (List.range 5)

/-- Summing the pointwise identity over the complete retained-spin boxes gives
the exact two-face boundary-tensor contraction. -/
theorem pairBubble_vacuum_sharedLinkRawMass_eqv_vacuum
    (w : Q') (upper : Bool) :
    fixedFinalTwoFaceRawMass w
        (pairBubblePacket upper) (⟨0, 0, 0, 0⟩ : FaceSpinPacket) ≈
      fixedFinalTwoFaceRawMass w
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket)
        (⟨0, 0, 0, 0⟩ : FaceSpinPacket) := by
  unfold fixedFinalTwoFaceRawMass
  apply listQSum_congr_on
  intro leftFinal _
  apply listQSum_congr_on
  intro rightFinal _
  exact pairBubble_vacuum_sharedLinkRawWeight_eqv_vacuum
    w upper leftFinal rightFinal

#print axioms fixedFinalTwoFaceProductionLinkFactor_eq_fusionInd
#print axioms vacuumPacket_fixedFinalRawWeight_eqv_zero_of_ne
#print axioms pairBubble_vacuum_sharedLinkRawWeight_eqv_vacuum
#print axioms pairBubble_vacuum_sharedLinkRawMass_eqv_vacuum

end YMGap.Continuum.Z4DyadicPairBubbleSharedLinkContraction
