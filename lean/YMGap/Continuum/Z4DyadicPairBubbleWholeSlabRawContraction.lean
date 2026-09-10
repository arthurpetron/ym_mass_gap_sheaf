/-
# Whole-slab raw contraction from an isolated pair-bubble packet profile

The free-face pair-bubble scalar is not pointwise in the retained coarse
label.  The production link network nevertheless removes the extra channel
when the bubble is isolated: every off-target source packet is vacuum, so a
nonzero off-target coarse label kills its face factor; if all off-target
labels vanish, a nonzero target label is killed by the canonical incident
production link.  At target label zero, the bubble and vacuum face rows both
have exact mass one.

This file packages that exhaustive finite case split.  Its input is an
explicit whole-slab packet profile saying that one coarse face has a lower or
upper pair-bubble packet and every other coarse face has the vacuum packet.
Its output is pointwise equality of the complete globally link-glued raw row
with the vacuum fine-source row, for every bounded coarse physical target.

The next geometric step is to instantiate the packet profile from the
literal dyadic pair-bubble fine support (subject to its fine-slab containment).
No arbitrary-background component cancellation is claimed here.

Constructive contract: finite case analysis, exact rational algebra, and
finite SU(2) fusion data only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicPairBubbleSharedLinkContraction
import YMGap.Continuum.Z4WholeSlabFaceFirstLinkIsolation
import YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel

namespace YMGap.Continuum.Z4DyadicPairBubbleWholeSlabRawContraction

set_option autoImplicit false
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
open YMGap.Continuum.Z4DyadicPairBubbleSharedLinkContraction
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4WholeSlabFaceFirstLinkIsolation

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
      exact qmul_congr
        (hagree head List.mem_cons_self)
        (wholeSlabFiniteQProduct_congr_on_local left right tail
          (fun item hmem =>
            hagree item (List.mem_cons_of_mem head hmem)))

private theorem wholeSlabFiniteQProduct_eqv_zero_of_member_local {A : Type}
    (value : A → Q') : ∀ (items : List A) {item : A},
    item ∈ items → value item ≈ 0 →
      wholeSlabFiniteQProduct value items ≈ 0
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem, hzero => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst head
        exact mul_eqv_zero_of_left hzero
      · exact mul_eqv_zero_of_right
          (wholeSlabFiniteQProduct_eqv_zero_of_member_local
            value tail htail hzero)

private theorem finite_all_or_exists_not_local
    {A : Type} (predicate : A → Prop) [DecidablePred predicate] :
    ∀ items : List A,
      (∀ item, item ∈ items → predicate item) ∨
        ∃ item, item ∈ items ∧ ¬ predicate item
  | [] => Or.inl (fun item hmem => False.elim (List.not_mem_nil hmem))
  | head :: tail => by
      by_cases hhead : predicate head
      · rcases finite_all_or_exists_not_local predicate tail with
          htail | ⟨item, hmem, hnot⟩
        · exact Or.inl (fun item hmem => by
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact hhead
            · exact htail item hmem)
        · exact Or.inr ⟨item, List.mem_cons_of_mem head hmem, hnot⟩
      · exact Or.inr ⟨head, List.mem_cons_self, hhead⟩

/-! ## 1. Exact packet-profile interface -/

/-- One whole-slab fine source has precisely one pair-bubble coarse fibre and
vacuum packets on every other physical coarse face. -/
structure IsolatedPairBubbleWholeSlabPacketProfile
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (targetFaceId : Nat) (upper : Bool) : Prop where
  target_mem : targetFaceId ∈ S.coarse.faceEdges
  packet_eq : ∀ faceId, faceId ∈ S.coarse.faceEdges →
    wholeSlabFinePacket S fineState faceId =
      if faceId = targetFaceId then
        pairBubblePacket upper
      else (⟨0, 0, 0, 0⟩ : FaceSpinPacket)

theorem wholeSlabFinePacket_zero
    (S : SlabScalePair) (faceId : Nat) :
    wholeSlabFinePacket S zeroEdgeLabelling faceId =
      (⟨0, 0, 0, 0⟩ : FaceSpinPacket) := by
  unfold wholeSlabFinePacket dyadicFaceSpinPacket slabSpinAtPlaquette
    zeroEdgeLabelling
  simp

/-- The whole-slab face row is the already evaluated cutoff-one fixed-final
row once its local packet is identified. -/
theorem wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling)
    (faceId : Nat) (packet : FaceSpinPacket)
    (hfineCutoff : S.fine.cutoff = 1)
    (hpacket : wholeSlabFinePacket S fineState faceId = packet) :
    wholeSlabFaceRawWeight S fineState coarseState faceId ≈
      fixedFinalFaceRawWeight S.coarse.coupling packet
        (coarseState faceId) := by
  unfold wholeSlabFaceRawWeight fixedFinalFaceRawWeight
  rw [hpacket, hfineCutoff]
  exact Q'.eqv_refl _

private theorem wholeSlabFaceRawProduct_eqv_of_facewise
    (S : SlabScalePair)
    (leftFine rightFine coarseState : EdgeLabelling)
    (hagrees : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      wholeSlabFaceRawWeight S leftFine coarseState faceId ≈
        wholeSlabFaceRawWeight S rightFine coarseState faceId) :
    wholeSlabFaceRawProduct S leftFine coarseState ≈
      wholeSlabFaceRawProduct S rightFine coarseState := by
  exact Q'.eqv_trans _ _ _
    (wholeSlabFaceRawProduct_eqv_finiteQProduct
      S leftFine coarseState)
    (Q'.eqv_trans _ _ _
      (wholeSlabFiniteQProduct_congr_on_local _ _
        S.coarse.faceEdges hagrees)
      (Q'.eqv_symm
        (wholeSlabFaceRawProduct_eqv_finiteQProduct
          S rightFine coarseState)))

private theorem wholeSlabFaceRawProduct_eqv_zero_of_face
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges)
    (hzero : wholeSlabFaceRawWeight S fineState coarseState faceId ≈ 0) :
    wholeSlabFaceRawProduct S fineState coarseState ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (wholeSlabFaceRawProduct_eqv_finiteQProduct
      S fineState coarseState)
    (wholeSlabFiniteQProduct_eqv_zero_of_member_local
      (wholeSlabFaceRawWeight S fineState coarseState)
      S.coarse.faceEdges hface hzero)

/-! ## 2. Exhaustive whole-slab contraction -/

/-- An isolated pair-bubble packet profile gives the same complete globally
link-glued raw row as the vacuum fine source, pointwise on every bounded
coarse physical target. -/
theorem wholeSlabRecouplingRawWeight_isolatedPairBubble_eqv_vacuum
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling)
    (targetFaceId : Nat) (upper : Bool)
    (hfineCutoff : S.fine.cutoff = 1)
    (hprofile : IsolatedPairBubbleWholeSlabPacketProfile
      S fineState targetFaceId upper)
    (hcoarseBounded : SlabFaceLabellingBounded
      S.coarse.cutoff S.coarse.extent coarseState) :
    wholeSlabRecouplingRawWeight S fineState coarseState ≈
      wholeSlabRecouplingRawWeight S zeroEdgeLabelling coarseState := by
  by_cases htargetZero : coarseState targetFaceId = 0
  · have hfaceProduct :
        wholeSlabFaceRawProduct S fineState coarseState ≈
          wholeSlabFaceRawProduct S zeroEdgeLabelling coarseState := by
      apply wholeSlabFaceRawProduct_eqv_of_facewise
      intro faceId hface
      by_cases htarget : faceId = targetFaceId
      · subst faceId
        have hpacket := hprofile.packet_eq targetFaceId hprofile.target_mem
        rw [if_pos rfl] at hpacket
        have hbubble :
            wholeSlabFaceRawWeight S fineState coarseState targetFaceId ≈
              1 := by
          refine Q'.eqv_trans _ _ _
            (wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
              S fineState coarseState targetFaceId
              (pairBubblePacket upper) hfineCutoff hpacket) ?_
          rw [htargetZero]
          cases upper
          · exact lowerPairBubblePacket_fixedFinalZero_eqv_one
              S.coarse.coupling
          · exact upperPairBubblePacket_fixedFinalZero_eqv_one
              S.coarse.coupling
        have hvacuum :
            wholeSlabFaceRawWeight S zeroEdgeLabelling coarseState
                targetFaceId ≈ 1 := by
          refine Q'.eqv_trans _ _ _
            (wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
              S zeroEdgeLabelling coarseState targetFaceId
              (⟨0, 0, 0, 0⟩ : FaceSpinPacket) hfineCutoff
              (wholeSlabFinePacket_zero S targetFaceId)) ?_
          rw [htargetZero]
          exact vacuumPacket_fixedFinalZero_eqv_one S.coarse.coupling
        exact Q'.eqv_trans _ 1 _ hbubble (Q'.eqv_symm hvacuum)
      · have hpacket := hprofile.packet_eq faceId hface
        rw [if_neg htarget] at hpacket
        unfold wholeSlabFaceRawWeight
        rw [hpacket, wholeSlabFinePacket_zero]
        exact Q'.eqv_refl _
    unfold wholeSlabRecouplingRawWeight
    exact Q'.mul_eqv_congr_right _ _ _ hfaceProduct
  · have hvacuumFaceZero :
        wholeSlabFaceRawWeight S zeroEdgeLabelling coarseState
            targetFaceId ≈ 0 := by
      refine Q'.eqv_trans _ _ _
        (wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
          S zeroEdgeLabelling coarseState targetFaceId
          (⟨0, 0, 0, 0⟩ : FaceSpinPacket) hfineCutoff
          (wholeSlabFinePacket_zero S targetFaceId)) ?_
      exact vacuumPacket_fixedFinalRawWeight_eqv_zero_of_ne
        S.coarse.coupling (coarseState targetFaceId) htargetZero
    have hvacuumProductZero :
        wholeSlabFaceRawProduct S zeroEdgeLabelling coarseState ≈ 0 :=
      wholeSlabFaceRawProduct_eqv_zero_of_face
        S zeroEdgeLabelling coarseState targetFaceId
        hprofile.target_mem hvacuumFaceZero
    have hvacuumRawZero :
        wholeSlabRecouplingRawWeight S zeroEdgeLabelling coarseState ≈ 0 := by
      unfold wholeSlabRecouplingRawWeight
      exact mul_eqv_zero_of_left hvacuumProductZero
    rcases finite_all_or_exists_not_local
        (fun faceId =>
          faceId = targetFaceId ∨ coarseState faceId = 0)
        S.coarse.faceEdges with hisolated | ⟨other, hotherMem, hotherNot⟩
    · have htargetPhysical :
          targetFaceId ∈ slabPhysicalFaceEdges S.coarse.extent := by
        simpa only [SlabPhysicalData.faceEdges] using hprofile.target_mem
      have htargetBound :
          coarseState targetFaceId ≤ linkAuxiliaryCutoff S.coarse.cutoff := by
        have hbound := hcoarseBounded targetFaceId htargetPhysical
        unfold linkAuxiliaryCutoff linkIncidenceBound
        omega
      have hlinkProductZero :
          slabExplicitLinkMultiplicityProduct
              S.coarse.cutoff S.coarse.extent coarseState = 0 := by
        apply
          slabExplicitLinkMultiplicityProduct_eq_zero_of_globally_isolated_face
            S.coarse.cutoff S.coarse.extent coarseState targetFaceId
            htargetPhysical htargetZero htargetBound
        intro faceId hfacePhysical hne
        have hface : faceId ∈ S.coarse.faceEdges := by
          simpa only [SlabPhysicalData.faceEdges] using hfacePhysical
        rcases hisolated faceId hface with heq | hzero
        · exact False.elim (hne heq)
        · exact hzero
      have hbubbleRawZero :
          wholeSlabRecouplingRawWeight S fineState coarseState ≈ 0 := by
        unfold wholeSlabRecouplingRawWeight
        rw [hlinkProductZero]
        exact mul_eqv_zero_of_right Q'.ofNat_zero_eqv
      exact Q'.eqv_trans _ 0 _ hbubbleRawZero
        (Q'.eqv_symm hvacuumRawZero)
    · have hotherNe : other ≠ targetFaceId := by
        intro heq
        exact hotherNot (Or.inl heq)
      have hotherNonzero : coarseState other ≠ 0 := by
        intro hzero
        exact hotherNot (Or.inr hzero)
      have hpacket := hprofile.packet_eq other hotherMem
      rw [if_neg hotherNe] at hpacket
      have hbubbleFaceZero :
          wholeSlabFaceRawWeight S fineState coarseState other ≈ 0 := by
        refine Q'.eqv_trans _ _ _
          (wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
            S fineState coarseState other
            (⟨0, 0, 0, 0⟩ : FaceSpinPacket) hfineCutoff hpacket) ?_
        exact vacuumPacket_fixedFinalRawWeight_eqv_zero_of_ne
          S.coarse.coupling (coarseState other) hotherNonzero
      have hbubbleProductZero :
          wholeSlabFaceRawProduct S fineState coarseState ≈ 0 :=
        wholeSlabFaceRawProduct_eqv_zero_of_face
          S fineState coarseState other hotherMem hbubbleFaceZero
      have hbubbleRawZero :
          wholeSlabRecouplingRawWeight S fineState coarseState ≈ 0 := by
        unfold wholeSlabRecouplingRawWeight
        exact mul_eqv_zero_of_left hbubbleProductZero
      exact Q'.eqv_trans _ 0 _ hbubbleRawZero
        (Q'.eqv_symm hvacuumRawZero)

#print axioms wholeSlabFinePacket_zero
#print axioms wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
#print axioms wholeSlabRecouplingRawWeight_isolatedPairBubble_eqv_vacuum

end YMGap.Continuum.Z4DyadicPairBubbleWholeSlabRawContraction
