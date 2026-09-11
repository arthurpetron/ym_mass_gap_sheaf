/-
# Strict anchor occupation bound for one dyadic fine packet

The causally matched fine antecedent of one coarse face is its complete
four-face dyadic packet.  Packet occupation is the union of the four
fine-face occupation events.  The two-face strand-component contraction
bounds each of those marginals by `64/425`, so a finite union bound gives the
strict packet constant `256/425 < 1`.

At fine cutoff one, the existing SU(2) lowering-support theorem then transfers
this strict constant to the normalized coherent raw mismatch between packet
occupation and coarse-face occupation.  This is a finite-volume statement at
the named SU(2) anchor, not a beta-, lattice-spacing-, or continuum-uniform
gap theorem.

Constructive contract: finite-list Fubini, exact dyadic geometry, and rational
order only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, trusted external computation, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDyadicSupport

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorPacketOccupation

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorOccupation
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDyadicSupport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A constructive finite union bound -/

private theorem listQSum_mono_local {A : Type} (lower upper : A -> Q') :
    forall items : List A,
      (forall item, item ∈ items -> lower item <= upper item) ->
      listQSum lower items <= listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_nonnegative_local {A : Type}
    (value : A -> Q') :
    forall items : List A,
      (forall item, item ∈ items -> (0 : Q') <= value item) ->
      (0 : Q') <= listQSum value items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hnonnegative =>
      Q'.zero_le_add _ _
        (hnonnegative head List.mem_cons_self)
        (listQSum_nonnegative_local value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_member_le_local {A : Type}
    (value : A -> Q') :
    forall items : List A,
      (forall item, item ∈ items -> (0 : Q') <= value item) ->
      forall selected, selected ∈ items ->
        value selected <= listQSum value items
  | [], _, selected, hselected => absurd hselected List.not_mem_nil
  | head :: tail, hnonnegative, selected, hselected => by
      rcases List.mem_cons.mp hselected with hhead | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_local value tail
            (fun item hitem =>
              hnonnegative item (List.mem_cons_of_mem head hitem)))
      · have ih := listQSum_member_le_local value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          selected htail
        have hheadNonnegative := hnonnegative head List.mem_cons_self
        have hmono := Q'.add_le_add_right
          (0 : Q') (value head) (listQSum value tail) hheadNonnegative
        rw [Q'.zero_add'] at hmono
        exact Q'.le_trans' _ _ _ ih hmono

/-- If a Boolean event is covered pointwise by a finite indexed family, its
mass under any nonnegative finite rational measure is bounded by the sum of
the family event masses. -/
private theorem finiteEventMass_le_indexedFamilyMass
    {State Index : Type}
    (mass : State -> Q') (states : List State)
    (event : State -> Bool) (indices : List Index)
    (indexedEvent : Index -> State -> Bool)
    (hmass : forall state, state ∈ states -> (0 : Q') <= mass state)
    (hcover : forall state, event state = true ->
      Exists fun index : Index =>
        index ∈ indices ∧ indexedEvent index state = true) :
    finiteEventMass mass states event <=
      listQSum
        (fun index => finiteEventMass mass states (indexedEvent index))
        indices := by
  unfold finiteEventMass
  have hpoint : forall state, state ∈ states ->
      (if event state then mass state else 0) <=
        listQSum
          (fun index =>
            if indexedEvent index state then mass state else 0)
          indices := by
    intro state hstate
    cases hevent : event state
    · simp only [Bool.false_eq_true, if_false]
      apply listQSum_nonnegative_local
      intro index _
      cases hindexed : indexedEvent index state
      · simp only [Bool.false_eq_true, if_false]
        exact Q'.le_refl' 0
      · simp only [if_true]
        exact hmass state hstate
    · obtain ⟨index, hindex, hindexed⟩ := hcover state hevent
      have hmember := listQSum_member_le_local
        (fun candidate =>
          if indexedEvent candidate state then mass state else 0)
        indices (fun candidate _ => by
          cases hcandidate : indexedEvent candidate state
          · simp only [hcandidate, Bool.false_eq_true, if_false]
            exact Q'.le_refl' 0
          · simp only [hcandidate, if_true]
            exact hmass state hstate)
        index hindex
      simp only [if_true, hindexed] at hmember
      exact hmember
  have hmono := listQSum_mono_local _ _ states hpoint
  exact Q'.le_trans' _ _ _ hmono
    (Q'.le_of_eqv
      (listQSum_swap
        (fun index state =>
          if indexedEvent index state then mass state else 0)
        indices states))

/-! ## 2. The four-face packet union -/

/-- The injected fine-face identifier packet has exactly four entries. -/
theorem dyadicCoarseFaceFineFaceIds_length
    (S : SlabScalePair) (coarseFaceId : Nat) :
    (dyadicCoarseFaceFineFaceIds S coarseFaceId).length = 4 := by
  unfold dyadicCoarseFaceFineFaceIds
  rw [List.length_map]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ :=
    slabPlaquetteAt S.coarse.extent coarseFaceId
  cases plane <;> rfl

/-- Packet occupation mass is bounded by the sum of its four one-face
occupation masses under the genuine normalized fine law. -/
theorem normalizedSlabDyadicFinePacketPositiveMass_le_faceMassSum
    (S : SlabScalePair) (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S coarseFaceId) <=
      listQSum
        (fun fineFaceId =>
          normalizedSlabEventMass S.fine
            (slabPhysicalFacePositiveB fineFaceId))
        (dyadicCoarseFaceFineFaceIds S coarseFaceId) := by
  unfold normalizedSlabEventMass
  apply finiteEventMass_le_indexedFamilyMass
    S.fine.normalizedMass S.fine.physicalLabellings
    (dyadicFinePacketPositiveB S coarseFaceId)
    (dyadicCoarseFaceFineFaceIds S coarseFaceId)
    (fun fineFaceId => slabPhysicalFacePositiveB fineFaceId)
  · intro state _
    exact S.fine.normalizedMass_nonnegative state
  · intro state hpacket
    obtain ⟨fineFaceId, hfineFaceId, hpositive⟩ :=
      (dyadicFinePacketPositiveB_true_iff_exists_positive
        S state coarseFaceId hcoarseFaceId).mp hpacket
    exact ⟨fineFaceId, hfineFaceId, by
      unfold slabPhysicalFacePositiveB
      exact decide_eq_true_eq.mpr hpositive⟩

private theorem listQSum_sixtyFourFourTwentyFive_le_twoFiftySixFourTwentyFive
    {A : Type} (items : List A) (hlength : items.length = 4) :
    listQSum (fun _ : A => Q'.mkPos 64 425 (by decide)) items <=
      Q'.mkPos 256 425 (by decide) := by
  cases items with
  | nil => simp at hlength
  | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second rest =>
          cases rest with
          | nil => simp at hlength
          | cons third rest =>
              cases rest with
              | nil => simp at hlength
              | cons fourth rest =>
                  cases rest with
                  | nil =>
                      change
                        Q'.mkPos 64 425 (by decide) +
                          (Q'.mkPos 64 425 (by decide) +
                            (Q'.mkPos 64 425 (by decide) +
                              (Q'.mkPos 64 425 (by decide) + 0))) <=
                            Q'.mkPos 256 425 (by decide)
                      decide
                  | cons fifth rest => simp at hlength

/-- **Strict four-face packet occupation at the named SU(2) anchor.**  If the
fine datum is the anchor slab, the normalized packet mass is at most
`256/425 < 1`, uniformly in its finite cutoff and volume parameters only at
that explicitly fixed coupling. -/
theorem normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half coarseFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S coarseFaceId) <=
      Q'.mkPos 256 425 (by decide) := by
  let fineFaceIds := dyadicCoarseFaceFineFaceIds S coarseFaceId
  have hunion :=
    normalizedSlabDyadicFinePacketPositiveMass_le_faceMassSum
      S coarseFaceId hcoarseFaceId
  have hfaces : forall fineFaceId, fineFaceId ∈ fineFaceIds ->
      normalizedSlabEventMass S.fine
          (slabPhysicalFacePositiveB fineFaceId) <=
        Q'.mkPos 64 425 (by decide) := by
    intro fineFaceId hfineFaceId
    have hpacketMem : fineFaceId ∈
        wholeSlabDyadicPacketFineFaceIds S := by
      unfold wholeSlabDyadicPacketFineFaceIds
      apply List.mem_flatMap.mpr
      exact ⟨coarseFaceId, hcoarseFaceId, hfineFaceId⟩
    have hphysical : fineFaceId ∈ S.fine.faceEdges :=
      wholeSlabDyadicPacketFineFaceIds_subset_physical S hpacketMem
    rw [hfine] at hphysical ⊢
    exact normalizedAnchorSlabFacePositiveMass_le_sixtyFourFourTwentyFive
      cutoff half fineFaceId hphysical
  have hmono :
      listQSum
          (fun fineFaceId =>
            normalizedSlabEventMass S.fine
              (slabPhysicalFacePositiveB fineFaceId)) fineFaceIds <=
        listQSum
          (fun _ : Nat => Q'.mkPos 64 425 (by decide)) fineFaceIds :=
    listQSum_mono_local _ _ fineFaceIds hfaces
  exact Q'.le_trans' _ _ _ hunion
    (Q'.le_trans' _ _ _ hmono
      (listQSum_sixtyFourFourTwentyFive_le_twoFiftySixFourTwentyFive
        fineFaceIds (dyadicCoarseFaceFineFaceIds_length S coarseFaceId)))

/-- The strict packet constant is genuinely below one. -/
theorem twoFiftySixFourTwentyFive_lt_one :
    Q'.mkPos 256 425 (by decide) < (1 : Q') := by
  decide

/-! ## 3. Strict same-object raw mismatch -/

/-- At fine cutoff one and the named SU(2) anchor, the causally matched
packet/coarse-face raw mismatch average is bounded by the explicit strict
constant `256/425`. -/
theorem coherentDyadicFaceRawMismatchAverage_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half coarseFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    coherentEventRawMismatchAverage S
        (dyadicFinePacketPositiveB S coarseFaceId)
        (slabPhysicalFacePositiveB coarseFaceId) <=
      Q'.mkPos 256 425 (by decide) := by
  exact Q'.le_trans' _ _ _
    (coherentDyadicFaceRawMismatchAverage_le_normalizedPacketMass
      S hfineCutoff coarseFaceId hcoarseFaceId)
    (normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
      S cutoff half coarseFaceId hfine hcoarseFaceId)

#print axioms dyadicCoarseFaceFineFaceIds_length
#print axioms normalizedSlabDyadicFinePacketPositiveMass_le_faceMassSum
#print axioms normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
#print axioms twoFiftySixFourTwentyFive_lt_one
#print axioms coherentDyadicFaceRawMismatchAverage_le_twoFiftySixFourTwentyFive

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorPacketOccupation
