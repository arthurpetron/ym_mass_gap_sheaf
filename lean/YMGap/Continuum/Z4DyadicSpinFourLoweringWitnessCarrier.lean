/-
# Explicit witnesses for the spin-four lowering multiplicity

The lower-triangular SU(2) kernel records a natural-number multiplicity at
each coarse face.  For the later connected-component peeling argument that
number must not remain an opaque prefactor: every copy must carry the actual
pair-fusion channel that it counts.

This file exposes the product multiplicity as a duplicate-free dependent
word of supported `PairChannelState`s, one state for every face in the given
list.  Membership is exactly the recursive facewise support predicate, the
carrier cardinality is exactly `spinFourLoweringMultiplicityProductOn`, and
multiplication by that natural number is exactly a constant-weight sum over
the witness carrier.

Constructive contract: literal filtered finite lists and structural list
induction only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization

namespace YMGap.Continuum.Z4DyadicSpinFourLoweringWitnessCarrier

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicPairBubbleRetainedTargetSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One-face witnesses -/

/-- The literal supported pair-fusion paths from `sourceSpin` to
`targetSpin`. -/
def spinFourLoweringChannels
    (sourceSpin targetSpin : Nat) : List PairChannelState :=
  (pairChannelStateSpace 1).filter
    (spinFourLoweringChannelB sourceSpin targetSpin)

/-- The existing local multiplicity is definitionally the cardinality of
the explicit channel list. -/
theorem spinFourLoweringChannels_length
    (sourceSpin targetSpin : Nat) :
    (spinFourLoweringChannels sourceSpin targetSpin).length =
      spinFourLoweringMultiplicity sourceSpin targetSpin := by
  rfl

/-- Membership exposes both the SU(2) fusion support and the selected final
coarse spin. -/
theorem mem_spinFourLoweringChannels_iff
    (sourceSpin targetSpin : Nat) (state : PairChannelState) :
    state ∈ spinFourLoweringChannels sourceSpin targetSpin ↔
      state ∈ pairChannelStateSpace 1 ∧
        packetPairChannelSupportedBool
            (spinFourPacket sourceSpin) state = true ∧
          state.2 = targetSpin := by
  unfold spinFourLoweringChannels spinFourLoweringChannelB
  rw [List.mem_filter]
  constructor
  · rintro ⟨hspace, htest⟩
    simp only [Bool.and_eq_true] at htest
    exact ⟨hspace, htest.1, of_decide_eq_true htest.2⟩
  · rintro ⟨hspace, hsupport, hfinal⟩
    exact ⟨hspace, by
      simp only [Bool.and_eq_true]
      exact ⟨hsupport, decide_eq_true hfinal⟩⟩

/-- The one-face witness list has no repeated recoupling path. -/
theorem spinFourLoweringChannels_nodup
    (sourceSpin targetSpin : Nat) :
    (spinFourLoweringChannels sourceSpin targetSpin).Nodup := by
  unfold spinFourLoweringChannels
  exact List.filter_sublist.nodup (pairChannelStateSpace_nodup 1)

/-! ## 2. The dependent word over a face list -/

/-- A word of pair-channel states, with one locally supported choice for each
face in the supplied order. -/
def spinFourLoweringWitnessCarrier
    (sourceState targetState : EdgeLabelling) :
    List Nat → List (List PairChannelState)
  | [] => [[]]
  | faceId :: faces =>
      (spinFourLoweringChannels
          (sourceState faceId) (targetState faceId)).flatMap fun channel =>
        (spinFourLoweringWitnessCarrier sourceState targetState faces).map
          fun tail => channel :: tail

/-- Recursive semantic predicate for an aligned face/channel word. -/
def SpinFourLoweringWitnessFits
    (sourceState targetState : EdgeLabelling) :
    List Nat → List PairChannelState → Prop
  | [], [] => True
  | faceId :: faces, channel :: tail =>
      channel ∈ spinFourLoweringChannels
          (sourceState faceId) (targetState faceId) ∧
        SpinFourLoweringWitnessFits sourceState targetState faces tail
  | _, _ => False

/-- Carrier membership is exactly facewise supported recoupling. -/
theorem mem_spinFourLoweringWitnessCarrier_iff
    (sourceState targetState : EdgeLabelling) :
    ∀ (faces : List Nat) (word : List PairChannelState),
      word ∈ spinFourLoweringWitnessCarrier
          sourceState targetState faces ↔
        SpinFourLoweringWitnessFits
          sourceState targetState faces word
  | [], word => by
      cases word <;> simp [spinFourLoweringWitnessCarrier,
        SpinFourLoweringWitnessFits]
  | faceId :: faces, word => by
      constructor
      · intro hword
        unfold spinFourLoweringWitnessCarrier at hword
        obtain ⟨channel, hchannel, hmap⟩ := List.mem_flatMap.mp hword
        obtain ⟨tail, htail, hwordEq⟩ := List.mem_map.mp hmap
        rw [← hwordEq]
        exact ⟨hchannel,
          (mem_spinFourLoweringWitnessCarrier_iff
            sourceState targetState faces tail).mp htail⟩
      · intro hfits
        cases word with
        | nil => cases hfits
        | cons channel tail =>
            apply List.mem_flatMap.mpr
            refine ⟨channel, hfits.1, ?_⟩
            apply List.mem_map.mpr
            exact ⟨tail,
              (mem_spinFourLoweringWitnessCarrier_iff
                sourceState targetState faces tail).mpr hfits.2,
              rfl⟩

private theorem flatMap_cons_word_length
    {A : Type} (heads : List A) (tails : List (List A)) :
    (heads.flatMap fun head =>
      tails.map fun tail => head :: tail).length =
        heads.length * tails.length := by
  induction heads with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- The witness carrier has exactly the old product multiplicity. -/
theorem spinFourLoweringWitnessCarrier_length
    (sourceState targetState : EdgeLabelling) : ∀ faces : List Nat,
    (spinFourLoweringWitnessCarrier
        sourceState targetState faces).length =
      spinFourLoweringMultiplicityProductOn
        sourceState targetState faces
  | [] => rfl
  | faceId :: faces => by
      rw [spinFourLoweringWitnessCarrier,
        flatMap_cons_word_length,
        spinFourLoweringChannels_length,
        spinFourLoweringWitnessCarrier_length
          sourceState targetState faces]
      rfl

private theorem nodup_map_cons_words
    {A : Type} (head : A) : ∀ {tails : List (List A)},
    tails.Nodup → (tails.map fun tail => head :: tail).Nodup
  | [], _ => List.nodup_nil
  | tail :: tails, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
        have htailEq : tail = other := by
          injection heq with _ htailEq
          exact htailEq.symm
        exact hparts.1 (htailEq ▸ hother)
      · exact nodup_map_cons_words head hparts.2

private theorem nodup_flatMap_cons_words
    {A : Type} (heads : List A) (tails : List (List A))
    (hheads : heads.Nodup) (htails : tails.Nodup) :
    (heads.flatMap fun head =>
      tails.map fun tail => head :: tail).Nodup := by
  induction heads with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
      have hparts := List.nodup_cons.mp hheads
      apply List.nodup_append.mpr
      refine ⟨?_, ih hparts.2, ?_⟩
      · exact nodup_map_cons_words head htails
      · intro first hfirst second hsecond heq
        obtain ⟨firstTail, _, hfirstEq⟩ := List.mem_map.mp hfirst
        obtain ⟨otherHead, hotherHead, hotherMap⟩ :=
          List.mem_flatMap.mp hsecond
        obtain ⟨secondTail, _, hsecondEq⟩ := List.mem_map.mp hotherMap
        rw [← hfirstEq, ← hsecondEq] at heq
        have hheadEq : head = otherHead := by injection heq
        exact hparts.1 (hheadEq ▸ hotherHead)

/-- Distinct witness words are not accidentally merged by the dependent
enumeration. -/
theorem spinFourLoweringWitnessCarrier_nodup
    (sourceState targetState : EdgeLabelling) : ∀ faces : List Nat,
    (spinFourLoweringWitnessCarrier
      sourceState targetState faces).Nodup
  | [] => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | faceId :: faces => by
      unfold spinFourLoweringWitnessCarrier
      exact nodup_flatMap_cons_words
        (spinFourLoweringChannels
          (sourceState faceId) (targetState faceId))
        (spinFourLoweringWitnessCarrier sourceState targetState faces)
        (spinFourLoweringChannels_nodup _ _)
        (spinFourLoweringWitnessCarrier_nodup
          sourceState targetState faces)

/-! ## 3. Exact multiplicity expansion -/

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

/-- The numeric product multiplicity is exactly a sum over explicit
facewise recoupling witnesses. -/
theorem spinFourLoweringMultiplicityProductOn_mul_eqv_witnessSum
    (sourceState targetState : EdgeLabelling)
    (faces : List Nat) (constant : Q') :
    Q'.ofNat
          (spinFourLoweringMultiplicityProductOn
            sourceState targetState faces) * constant ≈
      listQSum (fun _word => constant)
        (spinFourLoweringWitnessCarrier
          sourceState targetState faces) := by
  rw [← spinFourLoweringWitnessCarrier_length
    sourceState targetState faces]
  exact Q'.eqv_symm
    (listQSum_const_local constant
      (spinFourLoweringWitnessCarrier
        sourceState targetState faces))

#print axioms spinFourLoweringChannels_length
#print axioms mem_spinFourLoweringChannels_iff
#print axioms spinFourLoweringChannels_nodup
#print axioms mem_spinFourLoweringWitnessCarrier_iff
#print axioms spinFourLoweringWitnessCarrier_length
#print axioms spinFourLoweringWitnessCarrier_nodup
#print axioms spinFourLoweringMultiplicityProductOn_mul_eqv_witnessSum

end YMGap.Continuum.Z4DyadicSpinFourLoweringWitnessCarrier
