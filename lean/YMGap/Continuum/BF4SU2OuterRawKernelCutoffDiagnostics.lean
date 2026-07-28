/-
# Constructive cutoff diagnostics for the BF4 SU(2) whole-slab raw kernel

This module proves the finite-support facts directly at the literal
`wholeSlabRecouplingRawWeight` level.  An old fine source bounds every
four-spin packet by `K`.  The SU(2) triangle rule then kills every pair
channel outside the `K` carrier, while a coarse label above `4K` kills the
entire corresponding face sum.

The proof first isolates those unnormalized support facts, then carries them
through raw-partition normalization and null-row completion, including the
cutoff-zero crossing.  It constructs
`SU2OuterRawKernelCutoffStability`, the two-field coherence package, and the
physical Markov contract from `SU2OuterPositiveRowClosure` alone.

## Axiom gate

Finite `List`, `Nat`, `Bool`, and `Q'` algebra only.  No classical
principle, `sorry`, `native_decide`, custom axiom, choice, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
import YMGap.Continuum.BF4SU2OuterRawKernelCoherenceReduction
import YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
import YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup
import YMGap.Continuum.Z4ValenceFusionCutoffIndependence

namespace YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterRawKernelCoherenceReduction
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite extension algebra -/

private theorem listQSum_perm_local {A : Type}
    (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_perm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      exact Q'.eqv_trans _
        ((value second + value first) +
          listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.eqv_trans _
          ((value first + value second) +
            listQSum value rest) _
          (Q'.add_eqv_congr_right _ _
            (listQSum value rest)
            (Q'.add_comm_eqv _ _))
          (Q'.add_assoc_eqv _ _ _))
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value hleft)
        (listQSum_perm_local value hright)

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
        exact hzero item
          (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest,
            Bool.false_eq_true, if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local
                value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local
              value test tail htail)

private theorem listQSum_eqv_zero_of_all_local
    {A : Type} (value : A → Q') :
    ∀ source : List A,
      (∀ item, item ∈ source → value item ≈ 0) →
      listQSum value source ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      exact Q'.eqv_trans _
        (0 + 0) _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_all_local
            value tail
            (fun item hitem =>
              hzero item
                (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_extension_eq
    {A : Type} [DecidableEq A]
    (value : A → Q') (small large : List A)
    (hsmall : small.Nodup) (hlarge : large.Nodup)
    (hsubset : ∀ item, item ∈ small → item ∈ large)
    (hzero :
      ∀ item, item ∈ large → item ∉ small →
        value item ≈ 0) :
    listQSum value large ≈ listQSum value small := by
  let oldTest : A → Bool :=
    fun item => decide (item ∈ small)
  refine Q'.eqv_trans _
    (listQSum value (large.filter oldTest)) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero_local
    intro item hitem htest
    apply hzero item hitem
    simpa only [oldTest, decide_eq_false_iff_not] using htest
  · apply listQSum_perm_local
    apply perm_of_nodup_mem_iff
    · exact List.filter_sublist.nodup hlarge
    · exact hsmall
    · intro item
      simp only [List.mem_filter, oldTest, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hsubset item h, h⟩

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨rangeNodupLocal bound,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl bound)
        (List.mem_range.mp hleft)

private theorem slabPhysicalFaceEdgesNodupLocal
    (extent : Nat) :
    (slabPhysicalFaceEdges extent).Nodup := by
  unfold slabPhysicalFaceEdges
  exact rangeNodupLocal _

/-! ## 2. Pair-channel support is exhausted at the old cutoff -/

theorem pairChannelStateSpace_mem_of_le
    {K L : Nat} (hKL : K ≤ L)
    {state : PairChannelState}
    (hstate : state ∈ pairChannelStateSpace K) :
    state ∈ pairChannelStateSpace L := by
  have hbounds :=
    (mem_pairChannelStateSpace_iff K state).mp hstate
  apply (mem_pairChannelStateSpace_iff L state).mpr
  exact
    ⟨Nat.le_trans hbounds.1
        (Nat.mul_le_mul_left 2 hKL),
      Nat.le_trans hbounds.2.1
        (Nat.mul_le_mul_left 2 hKL),
      Nat.le_trans hbounds.2.2
        (Nat.mul_le_mul_left 4 hKL)⟩

theorem packetPairChannelRawWeight_eqv_zero_of_not_mem
    {w : Q'} {K : Nat}
    {packet : FaceSpinPacket}
    (hpacket : packet ∈ faceSpinPacketStateSpace K)
    {state : PairChannelState}
    (hstate : state ∉ pairChannelStateSpace K) :
    packetPairChannelRawWeight w packet state ≈ 0 := by
  have hpacketBounds :=
    (mem_faceSpinPacketStateSpace_iff K packet).mp hpacket
  have houtside :
      2 * K < state.1.1 ∨
        2 * K < state.1.2 ∨
          4 * K < state.2 := by
    by_cases hleft : state.1.1 ≤ 2 * K
    · by_cases hright : state.1.2 ≤ 2 * K
      · by_cases hfinal : state.2 ≤ 4 * K
        · exact False.elim
            (hstate
              ((mem_pairChannelStateSpace_iff K state).mpr
                ⟨hleft, hright, hfinal⟩))
        · exact Or.inr (Or.inr (by omega))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  rcases houtside with hleft | hright | hfinal
  · have hzero :
        fusionInd packet.spin0 packet.spin1 state.1.1 = 0 :=
      fusionInd_zero_of_add_lt (by omega)
    unfold packetPairChannelRawWeight
    rw [hzero]
    exact Q'.eqv_trans _
      (coeffW w state.2 * 0) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.zero_mul_eqv _))
      (Q'.mul_zero_eqv _)
  · have hzero :
        fusionInd packet.spin2 packet.spin3 state.1.2 = 0 :=
      fusionInd_zero_of_add_lt (by omega)
    unfold packetPairChannelRawWeight
    rw [hzero]
    refine Q'.eqv_trans _
      (coeffW w state.2 *
        (fusionInd packet.spin0 packet.spin1 state.1.1 * 0)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.zero_mul_eqv _))
    · exact Q'.eqv_trans _
        (coeffW w state.2 * 0) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_zero_eqv _))
        (Q'.mul_zero_eqv _)
  · have hleftBound :
        state.1.1 ≤ packet.spin0 + packet.spin1 ∨
          packet.spin0 + packet.spin1 < state.1.1 := by
      omega
    rcases hleftBound with hleftBound | hleftTooLarge
    · have hrightBound :
          state.1.2 ≤ packet.spin2 + packet.spin3 ∨
            packet.spin2 + packet.spin3 < state.1.2 := by
        omega
      rcases hrightBound with hrightBound | hrightTooLarge
      · have hzero :
            fusionInd state.1.1 state.1.2 state.2 = 0 :=
          fusionInd_zero_of_add_lt (by omega)
        unfold packetPairChannelRawWeight
        rw [hzero]
        refine Q'.eqv_trans _
          (coeffW w state.2 *
            (fusionInd packet.spin0 packet.spin1 state.1.1 * 0)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_zero_eqv _))
        · exact Q'.eqv_trans _
            (coeffW w state.2 * 0) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_zero_eqv _))
            (Q'.mul_zero_eqv _)
      · have hzero :
            fusionInd packet.spin2 packet.spin3 state.1.2 = 0 :=
          fusionInd_zero_of_add_lt hrightTooLarge
        unfold packetPairChannelRawWeight
        rw [hzero]
        refine Q'.eqv_trans _
          (coeffW w state.2 *
            (fusionInd packet.spin0 packet.spin1 state.1.1 * 0)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.zero_mul_eqv _))
        · exact Q'.eqv_trans _
            (coeffW w state.2 * 0) _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_zero_eqv _))
            (Q'.mul_zero_eqv _)
    · have hzero :
          fusionInd packet.spin0 packet.spin1 state.1.1 = 0 :=
        fusionInd_zero_of_add_lt hleftTooLarge
      unfold packetPairChannelRawWeight
      rw [hzero]
      exact Q'.eqv_trans _
        (coeffW w state.2 * 0) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.zero_mul_eqv _))
        (Q'.mul_zero_eqv _)

theorem packetPairChannelSum_cutoff_stable
    {w : Q'} {K L : Nat} (hKL : K ≤ L)
    {packet : FaceSpinPacket}
    (hpacket : packet ∈ faceSpinPacketStateSpace K)
    (event : PairChannelState → Bool) :
    listQSum
        (fun state =>
          if event state then
            packetPairChannelRawWeight w packet state
          else 0)
        (pairChannelStateSpace K) ≈
      listQSum
        (fun state =>
          if event state then
            packetPairChannelRawWeight w packet state
          else 0)
        (pairChannelStateSpace L) := by
  apply Q'.eqv_symm
  apply listQSum_extension_eq
  · exact pairChannelStateSpace_nodup K
  · exact pairChannelStateSpace_nodup L
  · intro state hstate
    exact pairChannelStateSpace_mem_of_le hKL hstate
  · intro state _ hnew
    split
    · exact packetPairChannelRawWeight_eqv_zero_of_not_mem
        hpacket hnew
    · exact Q'.eqv_refl 0

theorem packetPairChannelFinalSum_cutoff_stable
    {w : Q'} {K L : Nat} (hKL : K ≤ L)
    {packet : FaceSpinPacket}
    (hpacket : packet ∈ faceSpinPacketStateSpace K)
    (finalSpin : Nat) :
    listQSum
        (fun state =>
          if state.2 = finalSpin then
            packetPairChannelRawWeight w packet state
          else 0)
        (pairChannelStateSpace K) ≈
      listQSum
        (fun state =>
          if state.2 = finalSpin then
            packetPairChannelRawWeight w packet state
          else 0)
        (pairChannelStateSpace L) := by
  apply Q'.eqv_symm
  apply listQSum_extension_eq
  · exact pairChannelStateSpace_nodup K
  · exact pairChannelStateSpace_nodup L
  · intro state hstate
    exact pairChannelStateSpace_mem_of_le hKL hstate
  · intro state _ hnew
    split
    · exact packetPairChannelRawWeight_eqv_zero_of_not_mem
        hpacket hnew
    · exact Q'.eqv_refl 0

/-! ## 3. Every physical fine state supplies bounded geometric packets -/

theorem slabSpinAtPlaquette_le_of_physical
    {K extent : Nat} {physical : EdgeLabelling}
    (hphysical :
      physical ∈
        boundedEdgeLabellings K
          (slabPhysicalFaceEdges extent))
    (plaquette :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plaq) :
    slabSpinAtPlaquette extent physical plaquette ≤ K := by
  by_cases hplaquette :
      plaquette ∈ boundaryCompleteSlabPlaquettes extent
  · rw [slabSpinAtPlaquette_eq_of_mem hplaquette]
    have hindex :
        listIndexOf plaquette
            (boundaryCompleteSlabPlaquettes extent) ∈
          slabPhysicalFaceEdges extent := by
      unfold slabPhysicalFaceEdges
      exact List.mem_range.mpr
        (listIndexOf_lt_of_mem plaquette
          (boundaryCompleteSlabPlaquettes extent)
          hplaquette)
    have hbound :=
      (boundedEdgeLabellings_sound K
        (slabPhysicalFaceEdges extent)
        physical hphysical).1 _ hindex
    omega
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hplaquette]
    exact Nat.zero_le K

theorem wholeSlabFinePacket_mem_stateSpace
    {S : CompactDualFiniteBlockRemainder.SlabScalePair}
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (coarseFaceId : Nat) :
    wholeSlabFinePacket S fineState coarseFaceId ∈
      faceSpinPacketStateSpace S.fine.cutoff := by
  unfold wholeSlabFinePacket
  apply dyadicFaceSpinPacket_mem_stateSpace
  intro plaquette
  exact slabSpinAtPlaquette_le_of_physical hfine plaquette

/-! ## 4. Literal whole-face stability and upper support -/

theorem su2OuterWholeSlabFaceRawWeight_cutoff_stable
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (target : EdgeLabelling)
    (coarseFaceId : Nat) :
    wholeSlabFaceRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate K)
        source target coarseFaceId ≈
      wholeSlabFaceRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target coarseFaceId := by
  unfold wholeSlabFaceRawWeight
  dsimp only [su2OuterScalePair, su2FineOuterData,
    su2CoarseOuterData, SlabPhysicalData.cutoff,
    SlabPhysicalData.extent, SlabPhysicalData.half,
    SlabPhysicalData.coupling]
  exact packetPairChannelFinalSum_cutoff_stable
    hKL
    (wholeSlabFinePacket_mem_stateSpace
      (S := su2OuterScalePair
        G g hg candidate hcandidate K)
      hsource coarseFaceId)
    (target coarseFaceId)

theorem su2OuterWholeSlabFaceRawWeight_eqv_zero_of_above
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K L : Nat)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (target : EdgeLabelling)
    (coarseFaceId : Nat)
    (habove : 4 * K < target coarseFaceId) :
    wholeSlabFaceRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target coarseFaceId ≈ 0 := by
  unfold wholeSlabFaceRawWeight
  apply listQSum_eqv_zero_of_all_local
  intro state hstate
  split
  · apply packetPairChannelRawWeight_eqv_zero_of_not_mem
      (wholeSlabFinePacket_mem_stateSpace
        (S := su2OuterScalePair
          G g hg candidate hcandidate K)
        hsource coarseFaceId)
    intro hold
    have hbounds :=
      (mem_pairChannelStateSpace_iff K state).mp hold
    omega
  · exact Q'.eqv_refl 0

/-! ## 5. The corrected-slab link factor is cutoff-stable on old targets -/

private theorem listGetD_le_of_spinsBounded
    {K : Nat} :
    ∀ (spins : List Nat) (position : Nat),
      SpinsBounded K spins →
      position < spins.length →
      spins.getD position 0 ≤ K
  | [], position, _, hposition =>
      False.elim (Nat.not_lt_zero position hposition)
  | head :: tail, 0, hbounded, _ => by
      simp only [List.getD_cons_zero]
      exact hbounded head List.mem_cons_self
  | head :: tail, position + 1, hbounded, hposition => by
      simp only [List.getD_cons_succ]
      apply listGetD_le_of_spinsBounded tail position
      · intro spin hspin
        exact hbounded spin
          (List.mem_cons_of_mem head hspin)
      · simp only [List.length_cons] at hposition
        omega

theorem slabFaceLabellingBounded_of_physical
    {K extent : Nat} {physical : EdgeLabelling}
    (hphysical :
      physical ∈
        boundedEdgeLabellings K
          (slabPhysicalFaceEdges extent)) :
    SlabFaceLabellingBounded K extent physical := by
  intro id hid
  have hbound :=
    (boundedEdgeLabellings_sound K
      (slabPhysicalFaceEdges extent)
      physical hphysical).1 id hid
  omega

theorem slabExplicitLinkMultiplicity_cutoff_stable
    {K L extent : Nat} (hKL : K ≤ L)
    {physical : EdgeLabelling}
    (hbounded :
      SlabFaceLabellingBounded K extent physical)
    (link :
      YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    slabExplicitLinkMultiplicity L extent physical link =
      slabExplicitLinkMultiplicity K extent physical link := by
  unfold slabExplicitLinkMultiplicity
  let spins :=
    (slabIncidentPlaqIds extent link).map physical
  let external := externalSpinsOfList spins
  apply explicitValenceMultiplicity_cutoff_independent
      external
  · unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  · simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link
  · intro position hposition
    exact listGetD_le_of_spinsBounded
      spins position
      (slabIncidentSpins_bounded hbounded link)
      hposition

theorem slabExplicitLinkMultiplicityProduct_cutoff_stable
    {K L extent : Nat} (hKL : K ≤ L)
    {physical : EdgeLabelling}
    (hbounded :
      SlabFaceLabellingBounded K extent physical) :
    slabExplicitLinkMultiplicityProduct L extent physical =
      slabExplicitLinkMultiplicityProduct K extent physical := by
  unfold slabExplicitLinkMultiplicityProduct
  apply natListProduct_congr
  intro link _
  exact slabExplicitLinkMultiplicity_cutoff_stable
    hKL hbounded link

theorem su2OuterLinkMultiplicityProduct_cutoff_stable
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    {K L : Nat} (hKL : K ≤ L)
    {target : EdgeLabelling}
    (htarget :
      target ∈
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) :
    slabExplicitLinkMultiplicityProduct
        (4 * L) (centralExtent G.coarseHalf) target =
      slabExplicitLinkMultiplicityProduct
        (4 * K) (centralExtent G.coarseHalf) target := by
  apply slabExplicitLinkMultiplicityProduct_cutoff_stable
  · exact Nat.mul_le_mul_left 4 hKL
  · exact slabFaceLabellingBounded_of_physical htarget

/-! ## 6. Complete raw-weight stability on retained states -/

private theorem wholeSlabFiniteQProduct_congr_local
    {A : Type} (left right : A → Q') :
    ∀ source : List A,
      (∀ item, item ∈ source →
        left item ≈ right item) →
      wholeSlabFiniteQProduct left source ≈
        wholeSlabFiniteQProduct right source
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree =>
      Q'.eqv_trans _
        (right head *
          wholeSlabFiniteQProduct left tail) _
        (Q'.mul_eqv_congr_right _ _
          (wholeSlabFiniteQProduct left tail)
          (hagree head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (wholeSlabFiniteQProduct_congr_local
            left right tail
            (fun item hitem =>
              hagree item
                (List.mem_cons_of_mem head hitem))))

theorem su2OuterWholeSlabFaceRawProduct_cutoff_stable
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (target : EdgeLabelling) :
    wholeSlabFaceRawProduct
        (su2OuterScalePair
          G g hg candidate hcandidate K)
        source target ≈
      wholeSlabFaceRawProduct
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target := by
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate K)
        source target)
      (su2CoarseOuterData
        G candidate hcandidate K).faceEdges) _ ?_ ?_
  · exact wholeSlabFaceRawProduct_eqv_finiteQProduct
      (su2OuterScalePair
        G g hg candidate hcandidate K)
      source target
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target)
      (su2CoarseOuterData
        G candidate hcandidate L).faceEdges) _ ?_ ?_
  · apply wholeSlabFiniteQProduct_congr_local
    intro coarseFaceId _
    exact
      su2OuterWholeSlabFaceRawWeight_cutoff_stable
        G g hg candidate hcandidate hKL hsource
        target coarseFaceId
  · exact Q'.eqv_symm
      (wholeSlabFaceRawProduct_eqv_finiteQProduct
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target)

theorem su2OuterWholeSlabRecouplingRawWeight_cutoff_stable
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    {K L : Nat} (hKL : K ≤ L)
    {source target : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (htarget :
      target ∈
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) :
    wholeSlabRecouplingRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate K)
        source target ≈
      wholeSlabRecouplingRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target := by
  unfold wholeSlabRecouplingRawWeight
  refine Q'.eqv_trans _
    (wholeSlabFaceRawProduct
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target *
      Q'.ofNat
        (slabExplicitLinkMultiplicityProduct
          (4 * K) (centralExtent G.coarseHalf) target)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (su2OuterWholeSlabFaceRawProduct_cutoff_stable
        G g hg candidate hcandidate hKL hsource target)
  · change
      wholeSlabFaceRawProduct
            (su2OuterScalePair
              G g hg candidate hcandidate L)
            source target *
          Q'.ofNat
            (slabExplicitLinkMultiplicityProduct
              (4 * K) (centralExtent G.coarseHalf) target) ≈
        wholeSlabFaceRawProduct
            (su2OuterScalePair
              G g hg candidate hcandidate L)
            source target *
          Q'.ofNat
            (slabExplicitLinkMultiplicityProduct
              (4 * L) (centralExtent G.coarseHalf) target)
    rw [su2OuterLinkMultiplicityProduct_cutoff_stable
      G candidate hcandidate hKL htarget]
    exact Q'.eqv_refl _

/-! ## 7. Genuinely new coarse targets have zero old-source raw mass -/

theorem boundedEdgeLabellings_mem_of_le
    {K L : Nat} (hKL : K ≤ L)
    (edges : List Nat) {physical : EdgeLabelling}
    (hphysical :
      physical ∈ boundedEdgeLabellings K edges) :
    physical ∈ boundedEdgeLabellings L edges := by
  have hsound :=
    boundedEdgeLabellings_sound K edges physical hphysical
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    have hbound := hsound.1 edge hedge
    omega
  · exact hsound.2

private theorem labelWithinB_false_of_not_mem
    {K L : Nat} (edges : List Nat)
    {physical : EdgeLabelling}
    (hlarge :
      physical ∈ boundedEdgeLabellings L edges)
    (hnotSmall :
      physical ∉ boundedEdgeLabellings K edges) :
    labelWithinB K edges physical = false := by
  cases hwithin : labelWithinB K edges physical with
  | false => rfl
  | true =>
      exact False.elim
        (hnotSmall
          (boundedEdgeLabellings_complete K edges physical
            ((labelWithinB_true_iff K edges physical).mp
              hwithin)
            ((boundedEdgeLabellings_sound L edges
              physical hlarge).2)))

private theorem
    wholeSlabFiniteQProduct_zero_of_labelWithinB_false
    (K : Nat) (target : EdgeLabelling)
    (value : Nat → Q') :
    ∀ edges : List Nat,
      labelWithinB K edges target = false →
      (∀ edge, edge ∈ edges → K < target edge →
        value edge ≈ 0) →
      wholeSlabFiniteQProduct value edges ≈ 0
  | [], hfalse, _ => by
      simp only [labelWithinB] at hfalse
      exact Bool.noConfusion hfalse
  | head :: tail, hfalse, hzero => by
      simp only [labelWithinB] at hfalse
      cases hhead :
          decide (target head < K + 1) with
      | false =>
          have habove : K < target head := by
            have hnot :
                ¬ target head < K + 1 := by
              simpa only [decide_eq_false_iff_not] using hhead
            omega
          refine Q'.eqv_trans _
            (0 * wholeSlabFiniteQProduct value tail) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _
              (wholeSlabFiniteQProduct value tail)
              (hzero head List.mem_cons_self habove)
          · exact Q'.zero_mul_eqv _
      | true =>
          have htail :
              labelWithinB K tail target = false := by
            simpa only [hhead, Bool.true_and] using hfalse
          refine Q'.eqv_trans _
            (value head * 0) _ ?_ ?_
          · exact Q'.mul_eqv_congr_left _ _ _
              (wholeSlabFiniteQProduct_zero_of_labelWithinB_false
                K target value tail htail
                (fun edge hedge habove =>
                  hzero edge
                    (List.mem_cons_of_mem head hedge)
                    habove))
          · exact Q'.mul_zero_eqv _

theorem su2OuterWholeSlabFaceRawProduct_old_source_no_new_target
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K L : Nat)
    {source target : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (htarget :
      target ∈
        (su2CoarseOuterData
          G candidate hcandidate L).physicalLabellings)
    (hnew :
      target ∉
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) :
    wholeSlabFaceRawProduct
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target ≈ 0 := by
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target)
      (slabPhysicalFaceEdges
        (centralExtent G.coarseHalf))) _ ?_ ?_
  · exact wholeSlabFaceRawProduct_eqv_finiteQProduct
      (su2OuterScalePair
        G g hg candidate hcandidate L)
      source target
  · apply
      wholeSlabFiniteQProduct_zero_of_labelWithinB_false
        (4 * K) target
    · exact labelWithinB_false_of_not_mem
        (slabPhysicalFaceEdges
          (centralExtent G.coarseHalf))
        htarget hnew
    · intro coarseFaceId _ habove
      exact
        su2OuterWholeSlabFaceRawWeight_eqv_zero_of_above
          G g hg candidate hcandidate K L
          hsource target coarseFaceId habove

theorem su2OuterWholeSlabRecouplingRawWeight_old_source_no_new_target
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K L : Nat)
    {source target : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (htarget :
      target ∈
        (su2CoarseOuterData
          G candidate hcandidate L).physicalLabellings)
    (hnew :
      target ∉
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) :
    wholeSlabRecouplingRawWeight
        (su2OuterScalePair
          G g hg candidate hcandidate L)
        source target ≈ 0 := by
  unfold wholeSlabRecouplingRawWeight
  exact Q'.eqv_trans _
    (0 *
      Q'.ofNat
        (slabExplicitLinkMultiplicityProduct
          (su2OuterScalePair
            G g hg candidate hcandidate L).coarse.cutoff
          (su2OuterScalePair
            G g hg candidate hcandidate L).coarse.extent
          target)) _
    (Q'.mul_eqv_congr_right _ _ _
      (su2OuterWholeSlabFaceRawProduct_old_source_no_new_target
        G g hg candidate hcandidate K L
        hsource htarget hnew))
    (Q'.zero_mul_eqv _)

/-! ## 8. Raw row partitions and positive normalized rows -/

def su2OuterWholeSlabRawPartition
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (K : Nat) (source : EdgeLabelling) : Q' :=
  listQSum
    (wholeSlabRecouplingRawWeight
      (su2OuterScalePair
        G g hg candidate hcandidate K)
      source)
    (su2CoarseOuterData
      G candidate hcandidate K).physicalLabellings

theorem su2OuterWholeSlabRawPartition_cutoff_stable
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    su2OuterWholeSlabRawPartition
        G g hg candidate hcandidate K source ≈
      su2OuterWholeSlabRawPartition
        G g hg candidate hcandidate L source := by
  let small :=
    (su2CoarseOuterData
      G candidate hcandidate K).physicalLabellings
  let large :=
    (su2CoarseOuterData
      G candidate hcandidate L).physicalLabellings
  let rawK :=
    wholeSlabRecouplingRawWeight
      (su2OuterScalePair
        G g hg candidate hcandidate K)
      source
  let rawL :=
    wholeSlabRecouplingRawWeight
      (su2OuterScalePair
        G g hg candidate hcandidate L)
      source
  let oldTest :=
    labelWithinB (4 * K)
      (slabPhysicalFaceEdges
        (centralExtent G.coarseHalf))
  have hfilter :
      large.filter oldTest = small := by
    dsimp only [large, small, oldTest,
      su2CoarseOuterData,
      SlabPhysicalData.physicalLabellings,
      SlabPhysicalData.cutoff,
      SlabPhysicalData.faceEdges,
      SlabPhysicalData.extent,
      SlabPhysicalData.half]
    exact boundedEdgeLabellings_filter_cutoff
      (Nat.mul_le_mul_left 4 hKL) _
      (slabPhysicalFaceEdgesNodupLocal _)
  refine Q'.eqv_trans _
    (listQSum rawL small) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact
      su2OuterWholeSlabRecouplingRawWeight_cutoff_stable
        G g hg candidate hcandidate hKL
        hsource htarget
  · apply Q'.eqv_symm
    refine Q'.eqv_trans _
      (listQSum rawL (large.filter oldTest)) _ ?_ ?_
    · apply listQSum_eq_filter_of_zero_local
      intro target htarget htest
      apply
        su2OuterWholeSlabRecouplingRawWeight_old_source_no_new_target
          G g hg candidate hcandidate K L
          hsource htarget
      intro hsmall
      have hfiltered :
          target ∈ large.filter oldTest := by
        rw [hfilter]
        exact hsmall
      have htrue := (List.mem_filter.mp hfiltered).2
      rw [htest] at htrue
      cases htrue
    · rw [hfilter]
      exact Q'.eqv_refl _

private theorem qeqv_of_le_of_ge_local
    {left right : Q'}
    (hle : left ≤ right) (hge : right ≤ left) :
    left ≈ right := by
  show left.num * (right.den : Int) =
    right.num * (left.den : Int)
  exact Int.le_antisymm hle hge

private theorem divPos_eqv_congr_local
    {numerator numeratorLater
      denominator denominatorLater : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hdenominatorLater :
      (0 : Q') < denominatorLater)
    (hnumerator : numerator ≈ numeratorLater)
    (hdenominatorEq :
      denominator ≈ denominatorLater) :
    Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos numeratorLater denominatorLater
        hdenominatorLater := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le
      numeratorLater denominatorLater
      hdenominatorLater
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator denominator
            hdenominator)
          denominatorLater denominator
          (Q'.eqv_symm hdenominatorEq))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator denominator hdenominator)
          hnumerator))
  · apply Q'.le_divPos_of_mul_le
      numerator denominator hdenominator
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numeratorLater denominatorLater
            hdenominatorLater)
          denominator denominatorLater
          hdenominatorEq)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv numeratorLater
            denominatorLater hdenominatorLater)
          (Q'.eqv_symm hnumerator)))

theorem su2FineOuterPhysical_mem_of_le
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    source ∈
      (su2FineOuterData G g hg L).physicalLabellings := by
  dsimp only [su2FineOuterData,
    SlabPhysicalData.physicalLabellings,
    SlabPhysicalData.cutoff,
    SlabPhysicalData.faceEdges,
    SlabPhysicalData.extent,
    SlabPhysicalData.half] at hsource ⊢
  exact boundedEdgeLabellings_mem_of_le
    hKL _ hsource

theorem su2FineOuterPhysicalTerm_cutoff_stable
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings) :
    (su2FineOuterData G g hg L).physicalTerm source ≈
      (su2FineOuterData G g hg K).physicalTerm source := by
  dsimp only [su2FineOuterData,
    SlabPhysicalData.physicalTerm,
    SlabPhysicalData.coupling,
    SlabPhysicalData.cutoff,
    SlabPhysicalData.extent,
    SlabPhysicalData.half]
  exact slabParametricKPhysicalTerm_cutoff_stable
    hKL hsource

theorem su2FineOuterPhysicalTerm_pos_of_le
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (hpositive :
      (0 : Q') <
        (su2FineOuterData G g hg K).physicalTerm source) :
    (0 : Q') <
      (su2FineOuterData G g hg L).physicalTerm source := by
  exact Q'.pos_of_lt_of_le hpositive
    (Q'.ge_of_eqv
      (su2FineOuterPhysicalTerm_cutoff_stable
        G g hg hKL hsource))

private theorem coherentSource_fineState
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    (K : Nat) (source : EdgeLabelling)
    (hsource :
      source ∈
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalLabellings)
    (hpositive :
      (0 : Q') <
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalTerm source) :
    (closure.coherentSource
      K source hsource hpositive).fineState = source := by
  unfold SU2OuterPositiveRowClosure.coherentSource
  split
  · rename_i hK
    subst K
    rfl
  · rfl

theorem outerWholeSlabKernel_cutoff_stable_of_positive
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (hpositive :
      (0 : Q') <
        (su2FineOuterData G g hg K).physicalTerm source)
    {target : EdgeLabelling}
    (htarget :
      target ∈
        (su2CoarseOuterData
          G candidate hcandidate K).physicalLabellings) :
    outerWholeSlabKernel closure K source target ≈
      outerWholeSlabKernel closure L source target := by
  have hsourceL :=
    su2FineOuterPhysical_mem_of_le
      G g hg hKL hsource
  have hpositiveL :=
    su2FineOuterPhysicalTerm_pos_of_le
      G g hg hKL hsource hpositive
  let sourceK :=
    closure.coherentSource
      K source hsource hpositive
  let sourceL :=
    closure.coherentSource
      L source hsourceL hpositiveL
  have hfineK : sourceK.fineState = source :=
    coherentSource_fineState
      closure K source hsource hpositive
  have hfineL : sourceL.fineState = source :=
    coherentSource_fineState
      closure L source hsourceL hpositiveL
  refine Q'.eqv_trans _
    (wholeSlabRecouplingConditionalKernel
      sourceK target) _ ?_ ?_
  · exact outerWholeSlabKernel_eq_positive
      closure K hsource hpositive target
  refine Q'.eqv_trans _
    (wholeSlabRecouplingConditionalKernel
      sourceL target) _ ?_ ?_
  · have hraw :
        wholeSlabRecouplingRawWeight
              (su2OuterScalePair
                G g hg candidate hcandidate K)
              sourceK.fineState target ≈
          wholeSlabRecouplingRawWeight
              (su2OuterScalePair
                G g hg candidate hcandidate L)
              sourceL.fineState target := by
      rw [hfineK, hfineL]
      exact
        su2OuterWholeSlabRecouplingRawWeight_cutoff_stable
          G g hg candidate hcandidate hKL
          hsource htarget
    have hpartition :
        wholeSlabRecouplingPartition sourceK ≈
          wholeSlabRecouplingPartition sourceL := by
      unfold wholeSlabRecouplingPartition
      change
        listQSum
              (wholeSlabRecouplingRawWeight
                (su2OuterScalePair
                  G g hg candidate hcandidate K)
                sourceK.fineState)
              (su2CoarseOuterData
                G candidate hcandidate K).physicalLabellings ≈
          listQSum
              (wholeSlabRecouplingRawWeight
                (su2OuterScalePair
                  G g hg candidate hcandidate L)
                sourceL.fineState)
              (su2CoarseOuterData
                G candidate hcandidate L).physicalLabellings
      rw [hfineK, hfineL]
      exact
        su2OuterWholeSlabRawPartition_cutoff_stable
          G g hg candidate hcandidate hKL hsource
    unfold wholeSlabRecouplingConditionalKernel
    exact divPos_eqv_congr_local
      (wholeSlabRecouplingPartition_pos sourceK)
      (wholeSlabRecouplingPartition_pos sourceL)
      hraw hpartition
  · exact Q'.eqv_symm
      (outerWholeSlabKernel_eq_positive
        closure L hsourceL hpositiveL target)

/-! ## 9. Null-row bookkeeping, including the cutoff-zero crossing -/

theorem outerNullCompletion_cutoff_stable
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (target : EdgeLabelling) :
    outerNullCompletion
        G g hg candidate hcandidate K source target =
      outerNullCompletion
        G g hg candidate hcandidate L source target := by
  by_cases hKzero : K = 0
  · subst K
    have hsourceZero : source = zeroEdgeLabelling := by
      change
        source ∈
          boundedEdgeLabellings 0
            (slabPhysicalFaceEdges
              (centralExtent G.fineHalf)) at hsource
      rw [boundedEdgeLabellings_zero] at hsource
      exact List.mem_singleton.mp hsource
    subst source
    by_cases hLzero : L = 0
    · subst L
      rfl
    · have hLpositive : 1 ≤ L := by omega
      have htest :
          supportedLabellingEqB
              (su2FineOuterData G g hg L).faceEdges
              zeroEdgeLabelling
              (fixedSingletonLabelling
                (su2FineOuterData G g hg L)) =
            false := by
        cases heq :
            supportedLabellingEqB
              (su2FineOuterData G g hg L).faceEdges
              zeroEdgeLabelling
              (fixedSingletonLabelling
                (su2FineOuterData G g hg L)) with
        | false => rfl
        | true =>
            have hlabelEq :
                zeroEdgeLabelling =
                  fixedSingletonLabelling
                    (su2FineOuterData G g hg L) :=
              (supportedLabellingEqB_true_iff
                (zeroEdgeLabelling_mem_slab
                  (su2FineOuterData G g hg L))
                (fixedSingletonLabelling_mem
                  (su2FineOuterData G g hg L)
                  hLpositive)).mp heq
            exact False.elim
              ((fixedSingletonLabelling_ne_zero
                (su2FineOuterData G g hg L))
                hlabelEq.symm)
      unfold outerNullCompletion
      rw [if_pos rfl, if_neg hLzero]
      unfold nullCompletionKernel
      dsimp only [su2OuterScalePair]
      simp only [htest, Bool.false_eq_true, if_false]
      rfl
  · have hLzero : L ≠ 0 := by omega
    unfold outerNullCompletion
    rw [if_neg hKzero, if_neg hLzero]
    unfold nullCompletionKernel
    dsimp only [su2OuterScalePair]
    rfl

theorem outerWholeSlabKernel_cutoff_stable_of_not_positive
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate)
    {K L : Nat} (hKL : K ≤ L)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        (su2FineOuterData G g hg K).physicalLabellings)
    (hnotPositive :
      ¬ (0 : Q') <
        (su2FineOuterData G g hg K).physicalTerm source)
    (target : EdgeLabelling) :
    outerWholeSlabKernel closure K source target ≈
      outerWholeSlabKernel closure L source target := by
  have hsourceL :=
    su2FineOuterPhysical_mem_of_le
      G g hg hKL hsource
  have htermEq :=
    su2FineOuterPhysicalTerm_cutoff_stable
      G g hg hKL hsource
  have hnotPositiveL :
      ¬ (0 : Q') <
        (su2FineOuterData G g hg L).physicalTerm source := by
    intro hpositiveL
    apply hnotPositive
    exact Q'.pos_of_lt_of_le hpositiveL
      (Q'.le_of_eqv htermEq)
  refine Q'.eqv_trans _
    (outerNullCompletion
      G g hg candidate hcandidate K source target) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (outerWholeSlabKernel_eq_null
        closure K hsource hnotPositive target)
  refine Q'.eqv_trans _
    (outerNullCompletion
      G g hg candidate hcandidate L source target) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (outerNullCompletion_cutoff_stable
        G g hg candidate hcandidate hKL hsource target)
  · exact Q'.eqv_symm
      (Q'.eqv_of_eq
        (outerWholeSlabKernel_eq_null
          closure L hsourceL hnotPositiveL target))

/-! ## 10. The one-field normalized cutoff-stability inhabitant -/

theorem outerWholeSlabKernel_cutoff_stable
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate) :
    ∀ K L source target,
      K ≤ L →
      source ∈
          (su2FineOuterData
            G g hg K).physicalLabellings →
      target ∈
          (su2CoarseOuterData
            G candidate hcandidate K).physicalLabellings →
        outerWholeSlabKernel closure K source target ≈
          outerWholeSlabKernel closure L source target := by
  intro K L source target hKL hsource htarget
  by_cases hpositive :
      (0 : Q') <
        (su2FineOuterData G g hg K).physicalTerm source
  · exact outerWholeSlabKernel_cutoff_stable_of_positive
      closure hKL hsource hpositive htarget
  · exact outerWholeSlabKernel_cutoff_stable_of_not_positive
      closure hKL hsource hpositive target

def su2OuterRawKernelCutoffStability
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate) :
    SU2OuterRawKernelCutoffStability closure where
  cutoff_stable :=
    outerWholeSlabKernel_cutoff_stable closure

def su2OuterRawKernelCutoffCoherence
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate) :
    SU2OuterRawKernelCutoffCoherence closure :=
  (su2OuterRawKernelCutoffStability closure).toCoherence

def su2OuterPhysicalMarkovContractOfPositiveRowClosure
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (closure :
      SU2OuterPositiveRowClosure
        G g hg candidate hcandidate) :
    SU2OuterPhysicalMarkovContract
      G g hg candidate hcandidate :=
  physicalMarkovContractOfRawKernelCutoffStability
    closure
    (su2OuterRawKernelCutoffStability closure)

/-! ## Axiom audit for the proved finite-support layers -/

#print axioms pairChannelStateSpace_mem_of_le
#print axioms packetPairChannelRawWeight_eqv_zero_of_not_mem
#print axioms packetPairChannelSum_cutoff_stable
#print axioms slabSpinAtPlaquette_le_of_physical
#print axioms wholeSlabFinePacket_mem_stateSpace
#print axioms su2OuterWholeSlabFaceRawWeight_cutoff_stable
#print axioms
  su2OuterWholeSlabFaceRawWeight_eqv_zero_of_above
#print axioms slabFaceLabellingBounded_of_physical
#print axioms slabExplicitLinkMultiplicity_cutoff_stable
#print axioms slabExplicitLinkMultiplicityProduct_cutoff_stable
#print axioms su2OuterLinkMultiplicityProduct_cutoff_stable
#print axioms
  su2OuterWholeSlabFaceRawProduct_cutoff_stable
#print axioms
  su2OuterWholeSlabRecouplingRawWeight_cutoff_stable
#print axioms boundedEdgeLabellings_mem_of_le
#print axioms
  su2OuterWholeSlabFaceRawProduct_old_source_no_new_target
#print axioms
  su2OuterWholeSlabRecouplingRawWeight_old_source_no_new_target
#print axioms
  su2OuterWholeSlabRawPartition_cutoff_stable
#print axioms su2FineOuterPhysicalTerm_cutoff_stable
#print axioms outerWholeSlabKernel_cutoff_stable_of_positive
#print axioms outerNullCompletion_cutoff_stable
#print axioms
  outerWholeSlabKernel_cutoff_stable_of_not_positive
#print axioms outerWholeSlabKernel_cutoff_stable
#print axioms su2OuterRawKernelCutoffStability
#print axioms su2OuterRawKernelCutoffCoherence
#print axioms
  su2OuterPhysicalMarkovContractOfPositiveRowClosure

end YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
