/-
# Reflection of the whole corrected-slab recoupling carrier

This module proves that the globally link-glued raw recoupling carrier
commutes with the corrected-slab half-time reflection.

The proof has three finite reindexing layers:

* the zero-extended numerical fine labelling agrees with geometric
  reflection on every dyadic child queried by a physical coarse face;
* the two internal pair channels are permuted by their involutive reflection;
* the complete coarse-face product and complete coarse-link product are
  permuted by the corrected-slab face and link reflections.

The result is the equality needed to complete zero-mass rows symmetrically
without changing the positive physical recoupling rows.

## Axiom gate

Finite list and exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel

namespace YMGap.Continuum.CompactDualWholeSlabRecouplingReflection

set_option maxRecDepth 30000
set_option maxHeartbeats 300000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fine packet reflection on the actual corrected slab -/

theorem slabSpinAtPlaquette_supported_reflection_inside
    (extent : Nat) (physical : EdgeLabelling)
    {plaquette : Z4Plaq}
    (hplaquette :
      plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    slabSpinAtPlaquette extent
        (reflectSupportedSlabFaceLabelling extent physical) plaquette =
      slabSpinAtPlaquette extent physical
        (timeReflectPlaquette extent plaquette) := by
  have hreflected :=
    timeReflectPlaquette_mem_boundaryCompleteSlab hplaquette
  rw [slabSpinAtPlaquette_eq_of_mem hplaquette,
    slabSpinAtPlaquette_eq_of_mem hreflected]
  have hindex :
      listIndexOf plaquette
          (boundaryCompleteSlabPlaquettes extent) ∈
        slabPhysicalFaceEdges extent := by
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr
      (listIndexOf_lt_of_mem plaquette
        (boundaryCompleteSlabPlaquettes extent) hplaquette)
  rw [reflectSupportedSlabFaceLabelling_eq_on_physical
    extent physical hindex]
  unfold reflectSlabFaceLabelling slabFaceReflectId
  have hlookup :
      slabPlaquetteAt extent
          (listIndexOf plaquette
            (boundaryCompleteSlabPlaquettes extent)) = plaquette := by
    unfold slabPlaquetteAt
    exact getD_listIndexOf_of_mem fallbackPlaquette plaquette
      (boundaryCompleteSlabPlaquettes extent) hplaquette
  rw [hlookup]

private theorem dyadicFaceSpinPacket_congr_on_preimages
    (left right : Z4Plaq → Nat) (coarsePlaquette : Z4Plaq)
    (hagree : ∀ finePlaquette,
      finePlaquette ∈ dyadicFacePreimages coarsePlaquette →
        left finePlaquette = right finePlaquette) :
    dyadicFaceSpinPacket left coarsePlaquette =
      dyadicFaceSpinPacket right coarsePlaquette := by
  let fibre := dyadicFacePreimages coarsePlaquette
  have hlength : fibre.length = 4 := by
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
    cases plane <;> rfl
  have hmem : ∀ i, i < 4 →
      fibre.getD i fallbackPlaquette ∈ fibre := by
    intro i hi
    have hifibre : i < fibre.length := by omega
    rw [← List.getElem_eq_getD
      (l := fibre) (i := i) (h := hifibre) fallbackPlaquette]
    exact List.getElem_mem hifibre
  have h0 := hagree _ (hmem 0 (by decide))
  have h1 := hagree _ (hmem 1 (by decide))
  have h2 := hagree _ (hmem 2 (by decide))
  have h3 := hagree _ (hmem 3 (by decide))
  unfold dyadicFaceSpinPacket
  change
    (⟨left (fibre.getD 0 fallbackPlaquette),
        left (fibre.getD 1 fallbackPlaquette),
        left (fibre.getD 2 fallbackPlaquette),
        left (fibre.getD 3 fallbackPlaquette)⟩ : FaceSpinPacket) =
      ⟨right (fibre.getD 0 fallbackPlaquette),
        right (fibre.getD 1 fallbackPlaquette),
        right (fibre.getD 2 fallbackPlaquette),
        right (fibre.getD 3 fallbackPlaquette)⟩
  rw [h0, h1, h2, h3]

theorem wholeSlabFinePacket_reflection
    (S : SlabScalePair) {fineState : EdgeLabelling}
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈ S.coarse.faceEdges) :
    wholeSlabFinePacket S
        (S.fine.reflectLabelling fineState) coarseFaceId =
      reflectFaceSpinPacket
        (slabPlaquetteAt S.coarse.extent coarseFaceId).2
        (wholeSlabFinePacket S fineState
          (slabFaceReflectId S.coarse.extent coarseFaceId)) := by
  let coarsePlaquette :=
    slabPlaquetteAt S.coarse.extent coarseFaceId
  have hcoarse :
      coarsePlaquette ∈
        boundaryCompleteSlabPlaquettes S.coarse.extent :=
    slabPlaquetteAt_mem hface
  have hadmissible :=
    ((mem_boundaryCompleteSlabPlaquettes
      S.coarse.extent coarsePlaquette).mp hcoarse).2
  have hpacketCongr :
      dyadicFaceSpinPacket
          (slabSpinAtPlaquette S.fine.extent
            (S.fine.reflectLabelling fineState))
          coarsePlaquette =
        dyadicFaceSpinPacket
          (reflectSlabFaceSpinLabelling
            (dyadicSlabFineExtent S.coarse.extent)
            (slabSpinAtPlaquette S.fine.extent fineState))
          coarsePlaquette := by
    apply dyadicFaceSpinPacket_congr_on_preimages
    intro finePlaquette hpreimage
    have hfine :
        finePlaquette ∈
          boundaryCompleteSlabPlaquettes S.fine.extent := by
      rw [S.fine_extent]
      exact dyadicFacePreimage_mem_boundaryCompleteFineSlab
        hcoarse hpreimage
    unfold SlabPhysicalData.reflectLabelling
    rw [slabSpinAtPlaquette_supported_reflection_inside
      S.fine.extent fineState hfine]
    unfold reflectSlabFaceSpinLabelling
    rw [S.fine_extent]
  unfold wholeSlabFinePacket
  rw [hpacketCongr]
  have hreflection :=
    dyadicFaceSpinPacket_reflection
      S.coarse.extent
      (slabSpinAtPlaquette S.fine.extent fineState)
      coarsePlaquette hadmissible
  rw [hreflection]
  unfold coarsePlaquette
  rw [slabPlaquetteAt_slabFaceReflectId hface]

/-! ## 2. The complete fixed-final face sum is reflected -/

private theorem perm_of_nodup_mem_iff_local {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      cases (hmem head).2 List.mem_cons_self
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ :=
        List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm :=
        perm_of_nodup_mem_iff_local tail (before ++ after)
          hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

private theorem reflectPairChannelState_injective (plane : Z4Plane) :
    Function.Injective (reflectPairChannelState plane) := by
  intro left right heq
  have htwice := congrArg (reflectPairChannelState plane) heq
  simpa only [reflectPairChannelState_involutive] using htwice

private theorem nodup_map_of_injective_local {A B : Type}
    (reindex : A → B) (hinjective : Function.Injective reindex) :
    ∀ {entries : List A}, entries.Nodup →
      (entries.map reindex).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
        have hsourceEq : source = head :=
          hinjective (heq.trans rfl)
        subst source
        exact hparts.1 hsource
      · exact nodup_map_of_injective_local reindex hinjective hparts.2

private theorem mem_cartesian_iff_local {A B : Type}
    (xs : List A) (ys : List B) (pair : A × B) :
    pair ∈ cartesian xs ys ↔ pair.1 ∈ xs ∧ pair.2 ∈ ys := by
  induction xs with
  | nil => simp [cartesian]
  | cons head tail ih =>
      unfold cartesian
      rw [List.flatMap_cons, List.mem_append]
      constructor
      · intro hmem
        rcases hmem with hhead | htail
        · obtain ⟨second, hsecond, heq⟩ := List.mem_map.mp hhead
          rw [← heq]
          exact ⟨List.mem_cons_self, hsecond⟩
        · have hparts := ih.mp htail
          exact ⟨List.mem_cons_of_mem head hparts.1, hparts.2⟩
      · intro hparts
        rcases List.mem_cons.mp hparts.1 with hhead | htail
        · obtain ⟨first, second⟩ := pair
          change first = head at hhead
          subst first
          exact Or.inl (List.mem_map.mpr
            ⟨second, hparts.2, rfl⟩)
        · exact Or.inr (ih.mpr ⟨htail, hparts.2⟩)

private theorem reflectPairChannelState_mem_local
    {cutoff : Nat} {state : PairChannelState}
    (hstate : state ∈ pairChannelStateSpace cutoff)
    (plane : Z4Plane) :
    reflectPairChannelState plane state ∈
      pairChannelStateSpace cutoff := by
  unfold pairChannelStateSpace at hstate ⊢
  have hparts :=
    (mem_cartesian_iff_local
      (cartesian (List.range (2 * cutoff + 1))
        (List.range (2 * cutoff + 1)))
      (List.range (4 * cutoff + 1)) state).mp hstate
  have hpairs :=
    (mem_cartesian_iff_local
      (List.range (2 * cutoff + 1))
      (List.range (2 * cutoff + 1)) state.1).mp hparts.1
  apply (mem_cartesian_iff_local
    (cartesian (List.range (2 * cutoff + 1))
      (List.range (2 * cutoff + 1)))
    (List.range (4 * cutoff + 1)) _).mpr
  constructor
  · apply (mem_cartesian_iff_local
      (List.range (2 * cutoff + 1))
      (List.range (2 * cutoff + 1)) _).mpr
    cases plane with
    | p01 => exact ⟨hpairs.2, hpairs.1⟩
    | p02 => exact ⟨hpairs.2, hpairs.1⟩
    | p03 => exact hpairs
    | p12 => exact ⟨hpairs.2, hpairs.1⟩
    | p13 => exact hpairs
    | p23 => exact hpairs
  · cases plane <;> exact hparts.2

theorem reflectPairChannelState_space_perm
    (cutoff : Nat) (plane : Z4Plane) :
    ((pairChannelStateSpace cutoff).map
      (reflectPairChannelState plane)).Perm
        (pairChannelStateSpace cutoff) := by
  apply perm_of_nodup_mem_iff_local
  · exact nodup_map_of_injective_local
      (reflectPairChannelState plane)
      (reflectPairChannelState_injective plane)
      (pairChannelStateSpace_nodup cutoff)
  · exact pairChannelStateSpace_nodup cutoff
  · intro state
    constructor
    · intro hmem
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
      rw [← heq]
      exact reflectPairChannelState_mem_local hsource plane
    · intro hmem
      apply List.mem_map.mpr
      refine ⟨reflectPairChannelState plane state,
        reflectPairChannelState_mem_local hmem plane, ?_⟩
      exact reflectPairChannelState_involutive plane state

private theorem reflectPairChannelState_final
    (plane : Z4Plane) (state : PairChannelState) :
    (reflectPairChannelState plane state).2 = state.2 := by
  cases plane <;> rfl

theorem wholeSlabFaceRawWeight_reflection
    (S : SlabScalePair)
    {fineState coarseState : EdgeLabelling}
    {coarseFaceId : Nat}
    (hface : coarseFaceId ∈ S.coarse.faceEdges) :
    wholeSlabFaceRawWeight S
        (S.fine.reflectLabelling fineState)
        (S.coarse.reflectLabelling coarseState)
        coarseFaceId ≈
      wholeSlabFaceRawWeight S fineState coarseState
        (slabFaceReflectId S.coarse.extent coarseFaceId) := by
  let plane :=
    (slabPlaquetteAt S.coarse.extent coarseFaceId).2
  let reflectedPacket :=
    wholeSlabFinePacket S
      (S.fine.reflectLabelling fineState) coarseFaceId
  let sourcePacket :=
    wholeSlabFinePacket S fineState
      (slabFaceReflectId S.coarse.extent coarseFaceId)
  let reflectedFinal :=
    S.coarse.reflectLabelling coarseState coarseFaceId
  let sourceFinal :=
    coarseState (slabFaceReflectId S.coarse.extent coarseFaceId)
  have hpacket :
      reflectedPacket = reflectFaceSpinPacket plane sourcePacket := by
    exact wholeSlabFinePacket_reflection S hface
  have hfinal : reflectedFinal = sourceFinal := by
    unfold reflectedFinal sourceFinal
      SlabPhysicalData.reflectLabelling
    exact reflectSupportedSlabFaceLabelling_eq_on_physical
      S.coarse.extent coarseState hface
  let leftWeight : PairChannelState → Q' :=
    fun channel =>
      if channel.2 = reflectedFinal then
        packetPairChannelRawWeight S.coarse.coupling
          reflectedPacket channel
      else 0
  let rightWeight : PairChannelState → Q' :=
    fun channel =>
      if channel.2 = sourceFinal then
        packetPairChannelRawWeight S.coarse.coupling
          sourcePacket channel
      else 0
  have hterm : ∀ channel,
      channel ∈ pairChannelStateSpace S.fine.cutoff →
        leftWeight (reflectPairChannelState plane channel) ≈
          rightWeight channel := by
    intro channel _
    unfold leftWeight rightWeight
    rw [hpacket, hfinal,
      reflectPairChannelState_final plane channel]
    by_cases hchannel : channel.2 = sourceFinal
    · rw [if_pos hchannel, if_pos hchannel]
      exact packetPairChannelRawWeight_reflection
        S.coarse.coupling plane sourcePacket channel
    · rw [if_neg hchannel, if_neg hchannel]
      exact Q'.eqv_refl 0
  unfold wholeSlabFaceRawWeight
  change listQSum leftWeight
      (pairChannelStateSpace S.fine.cutoff) ≈
    listQSum rightWeight
      (pairChannelStateSpace S.fine.cutoff)
  refine Q'.eqv_trans _
    (listQSum leftWeight
      ((pairChannelStateSpace S.fine.cutoff).map
        (reflectPairChannelState plane))) _ ?_ ?_
  · exact listQSum_perm leftWeight
      (reflectPairChannelState_space_perm
        S.fine.cutoff plane).symm
  · rw [listQSum_map]
    exact listQSum_congr_on _ _
      (pairChannelStateSpace S.fine.cutoff) hterm

/-! ## 3. Whole face product, link product, and raw carrier -/

theorem wholeSlabFaceRawProduct_reflection
    (S : SlabScalePair)
    {fineState coarseState : EdgeLabelling} :
    wholeSlabFaceRawProduct S
        (S.fine.reflectLabelling fineState)
        (S.coarse.reflectLabelling coarseState) ≈
      wholeSlabFaceRawProduct S fineState coarseState := by
  apply wholeSlabFaceRawProduct_eqv_of_reindex S
    (S.fine.reflectLabelling fineState)
    (S.coarse.reflectLabelling coarseState)
    fineState coarseState
    (slabFaceReflectId S.coarse.extent)
  · exact slabFaceReflectId_range_perm S.coarse.extent
  · intro faceId hface
    exact wholeSlabFaceRawWeight_reflection S hface

private theorem slabLinkMultiplicityProduct_supported_eq_rawReflection
    (D : SlabPhysicalData) (physical : EdgeLabelling) :
    slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent (D.reflectLabelling physical) =
      slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent
          (reflectSlabFaceLabelling D.extent physical) := by
  unfold slabExplicitLinkMultiplicityProduct
  apply natListProduct_congr
  intro link _
  have hspins :
      (slabIncidentPlaqIds D.extent link).map
          (D.reflectLabelling physical) =
        (slabIncidentPlaqIds D.extent link).map
          (reflectSlabFaceLabelling D.extent physical) := by
    apply List.map_congr_left
    intro id hid
    exact reflectSupportedSlabFaceLabelling_eq_on_physical
      D.extent physical (slabIncidentPlaqId_physical hid)
  unfold slabExplicitLinkMultiplicity
  rw [hspins]

theorem slabLinkMultiplicityProduct_supported_reflection
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent (D.reflectLabelling physical) =
      slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent physical := by
  rw [slabLinkMultiplicityProduct_supported_eq_rawReflection]
  exact slabExplicitLinkMultiplicityProduct_reflection
    (fun id hid =>
      Nat.le_of_lt_succ
        ((boundedEdgeLabellings_sound
          D.cutoff D.faceEdges physical hphysical).1 id hid))

theorem wholeSlabRecouplingRawWeight_reflection
    (S : SlabScalePair)
    {fineState coarseState : EdgeLabelling}
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    wholeSlabRecouplingRawWeight S
        (S.fine.reflectLabelling fineState)
        (S.coarse.reflectLabelling coarseState) ≈
      wholeSlabRecouplingRawWeight S fineState coarseState := by
  unfold wholeSlabRecouplingRawWeight
  rw [slabLinkMultiplicityProduct_supported_reflection
    S.coarse hcoarse]
  apply Q'.mul_eqv_congr_right
  exact wholeSlabFaceRawProduct_reflection S

#print axioms slabSpinAtPlaquette_supported_reflection_inside
#print axioms wholeSlabFinePacket_reflection
#print axioms perm_of_nodup_mem_iff_local
#print axioms reflectPairChannelState_injective
#print axioms nodup_map_of_injective_local
#print axioms pairChannelStateSpace_nodup
#print axioms mem_cartesian_iff_local
#print axioms reflectPairChannelState_mem_local
#print axioms reflectPairChannelState_space_perm
#print axioms wholeSlabFaceRawWeight_reflection
#print axioms wholeSlabFaceRawProduct_reflection
#print axioms slabLinkMultiplicityProduct_supported_reflection
#print axioms wholeSlabRecouplingRawWeight_reflection

end YMGap.Continuum.CompactDualWholeSlabRecouplingReflection
