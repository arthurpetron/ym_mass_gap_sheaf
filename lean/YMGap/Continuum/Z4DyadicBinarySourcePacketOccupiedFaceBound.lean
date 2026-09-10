/-
# Dyadic source-packet activity is paid by fine occupied faces

The four fine faces read by distinct coarse packet fibres are disjoint: every
such fine face remembers its unique coarse face under the literal dyadic
projection.  After inverse indexing into the corrected fine slab, the union
of all packet-face identifiers is therefore duplicate-free and lies inside
the complete fine physical face list.

At cutoff one every source spin is zero or one.  Consequently the sum of all
coarse packet totals is exactly the binary occupation count on this injected
packet-face list, and is bounded by the full fine occupied-face count which
appears in the actual fine Casimir exponent.  The four-face packet family is
not asserted to cover the fine slab.

Constructive contract: explicit finite lists and exact natural arithmetic
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, enlarged heartbeat budget, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic

namespace YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Unique geometric packet fibres -/

private theorem odd_half_packet_local (coordinate : Nat) :
    (2 * coordinate + 1) / 2 = coordinate := by
  rw [Nat.mul_add_div (m := 2) (by omega) coordinate 1]
  simp

private theorem twice_ne_twice_add_one_local (coordinate : Nat) :
    2 * coordinate ≠ 2 * coordinate + 1 := by
  omega

private theorem twice_add_one_ne_twice_local (coordinate : Nat) :
    2 * coordinate + 1 ≠ 2 * coordinate := by
  omega

/-- Every member of a four-face nondegenerate fibre projects back to its
unique coarse plaquette. -/
theorem dyadicPlaquetteProjection_eq_of_mem_facePreimages
    {coarse fine : Z4Plaq} (hfine : fine ∈ dyadicFacePreimages coarse) :
    dyadicPlaquetteProjection fine = coarse := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp only [dyadicFacePreimages, List.mem_cons, List.not_mem_nil,
      or_false] at hfine <;>
    rcases hfine with rfl | rfl | rfl | rfl <;>
    simp [dyadicPlaquetteProjection, dyadicVertexProjection,
      odd_half_packet_local]

/-- The four nondegenerate fine faces above one coarse plaquette are
duplicate-free. -/
theorem dyadicFacePreimages_nodup (coarse : Z4Plaq) :
    (dyadicFacePreimages coarse).Nodup := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp only [dyadicFacePreimages, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq,
      true_and, and_true, false_and, not_false_eq_true, List.nodup_nil,
      twice_ne_twice_add_one_local, twice_add_one_ne_twice_local]

/-- Distinct coarse plaquettes have disjoint nondegenerate packet fibres. -/
theorem dyadicFacePreimages_disjoint_of_ne
    {left right : Z4Plaq} (hne : left ≠ right)
    {fine : Z4Plaq}
    (hleft : fine ∈ dyadicFacePreimages left)
    (hright : fine ∈ dyadicFacePreimages right) : False := by
  apply hne
  rw [← dyadicPlaquetteProjection_eq_of_mem_facePreimages hleft,
    ← dyadicPlaquetteProjection_eq_of_mem_facePreimages hright]

/-! ## 2. The injected fine face-identifier carrier -/

/-- All fine face identifiers actually read by the coarse packet product.
This is generally only a subset of the complete fine slab. -/
def wholeSlabDyadicPacketFineFaceIds
    (S : SlabScalePair) : List Nat :=
  S.coarse.faceEdges.flatMap (dyadicCoarseFaceFineFaceIds S)

theorem wholeSlabDyadicPacketFineFaceIds_subset_physical
    (S : SlabScalePair) {fineFaceId : Nat}
    (hface : fineFaceId ∈ wholeSlabDyadicPacketFineFaceIds S) :
    fineFaceId ∈ S.fine.faceEdges := by
  unfold wholeSlabDyadicPacketFineFaceIds at hface
  obtain ⟨coarseFaceId, hcoarseFaceId, hfineFaceId⟩ :=
    List.mem_flatMap.mp hface
  unfold dyadicCoarseFaceFineFaceIds at hfineFaceId
  obtain ⟨finePlaquette, hpreimage, rfl⟩ :=
    List.mem_map.mp hfineFaceId
  have hcoarsePlaquette := slabPlaquetteAt_mem hcoarseFaceId
  have hfinePlaquette := dyadicFacePreimage_mem_boundaryCompleteFineSlab
    hcoarsePlaquette hpreimage
  apply slabFaceIdOfPlaquette_physical
  rw [S.fine_extent]
  exact hfinePlaquette

theorem dyadicCoarseFaceFineFaceIds_nodup
    (S : SlabScalePair) (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    (dyadicCoarseFaceFineFaceIds S coarseFaceId).Nodup := by
  unfold dyadicCoarseFaceFineFaceIds
  apply nodup_map_of_injOn (slabFaceIdOfPlaquette S.fine.extent)
  · exact dyadicFacePreimages_nodup _
  · intro left hleft right hright heq
    have hcoarsePlaquette := slabPlaquetteAt_mem hcoarseFaceId
    have hleftBoundary : left ∈
        boundaryCompleteSlabPlaquettes S.fine.extent := by
      rw [S.fine_extent]
      exact dyadicFacePreimage_mem_boundaryCompleteFineSlab
        hcoarsePlaquette hleft
    have hrightBoundary : right ∈
        boundaryCompleteSlabPlaquettes S.fine.extent := by
      rw [S.fine_extent]
      exact dyadicFacePreimage_mem_boundaryCompleteFineSlab
        hcoarsePlaquette hright
    have hplaquette := congrArg
      (slabPlaquetteAt S.fine.extent) heq
    rw [slabPlaquetteAt_faceIdOfPlaquette hleftBoundary,
      slabPlaquetteAt_faceIdOfPlaquette hrightBoundary] at hplaquette
    exact hplaquette

theorem wholeSlabDyadicPacketFineFaceIds_nodup_on
    (S : SlabScalePair) : ∀ coarseFaceIds : List Nat,
    coarseFaceIds.Nodup →
    (∀ faceId, faceId ∈ coarseFaceIds →
      faceId ∈ S.coarse.faceEdges) →
    (coarseFaceIds.flatMap
      (dyadicCoarseFaceFineFaceIds S)).Nodup
  | [], _, _ => List.nodup_nil
  | coarseFaceId :: rest, hnodup, hphysical => by
      have hparts := List.nodup_cons.mp hnodup
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨
        dyadicCoarseFaceFineFaceIds_nodup S coarseFaceId
          (hphysical coarseFaceId List.mem_cons_self),
        wholeSlabDyadicPacketFineFaceIds_nodup_on S rest hparts.2
          (fun faceId hfaceId =>
            hphysical faceId (List.mem_cons_of_mem coarseFaceId hfaceId)),
        ?_⟩
      intro fineFaceId hleft otherFineFaceId hright heq
      unfold dyadicCoarseFaceFineFaceIds at hleft
      obtain ⟨leftPlaquette, hleftPreimage, hleftId⟩ :=
        List.mem_map.mp hleft
      obtain ⟨otherCoarseFaceId, hotherCoarseFaceId, hother⟩ :=
        List.mem_flatMap.mp hright
      unfold dyadicCoarseFaceFineFaceIds at hother
      obtain ⟨rightPlaquette, hrightPreimage, hrightId⟩ :=
        List.mem_map.mp hother
      have hcoarsePhysical :=
        hphysical coarseFaceId List.mem_cons_self
      have hotherPhysical := hphysical otherCoarseFaceId
        (List.mem_cons_of_mem coarseFaceId hotherCoarseFaceId)
      have hleftBoundary : leftPlaquette ∈
          boundaryCompleteSlabPlaquettes S.fine.extent := by
        rw [S.fine_extent]
        exact dyadicFacePreimage_mem_boundaryCompleteFineSlab
          (slabPlaquetteAt_mem hcoarsePhysical) hleftPreimage
      have hrightBoundary : rightPlaquette ∈
          boundaryCompleteSlabPlaquettes S.fine.extent := by
        rw [S.fine_extent]
        exact dyadicFacePreimage_mem_boundaryCompleteFineSlab
          (slabPlaquetteAt_mem hotherPhysical) hrightPreimage
      have hid : slabFaceIdOfPlaquette S.fine.extent leftPlaquette =
          slabFaceIdOfPlaquette S.fine.extent rightPlaquette := by
        rw [hleftId, hrightId]
        exact heq
      have hplaquette := congrArg (slabPlaquetteAt S.fine.extent) hid
      rw [slabPlaquetteAt_faceIdOfPlaquette hleftBoundary,
        slabPlaquetteAt_faceIdOfPlaquette hrightBoundary] at hplaquette
      have hcoarsePlaquette :
          slabPlaquetteAt S.coarse.extent coarseFaceId =
            slabPlaquetteAt S.coarse.extent otherCoarseFaceId := by
        rw [← dyadicPlaquetteProjection_eq_of_mem_facePreimages
            hleftPreimage,
          ← dyadicPlaquetteProjection_eq_of_mem_facePreimages
            hrightPreimage,
          hplaquette]
      have hcoarseId := slabPlaquetteAt_injective_on_physical
        hcoarsePhysical hotherPhysical hcoarsePlaquette
      subst otherCoarseFaceId
      exact hparts.1 hotherCoarseFaceId

private theorem range_nodup_local : ∀ count : Nat,
    (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      exact ⟨range_nodup_local count,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun left hleft right hright heq => by
          have hrightEq : right = count := List.mem_singleton.mp hright
          rw [heq, hrightEq] at hleft
          exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)⟩

theorem wholeSlabDyadicPacketFineFaceIds_nodup
    (S : SlabScalePair) :
    (wholeSlabDyadicPacketFineFaceIds S).Nodup := by
  unfold wholeSlabDyadicPacketFineFaceIds
  apply wholeSlabDyadicPacketFineFaceIds_nodup_on
  · exact range_nodup_local _
  · intro faceId hfaceId
    exact hfaceId

/-! ## 3. Packet totals are the injected fine-spin sum -/

private theorem faceSpinPacketTotal_dyadicFaceSpinPacket
    (fineSpin : Z4Plaq → Nat) (coarse : Z4Plaq) :
    faceSpinPacketTotal (dyadicFaceSpinPacket fineSpin coarse) =
      listNatWeight fineSpin (dyadicFacePreimages coarse) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [faceSpinPacketTotal, dyadicFaceSpinPacket,
      dyadicFacePreimages, listNatWeight] <;> omega

private theorem listNatWeight_congr_local {A : Type}
    (first second : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → first item = second item) →
      listNatWeight first items = listNatWeight second items
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [listNatWeight]
      rw [hagree head List.mem_cons_self]
      rw [listNatWeight_congr_local first second tail (fun item hitem =>
        hagree item (List.mem_cons_of_mem head hitem))]

theorem wholeSlabFinePacketTotal_eq_fineFaceIdWeight
    (S : SlabScalePair) (source : EdgeLabelling)
    (coarseFaceId : Nat)
    (hcoarseFaceId : coarseFaceId ∈ S.coarse.faceEdges) :
    wholeSlabFinePacketTotalLabelling S source coarseFaceId =
      listNatWeight source
        (dyadicCoarseFaceFineFaceIds S coarseFaceId) := by
  unfold wholeSlabFinePacketTotalLabelling wholeSlabFinePacket
  rw [faceSpinPacketTotal_dyadicFaceSpinPacket]
  unfold dyadicCoarseFaceFineFaceIds
  rw [listNatWeight_map]
  apply listNatWeight_congr_local
  intro finePlaquette hpreimage
  have hcoarsePlaquette := slabPlaquetteAt_mem hcoarseFaceId
  have hfinePlaquette : finePlaquette ∈
      boundaryCompleteSlabPlaquettes S.fine.extent := by
    rw [S.fine_extent]
    exact dyadicFacePreimage_mem_boundaryCompleteFineSlab
      hcoarsePlaquette hpreimage
  rw [slabSpinAtPlaquette_eq_of_mem hfinePlaquette]
  rfl

private theorem wholeSlabFinePacketTotalMass_eq_injectedFineWeight_on
    (S : SlabScalePair) (source : EdgeLabelling) :
    ∀ coarseFaceIds : List Nat,
    (∀ faceId, faceId ∈ coarseFaceIds →
      faceId ∈ S.coarse.faceEdges) →
    listNatWeight (wholeSlabFinePacketTotalLabelling S source)
        coarseFaceIds =
      listNatWeight source
        (coarseFaceIds.flatMap (dyadicCoarseFaceFineFaceIds S))
  | [], _ => rfl
  | coarseFaceId :: rest, hphysical => by
      have hhead := hphysical coarseFaceId List.mem_cons_self
      have hrest : ∀ faceId, faceId ∈ rest →
          faceId ∈ S.coarse.faceEdges := by
        intro faceId hfaceId
        exact hphysical faceId
          (List.mem_cons_of_mem coarseFaceId hfaceId)
      simp only [listNatWeight, List.flatMap_cons,
        listNatWeight_append]
      rw [wholeSlabFinePacketTotal_eq_fineFaceIdWeight S source
        coarseFaceId hhead]
      rw [wholeSlabFinePacketTotalMass_eq_injectedFineWeight_on
        S source rest hrest]

theorem wholeSlabFinePacketTotalMass_eq_injectedFineWeight
    (S : SlabScalePair) (source : EdgeLabelling) :
    listNatWeight (wholeSlabFinePacketTotalLabelling S source)
        S.coarse.faceEdges =
      listNatWeight source (wholeSlabDyadicPacketFineFaceIds S) := by
  unfold wholeSlabDyadicPacketFineFaceIds
  exact wholeSlabFinePacketTotalMass_eq_injectedFineWeight_on
    S source S.coarse.faceEdges (fun _faceId hfaceId => hfaceId)

/-! ## 4. Binary injected weight is bounded by full occupation -/

private theorem mem_of_mem_slabCutoffOneOccupiedFaces
    (physical : EdgeLabelling) : ∀ {faces : List Nat} {faceId : Nat},
    faceId ∈ slabCutoffOneOccupiedFaces physical faces →
      faceId ∈ faces
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, faceId, hmem => by
      by_cases hhead : physical head = 1
      · simp only [slabCutoffOneOccupiedFaces, hhead, if_true,
          List.mem_cons] at hmem
        rcases hmem with rfl | hrest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem head
            (mem_of_mem_slabCutoffOneOccupiedFaces physical hrest)
      · simp only [slabCutoffOneOccupiedFaces, hhead, if_false] at hmem
        exact List.mem_cons_of_mem head
          (mem_of_mem_slabCutoffOneOccupiedFaces physical hmem)

private theorem slabCutoffOneOccupiedFaces_nodup
    (physical : EdgeLabelling) : ∀ {faces : List Nat},
    faces.Nodup → (slabCutoffOneOccupiedFaces physical faces).Nodup
  | [], _ => List.nodup_nil
  | head :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : physical head = 1
      · simp only [slabCutoffOneOccupiedFaces, hhead, if_true]
        apply List.nodup_cons.mpr
        refine ⟨?_, slabCutoffOneOccupiedFaces_nodup physical hparts.2⟩
        intro hmem
        exact hparts.1
          (mem_of_mem_slabCutoffOneOccupiedFaces physical hmem)
      · simp only [slabCutoffOneOccupiedFaces, hhead, if_false]
        exact slabCutoffOneOccupiedFaces_nodup physical hparts.2

private theorem listNatWeight_eq_occupiedLength_of_binary
    (physical : EdgeLabelling) : ∀ faces : List Nat,
    (∀ faceId, faceId ∈ faces →
      physical faceId = 0 ∨ physical faceId = 1) →
    listNatWeight physical faces =
      (slabCutoffOneOccupiedFaces physical faces).length
  | [], _ => rfl
  | head :: rest, hbinary => by
      have hhead := hbinary head List.mem_cons_self
      have hrest : ∀ faceId, faceId ∈ rest →
          physical faceId = 0 ∨ physical faceId = 1 := by
        intro faceId hfaceId
        exact hbinary faceId (List.mem_cons_of_mem head hfaceId)
      have ih := listNatWeight_eq_occupiedLength_of_binary
        physical rest hrest
      rcases hhead with hzero | hone
      · simp only [listNatWeight, slabCutoffOneOccupiedFaces,
          hzero, Nat.zero_ne_one, if_false, Nat.zero_add]
        exact ih
      · simp only [listNatWeight, slabCutoffOneOccupiedFaces,
          hone, if_true, List.length_cons]
        omega

private theorem occupiedLength_le_of_nodup_mem
    (physical : EdgeLabelling) (source target : List Nat)
    (hsourceNodup : source.Nodup)
    (hsourceMem : ∀ faceId, faceId ∈ source → faceId ∈ target) :
    (slabCutoffOneOccupiedFaces physical source).length ≤
      (slabCutoffOneOccupiedFaces physical target).length := by
  have hoccupiedNodup := slabCutoffOneOccupiedFaces_nodup
    physical hsourceNodup
  have hoccupiedMem : ∀ faceId,
      faceId ∈ slabCutoffOneOccupiedFaces physical source →
        faceId ∈ slabCutoffOneOccupiedFaces physical target := by
    intro faceId hfaceId
    have hsource := mem_of_mem_slabCutoffOneOccupiedFaces
      physical hfaceId
    have hone := mem_slabCutoffOneOccupiedFaces_spin_one
      physical source faceId hfaceId
    exact mem_slabCutoffOneOccupiedFaces_of_mem_of_spin_one
      physical target faceId (hsourceMem faceId hsource) hone
  have hweight := listNatWeight_le_of_nodup_mem
    (fun _faceId : Nat => 1)
    (slabCutoffOneOccupiedFaces physical source)
    (slabCutoffOneOccupiedFaces physical target)
    hoccupiedNodup hoccupiedMem
  have listNatWeight_one_eq_length : ∀ items : List Nat,
      listNatWeight (fun _faceId : Nat => 1) items = items.length := by
    intro items
    induction items with
    | nil => rfl
    | cons _head rest ih =>
        simp only [listNatWeight, List.length_cons]
        rw [ih]
        omega
  rw [listNatWeight_one_eq_length,
    listNatWeight_one_eq_length] at hweight
  exact hweight

/-- The total source occupation visible to all coarse dyadic packets is at
most the full fine occupied-face count in the actual source heat exponent. -/
theorem wholeSlabFinePacketTotalMass_le_occupiedFaceCount
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings) :
    listNatWeight (wholeSlabFinePacketTotalLabelling S source)
        S.coarse.faceEdges ≤
      fineCouplingPhysicalOccupiedFaceCount S source := by
  rw [wholeSlabFinePacketTotalMass_eq_injectedFineWeight]
  rw [listNatWeight_eq_occupiedLength_of_binary]
  · unfold fineCouplingPhysicalOccupiedFaceCount
    exact occupiedLength_le_of_nodup_mem source
      (wholeSlabDyadicPacketFineFaceIds S)
      (slabPhysicalFaceEdges S.fine.extent)
      (wholeSlabDyadicPacketFineFaceIds_nodup S)
      (fun faceId hfaceId =>
        wholeSlabDyadicPacketFineFaceIds_subset_physical S hfaceId)
  · intro faceId hfaceId
    exact finePhysicalFaceSpin_zero_or_one S hfineCutoff source hsource
      faceId
      (wholeSlabDyadicPacketFineFaceIds_subset_physical S hfaceId)

/-! ## 5. Both oriented sources are paid without multiplicity -/

def finePacketOrientedTotalSourceActivity
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) : Nat :=
  listNatWeight
    (fun faceId =>
      finePacketOrientedLeftSource S orientation first second faceId +
        finePacketOrientedRightSource S orientation first second faceId)
    S.coarse.faceEdges

private theorem listNatWeight_add_local {A : Type}
    (first second : A → Nat) : ∀ items : List A,
    listNatWeight (fun item => first item + second item) items =
      listNatWeight first items + listNatWeight second items
  | [] => rfl
  | _head :: rest => by
      simp only [listNatWeight]
      rw [listNatWeight_add_local first second rest]
      omega

theorem finePacketOrientedTotalSourceActivity_le_occupiedFaceCounts
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    finePacketOrientedTotalSourceActivity
        S orientation first.1 second.1 ≤
      fineCouplingPhysicalOccupiedFaceCount S first.1 +
        fineCouplingPhysicalOccupiedFaceCount S second.1 := by
  unfold finePacketOrientedTotalSourceActivity
  rw [listNatWeight_add_local]
  cases orientation with
  | forward =>
      exact Nat.add_le_add
        (wholeSlabFinePacketTotalMass_le_occupiedFaceCount
          S hfineCutoff first.1 first.2.1)
        (wholeSlabFinePacketTotalMass_le_occupiedFaceCount
          S hfineCutoff second.1 second.2.1)
  | reverse =>
      change
        listNatWeight (wholeSlabFinePacketTotalLabelling S second.1)
              S.coarse.faceEdges +
            listNatWeight (wholeSlabFinePacketTotalLabelling S first.1)
              S.coarse.faceEdges ≤
          fineCouplingPhysicalOccupiedFaceCount S first.1 +
            fineCouplingPhysicalOccupiedFaceCount S second.1
      have hsecond := wholeSlabFinePacketTotalMass_le_occupiedFaceCount
        S hfineCutoff second.1 second.2.1
      have hfirst := wholeSlabFinePacketTotalMass_le_occupiedFaceCount
        S hfineCutoff first.1 first.2.1
      omega

/-! ## 6. Axiom audit -/

#print axioms dyadicPlaquetteProjection_eq_of_mem_facePreimages
#print axioms dyadicFacePreimages_nodup
#print axioms dyadicFacePreimages_disjoint_of_ne
#print axioms wholeSlabDyadicPacketFineFaceIds
#print axioms wholeSlabDyadicPacketFineFaceIds_subset_physical
#print axioms dyadicCoarseFaceFineFaceIds_nodup
#print axioms wholeSlabDyadicPacketFineFaceIds_nodup_on
#print axioms wholeSlabDyadicPacketFineFaceIds_nodup
#print axioms wholeSlabFinePacketTotal_eq_fineFaceIdWeight
#print axioms wholeSlabFinePacketTotalMass_eq_injectedFineWeight
#print axioms wholeSlabFinePacketTotalMass_le_occupiedFaceCount
#print axioms finePacketOrientedTotalSourceActivity
#print axioms finePacketOrientedTotalSourceActivity_le_occupiedFaceCounts

end YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
