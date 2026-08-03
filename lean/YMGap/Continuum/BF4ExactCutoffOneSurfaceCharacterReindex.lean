import YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

/-
# Exact cutoff-one BF4 character expansion onto closed binary surfaces

This module proves the first half of the actual `Haar_5` surface bridge.  It
never enumerates the `2^72` cutoff-one face carrier.  Instead it encodes a
bounded labelling as a 72-bit mask, annihilates every odd-incidence term by
selected-link quaternion Fubini, invokes the rank-65 closure certificate, and
uses literal list permutations to identify every surviving term exactly once
with the 128 embedded closed surfaces.  The same construction restricted to
the vacuum lower row leaves exactly its two certified surfaces.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
`noncomputable` declaration is used.
-/

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup

local infix:50 " ≈ " => Q'.eqv

def cutoffOneSlabMaskFrom (physical : EdgeLabelling) : Nat -> Nat
  | 0 => 0
  | width + 1 =>
      Nat.bitwise (fun left right => left || right)
        (cutoffOneSlabMaskFrom physical width)
        (if physical width = 1 then 2 ^ width else 0)

theorem cutoffOneSlabMaskFrom_lt (physical : EdgeLabelling) :
    forall width, cutoffOneSlabMaskFrom physical width < 2 ^ width
  | 0 => by simp [cutoffOneSlabMaskFrom]
  | width + 1 => by
      unfold cutoffOneSlabMaskFrom
      apply Nat.bitwise_lt_two_pow
      · have hpow : 2 ^ width < 2 ^ (width + 1) := by
          rw [Nat.pow_succ]
          have hpos := Nat.two_pow_pos width
          omega
        exact Nat.lt_trans (cutoffOneSlabMaskFrom_lt physical width) hpow
      · split
        · rw [Nat.pow_succ]
          have hpos := Nat.two_pow_pos width
          omega
        · exact Nat.two_pow_pos (width + 1)

theorem cutoffOneSlabMaskFrom_testBit (physical : EdgeLabelling) :
    forall width index, index < width ->
      (cutoffOneSlabMaskFrom physical width).testBit index =
        decide (physical index = 1)
  | 0, _, hindex => by omega
  | width + 1, index, hindex => by
      simp only [cutoffOneSlabMaskFrom,
        Nat.testBit_bitwise (f := fun left right => left || right) (by decide)]
      by_cases hlabel : physical width = 1
      · rw [if_pos hlabel, Nat.testBit_two_pow]
        by_cases heq : index = width
        · subst index
          rw [Nat.testBit_lt_two_pow
            (cutoffOneSlabMaskFrom_lt physical width)]
          simp [hlabel]
        · have hlt : index < width := by omega
          rw [cutoffOneSlabMaskFrom_testBit physical width index hlt]
          have hne : width ≠ index := Ne.symm heq
          simp [hne]
      · rw [if_neg hlabel]
        by_cases heq : index = width
        · subst index
          rw [Nat.testBit_lt_two_pow
            (cutoffOneSlabMaskFrom_lt physical width)]
          simp [hlabel]
        · have hlt : index < width := by omega
          rw [cutoffOneSlabMaskFrom_testBit physical width index hlt]
          simp

def cutoffOneSlabMask (physical : EdgeLabelling) : Nat :=
  cutoffOneSlabMaskFrom physical 72

theorem cutoffOneSlabMask_lt (physical : EdgeLabelling) :
    cutoffOneSlabMask physical < 2 ^ 72 :=
  cutoffOneSlabMaskFrom_lt physical 72

theorem cutoffOneSlabMask_testBit
    (physical : EdgeLabelling) (index : Nat) (hindex : index < 72) :
    (cutoffOneSlabMask physical).testBit index =
      decide (physical index = 1) :=
  cutoffOneSlabMaskFrom_testBit physical 72 index hindex

def slabFaceBlockIncidenceCheck : Bool :=
  (List.range 116).all fun block =>
    (List.range 72).all fun faceId =>
      decide
        (slabFaceBlockDegree block (slabPlaquetteAt 1 faceId) =
          if (slabEdgeFaceIncidenceMask block).testBit faceId then 1 else 0)

theorem slabFaceBlockIncidenceCheck_true :
    slabFaceBlockIncidenceCheck = true := by
  decide

theorem slabFaceBlockDegree_eq_incidenceBit
    (block faceId : Nat) (hblock : block < 116) (hfaceId : faceId < 72) :
    slabFaceBlockDegree block (slabPlaquetteAt 1 faceId) =
      if (slabEdgeFaceIncidenceMask block).testBit faceId then 1 else 0 := by
  exact of_decide_eq_true
    (List.all_eq_true.mp
      (List.all_eq_true.mp slabFaceBlockIncidenceCheck_true
        block (List.mem_range.mpr hblock))
      faceId (List.mem_range.mpr hfaceId))

def cutoffOneIndexedSelectedBlockDegree
    (block : Nat) (physical : EdgeLabelling) : List Nat -> Nat
  | [] => 0
  | faceId :: rest =>
      physical faceId *
          (if (slabEdgeFaceIncidenceMask block).testBit faceId then 1 else 0) +
        cutoffOneIndexedSelectedBlockDegree block physical rest

private theorem cutoffOneFacesSelectedBlockDegree_map
    (block : Nat) (hblock : block < 116) (physical : EdgeLabelling) :
    forall faceIds : List Nat,
      (forall faceId, faceId ∈ faceIds -> faceId < 72) ->
      cutoffOneFacesSelectedBlockDegree block physical
          (faceIds.map (slabPlaquetteAt 1)) =
        cutoffOneIndexedSelectedBlockDegree block physical faceIds
  | [], _ => rfl
  | faceId :: rest, hfaceIds => by
      simp only [List.map_cons, cutoffOneFacesSelectedBlockDegree,
        cutoffOneIndexedSelectedBlockDegree]
      have hfaceId := hfaceIds faceId List.mem_cons_self
      have hidPhysical : faceId ∈ slabPhysicalFaceEdges 1 := by
        unfold slabPhysicalFaceEdges
        rw [correctedSlabPlaquettes_extent_one_length]
        exact List.mem_range.mpr hfaceId
      rw [idxOf_slabPlaquetteAt_one hidPhysical,
        slabFaceBlockDegree_eq_incidenceBit block faceId hblock hfaceId,
        cutoffOneFacesSelectedBlockDegree_map block hblock physical rest
          (fun other hother =>
            hfaceIds other (List.mem_cons_of_mem faceId hother))]

private theorem cutoffOneIndexedSelectedBlockDegree_eq_maskCount
    (block : Nat) (physical : EdgeLabelling)
    (hlabel : forall id, physical id <= 1) :
    forall faceIds : List Nat,
      (forall faceId, faceId ∈ faceIds -> faceId < 72) ->
      cutoffOneIndexedSelectedBlockDegree block physical faceIds =
        (faceIds.filter fun faceId =>
          (slabEdgeFaceIncidenceMask block).testBit faceId &&
            (cutoffOneSlabMask physical).testBit faceId).length
  | [], _ => rfl
  | faceId :: rest, hfaceIds => by
      have hfaceId := hfaceIds faceId List.mem_cons_self
      have hrest := cutoffOneIndexedSelectedBlockDegree_eq_maskCount
        block physical hlabel rest
        (fun other hother =>
          hfaceIds other (List.mem_cons_of_mem faceId hother))
      have hspin : physical faceId = 0 ∨ physical faceId = 1 := by
        have := hlabel faceId
        omega
      simp only [List.filter_cons]
      rw [cutoffOneSlabMask_testBit physical faceId hfaceId]
      rcases hspin with hzero | hone
      · simp [cutoffOneIndexedSelectedBlockDegree, hzero, hrest]
      · cases hincidence :
          (slabEdgeFaceIncidenceMask block).testBit faceId <;>
          simp [cutoffOneIndexedSelectedBlockDegree, hone, hincidence, hrest] <;>
          omega

private theorem slabPlaquetteAt_range_72 :
    (List.range 72).map (slabPlaquetteAt 1) =
      boundaryCompleteSlabPlaquettes 1 := by
  decide

theorem cutoffOneSlabSelectedBlockDegree_eq_maskIntersectionCount
    (block : Nat) (hblock : block < 116) (physical : EdgeLabelling)
    (hlabel : forall id, physical id <= 1) :
    cutoffOneSlabSelectedBlockDegree block physical =
      slabMaskIntersectionCount
        (slabEdgeFaceIncidenceMask block)
        (cutoffOneSlabMask physical) := by
  unfold cutoffOneSlabSelectedBlockDegree slabMaskIntersectionCount
  rw [← slabPlaquetteAt_range_72,
    cutoffOneFacesSelectedBlockDegree_map block hblock physical
      (List.range 72) (fun faceId hfaceId => List.mem_range.mp hfaceId)]
  exact cutoffOneIndexedSelectedBlockDegree_eq_maskCount
    block physical hlabel (List.range 72)
    (fun faceId hfaceId => List.mem_range.mp hfaceId)

private theorem listAll_false_witness {A : Type}
    (predicate : A -> Bool) (items : List A)
    (hfalse : items.all predicate = false) :
    exists item, item ∈ items ∧ predicate item = false := by
  induction items with
  | nil =>
      change true = false at hfalse
      cases hfalse
  | cons head tail induction =>
      cases hhead : predicate head with
      | false => exact ⟨head, List.mem_cons_self, hhead⟩
      | true =>
          simp only [List.all_cons, hhead, Bool.true_and] at hfalse
          exact Exists.elim (induction hfalse) fun item hparts =>
            ⟨item, List.mem_cons_of_mem head hparts.1, hparts.2⟩

theorem cutoffOneSlabMask_not_closed_has_odd_degree
    (physical : EdgeLabelling) (hlabel : forall id, physical id <= 1)
    (hclosed : slabSurfaceIsClosed (cutoffOneSlabMask physical) = false) :
    exists block, block < 116 ∧
      cutoffOneSlabSelectedBlockDegree block physical % 2 = 1 := by
  unfold slabSurfaceIsClosed at hclosed
  rw [correctedSlabLinks_extent_one_length] at hclosed
  obtain ⟨block, hblockMem, hblockFalse⟩ :=
    listAll_false_witness _ _ hclosed
  have hblock : block < 116 := List.mem_range.mp hblockMem
  have hdecide :
      decide (slabMaskIntersectionCount
        (slabEdgeFaceIncidenceMask block)
        (cutoffOneSlabMask physical) % 2 = 0) = false :=
    hblockFalse
  have hnotEven := of_decide_eq_false hdecide
  have hoddCount : slabMaskIntersectionCount
      (slabEdgeFaceIncidenceMask block)
      (cutoffOneSlabMask physical) % 2 = 1 := by
    omega
  refine ⟨block, hblock, ?_⟩
  rw [cutoffOneSlabSelectedBlockDegree_eq_maskIntersectionCount
    block hblock physical hlabel]
  exact hoddCount

theorem boundedCutoffOneSlabLabelling_le_one
    {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings 1
      (slabPhysicalFaceEdges 1)) :
    forall id, physical id <= 1 := by
  have hsound := boundedEdgeLabellings_sound 1
    (slabPhysicalFaceEdges 1) physical hphysical
  intro id
  by_cases hid : id ∈ slabPhysicalFaceEdges 1
  · have := hsound.1 id hid
    omega
  · rw [hsound.2 id hid]
    decide

theorem exactCorrectedSlabDualTerm_cutoffOne_eq_zero_of_not_closed
    (w : Q') (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings 1
      (slabPhysicalFaceEdges 1))
    (hclosed : slabSurfaceIsClosed (cutoffOneSlabMask physical) = false) :
    exactCorrectedSlabDualTerm w 1 1 physical ≈ 0 := by
  have hlabel := boundedCutoffOneSlabLabelling_le_one hphysical
  obtain ⟨block, hblock, hodd⟩ :=
    cutoffOneSlabMask_not_closed_has_odd_degree physical hlabel hclosed
  exact Q'.eqv_trans _ _ _
    (exactCorrectedSlabDualTerm_eq_weightedHaar w 1 physical)
    (exactCorrectedSlabWeightedHaar_cutoffOne_eq_zero_of_odd_degree
      w physical block hblock hlabel hodd)


def slabMaskLabelling (mask : Nat) : EdgeLabelling :=
  fun faceId => if mask.testBit faceId then 1 else 0

theorem slabMaskLabelling_cutoffOneSlabMask_eq
    (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings 1
      (slabPhysicalFaceEdges 1)) :
    slabMaskLabelling (cutoffOneSlabMask physical) = physical := by
  have hsound := boundedEdgeLabellings_sound 1
    (slabPhysicalFaceEdges 1) physical hphysical
  funext faceId
  by_cases hfaceId : faceId < 72
  · have hspin : physical faceId = 0 ∨ physical faceId = 1 := by
      have hidPhysical : faceId ∈ slabPhysicalFaceEdges 1 := by
        unfold slabPhysicalFaceEdges
        rw [correctedSlabPlaquettes_extent_one_length]
        exact List.mem_range.mpr hfaceId
      have := hsound.1 faceId hidPhysical
      omega
    unfold slabMaskLabelling
    rw [cutoffOneSlabMask_testBit physical faceId hfaceId]
    rcases hspin with hzero | hone
    · simp [hzero]
    · simp [hone]
  · have hidNotPhysical : faceId ∉ slabPhysicalFaceEdges 1 := by
      unfold slabPhysicalFaceEdges
      rw [correctedSlabPlaquettes_extent_one_length]
      simpa [List.mem_range] using hfaceId
    rw [hsound.2 faceId hidNotPhysical]
    unfold slabMaskLabelling
    have hpow : 2 ^ 72 <= 2 ^ faceId :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hmaskLt : cutoffOneSlabMask physical < 2 ^ faceId :=
      Nat.lt_of_lt_of_le (cutoffOneSlabMask_lt physical) hpow
    rw [Nat.testBit_lt_two_pow hmaskLt]
    rfl

theorem slabMaskLabelling_injective_below_72
    {left right : Nat} (hleft : left < 2 ^ 72)
    (hright : right < 2 ^ 72)
    (heq : slabMaskLabelling left = slabMaskLabelling right) :
    left = right := by
  apply Nat.eq_of_testBit_eq
  intro faceId
  by_cases hfaceId : faceId < 72
  · have hvalue := congrFun heq faceId
    unfold slabMaskLabelling at hvalue
    cases hleftBit : left.testBit faceId <;>
      cases hrightBit : right.testBit faceId <;>
      simp [hleftBit, hrightBit] at hvalue ⊢
  · have hpow : 2 ^ 72 <= 2 ^ faceId :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hleft hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hright hpow)]

theorem embeddedSurfaceLabelling_eq_slabMaskLabelling
    (compactMask : Nat) :
    embeddedSurfaceLabelling compactMask =
      slabMaskLabelling (embedBinarySurfaceMask compactMask) := by
  rfl

def cutoffOneFullSlabLabellings : List EdgeLabelling :=
  boundedEdgeLabellings 1 (slabPhysicalFaceEdges 1)

def cutoffOneClosedSlabLabellings : List EdgeLabelling :=
  cutoffOneFullSlabLabellings.filter fun physical =>
    slabSurfaceIsClosed (cutoffOneSlabMask physical)

def embeddedClosedSurfaceLabellings : List EdgeLabelling :=
  embeddedBinarySurfaceMasks.map slabMaskLabelling

theorem cutoffOneFullSlabLabellings_nodup :
    cutoffOneFullSlabLabellings.Nodup := by
  unfold cutoffOneFullSlabLabellings
  apply boundedEdgeLabellings_nodup
  decide

theorem embeddedClosedSurfaceLabellings_nodup :
    embeddedClosedSurfaceLabellings.Nodup := by
  unfold embeddedClosedSurfaceLabellings
  apply nodup_map_of_injOn
    slabMaskLabelling embeddedBinarySurfaceMasks
    embeddedBinarySurfaceMasks_sound.2.1
  intro left hleft right hright heq
  have hleftBound := of_decide_eq_true
    (List.all_eq_true.mp embeddedBinarySurfaceMasks_bounded left hleft)
  have hrightBound := of_decide_eq_true
    (List.all_eq_true.mp embeddedBinarySurfaceMasks_bounded right hright)
  exact slabMaskLabelling_injective_below_72
    hleftBound hrightBound heq

theorem mem_cutoffOneClosedSlabLabellings_iff
    (physical : EdgeLabelling) :
    physical ∈ cutoffOneClosedSlabLabellings ↔
      physical ∈ embeddedClosedSurfaceLabellings := by
  constructor
  · intro hphysical
    have hparts := List.mem_filter.mp hphysical
    have hmaskMem : cutoffOneSlabMask physical ∈
        embeddedBinarySurfaceMasks :=
      (slabSurfaceIsClosed_iff_mem_embeddedBinarySurfaceMasks
        (cutoffOneSlabMask physical)
        (cutoffOneSlabMask_lt physical)).mp hparts.2
    apply List.mem_map.mpr
    refine ⟨cutoffOneSlabMask physical, hmaskMem, ?_⟩
    exact slabMaskLabelling_cutoffOneSlabMask_eq physical hparts.1
  · intro hphysical
    obtain ⟨mask, hmask, heq⟩ := List.mem_map.mp hphysical
    rw [← heq]
    have hmaskBound := of_decide_eq_true
      (List.all_eq_true.mp embeddedBinarySurfaceMasks_bounded mask hmask)
    have hbounded : slabMaskLabelling mask ∈ cutoffOneFullSlabLabellings := by
      unfold cutoffOneFullSlabLabellings
      apply boundedEdgeLabellings_complete
      · intro faceId _
        unfold slabMaskLabelling
        split <;> decide
      · intro faceId hfaceId
        unfold slabPhysicalFaceEdges at hfaceId
        rw [correctedSlabPlaquettes_extent_one_length] at hfaceId
        have hge : 72 <= faceId := by
          simpa [List.mem_range] using hfaceId
        have hpow : 2 ^ 72 <= 2 ^ faceId :=
          Nat.pow_le_pow_right (by decide) hge
        unfold slabMaskLabelling
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hmaskBound hpow)]
        rfl
    apply List.mem_filter.mpr
    refine ⟨hbounded, ?_⟩
    have hdecode := slabMaskLabelling_cutoffOneSlabMask_eq
      (slabMaskLabelling mask) hbounded
    have hencoded : cutoffOneSlabMask (slabMaskLabelling mask) = mask :=
      slabMaskLabelling_injective_below_72
        (cutoffOneSlabMask_lt _) hmaskBound hdecode
    rw [hencoded]
    exact List.all_eq_true.mp embeddedBinarySurfaceMasks_sound.2.2 mask hmask

private theorem permOfNodupMemIff {A : Type} :
    forall (left right : List A), left.Nodup -> right.Nodup ->
      (forall item, item ∈ left ↔ item ∈ right) -> left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : forall item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hrightItem :=
            (hmem item).1 (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hrightItem with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hrightItem : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp
            ((hmem item).2 hrightItem)).resolve_left hne
      have htailPerm := permOfNodupMemIff
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

theorem cutoffOneClosedSlabLabellings_perm_embedded :
    cutoffOneClosedSlabLabellings.Perm embeddedClosedSurfaceLabellings := by
  apply permOfNodupMemIff
  · exact cutoffOneFullSlabLabellings_nodup.filter _
  · exact embeddedClosedSurfaceLabellings_nodup
  · exact mem_cutoffOneClosedSlabLabellings_iff


private theorem listQSum_eq_filter_of_zero
    {A : Type} (value : A -> Q') (predicate : A -> Bool) :
    forall items : List A,
      (forall item, item ∈ items -> predicate item = false ->
        value item ≈ 0) ->
      listQSum value items ≈ listQSum value (items.filter predicate)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail : forall item, item ∈ tail ->
          predicate item = false -> value item ≈ 0 := by
        intro item hitem hpredicate
        exact hzero item (List.mem_cons_of_mem head hitem) hpredicate
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum value (tail.filter predicate)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self hp)
              (listQSum_eq_filter_of_zero value predicate tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero value predicate tail htail)

private theorem listQSumPerm {A : Type} (value : A -> Q') :
    forall {left right : List A}, left.Perm right ->
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSumPerm value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      refine Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value first + value second) + listQSum value rest) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSumPerm value hleft) (listQSumPerm value hright)

theorem cutoffOneFullDualSum_eq_embeddedSurfaceDualSum
    (w : Q') :
    listQSum (exactCorrectedSlabDualTerm w 1 1)
        cutoffOneFullSlabLabellings ≈
      exactEmbeddedSurfaceDualSum w binarySurfaceMasks := by
  refine Q'.eqv_trans _
    (listQSum (exactCorrectedSlabDualTerm w 1 1)
      cutoffOneClosedSlabLabellings) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero
    intro physical hphysical hclosed
    exact exactCorrectedSlabDualTerm_cutoffOne_eq_zero_of_not_closed
      w physical hphysical hclosed
  · refine Q'.eqv_trans _
      (listQSum (exactCorrectedSlabDualTerm w 1 1)
        embeddedClosedSurfaceLabellings) _
      (listQSumPerm _ cutoffOneClosedSlabLabellings_perm_embedded) ?_
    unfold embeddedClosedSurfaceLabellings embeddedBinarySurfaceMasks
      exactEmbeddedSurfaceDualSum embeddedSurfaceLabelling
    simp only [List.map_map, Function.comp_apply, listQSum_map]
    exact Q'.eqv_refl _


def centralTripleDualTerm (w : Q')
    (triple :
      YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.CentralReflectionTriple) : Q' :=
  exactCorrectedSlabDualTerm w 1 1
    (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.assembleCentralReflectionTriple
      0 triple)

private theorem centralTripleDualSum_eq_nested (w : Q') :
    listQSum (centralTripleDualTerm w)
        (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectionTriples
          1 0) ≈
      listQSum
        (fun left => listQSum
          (fun right => listQSum
            (fun boundary =>
              exactCorrectedSlabDualTerm w 1 1
                (assembleReflectedSlabLabelling 0 left boundary right))
            (centralBoundaryChannels 1 0))
          (centralHalfStates 1 0))
        (centralHalfStates 1 0) := by
  unfold YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectionTriples
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (centralTripleDualTerm w)
      (fun left =>
        (centralHalfStates 1 0).flatMap (fun right =>
          (centralBoundaryChannels 1 0).map (fun boundary =>
            (left, (right, boundary)))))
      (centralHalfStates 1 0)) ?_
  apply listQSum_congr
  intro left
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (centralTripleDualTerm w)
      (fun right =>
        (centralBoundaryChannels 1 0).map (fun boundary =>
          (left, (right, boundary))))
      (centralHalfStates 1 0)) ?_
  apply listQSum_congr
  intro right
  rw [listQSum_map]
  exact Q'.eqv_refl _


theorem exactConstantQuadraticMoment_cutoffOne_eq_fullDualSum
    (w : Q') :
    exactConstantQuadraticMoment w 1 ≈
      listQSum (exactCorrectedSlabDualTerm w 1 1)
        cutoffOneFullSlabLabellings := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left => listQSum
        (fun right => listQSum
          (fun boundary =>
            exactCorrectedSlabDualTerm w 1 1
              (assembleReflectedSlabLabelling 0 left boundary right))
          (centralBoundaryChannels 1 0))
        (centralHalfStates 1 0))
      (centralHalfStates 1 0)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun left => listQSum
          (exactCorrectedSlabReflectedKernel w 1 0 left)
          (centralHalfStates 1 0))
        (centralHalfStates 1 0)) _
      (finiteJointBilinear_one_one_eq_joint_sum
        (centralHalfStates 1 0)
        (exactCorrectedSlabReflectedKernel w 1 0)) ?_
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    unfold exactCorrectedSlabReflectedKernel
    exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      (listQSum (centralTripleDualTerm w)
        (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectionTriples
          1 0)) _
      (Q'.eqv_symm (centralTripleDualSum_eq_nested w)) ?_
    refine Q'.eqv_trans _
      (listQSum (exactCorrectedSlabDualTerm w 1 1)
        (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralAssembledSlabLabellings
          1 0)) _ ?_ ?_
    · unfold YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralAssembledSlabLabellings
        centralTripleDualTerm
      rw [listQSum_map]
      exact Q'.eqv_refl _
    · have hfull :=
        YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.listQSum_centralAssembledSlabLabellings
          (exactCorrectedSlabDualTerm w 1 1) 1 0
      rw [show centralExtent 0 = 1 from rfl] at hfull
      unfold cutoffOneFullSlabLabellings
      exact hfull


theorem constantHaarFive_reindex (w : Q') :
    quaternionHaar 5
        (exactConstantMomentBasedCycleFivePolynomialCutoffOne w) ≈
      exactEmbeddedSurfaceDualSum w binarySurfaceMasks := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (exactConstantQuadraticMoment_cutoffOne_eq_basedCycleFiveHaar w))
    (Q'.eqv_trans _ _ _
      (exactConstantQuadraticMoment_cutoffOne_eq_fullDualSum w)
      (cutoffOneFullDualSum_eq_embeddedSurfaceDualSum w))


def slabLowerVacuum (physical : EdgeLabelling) : Bool :=
  (centralLowerFaceIds 0).all fun faceId => decide (physical faceId = 0)

def embeddedSurfaceLowerVacuum (compactMask : Nat) : Bool :=
  slabLowerVacuum (embeddedSurfaceLabelling compactMask)

theorem binarySurfaceMasks_filter_lowerVacuum :
    binarySurfaceMasks.filter embeddedSurfaceLowerVacuum =
      vacuumRowSurfaceMasks := by
  decide

private theorem filter_map_eq_map_filter
    {A B : Type} (predicate : B -> Bool) (mapItem : A -> B) :
    forall items : List A,
      (items.map mapItem).filter predicate =
        (items.filter (fun item => predicate (mapItem item))).map mapItem
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, List.filter_cons]
      cases hpredicate : predicate (mapItem head) <;>
        simp [filter_map_eq_map_filter predicate mapItem tail]

def cutoffOneVacuumClosedSlabLabellings : List EdgeLabelling :=
  cutoffOneClosedSlabLabellings.filter slabLowerVacuum

def embeddedVacuumRowSurfaceLabellings : List EdgeLabelling :=
  vacuumRowSurfaceMasks.map embeddedSurfaceLabelling

theorem embeddedClosed_filter_lowerVacuum_eq_vacuumRow :
    embeddedClosedSurfaceLabellings.filter slabLowerVacuum =
      embeddedVacuumRowSurfaceLabellings := by
  have hmap : embeddedClosedSurfaceLabellings =
      binarySurfaceMasks.map embeddedSurfaceLabelling := by
    unfold embeddedClosedSurfaceLabellings embeddedBinarySurfaceMasks
    rw [List.map_map]
    rfl
  rw [hmap]
  rw [filter_map_eq_map_filter]
  change (binarySurfaceMasks.filter embeddedSurfaceLowerVacuum).map
      embeddedSurfaceLabelling = embeddedVacuumRowSurfaceLabellings
  rw [binarySurfaceMasks_filter_lowerVacuum]
  rfl

theorem cutoffOneVacuumClosedSlabLabellings_perm_embedded :
    cutoffOneVacuumClosedSlabLabellings.Perm
      embeddedVacuumRowSurfaceLabellings := by
  unfold cutoffOneVacuumClosedSlabLabellings
  have hfiltered :=
    cutoffOneClosedSlabLabellings_perm_embedded.filter slabLowerVacuum
  rw [embeddedClosed_filter_lowerVacuum_eq_vacuumRow] at hfiltered
  exact hfiltered

abbrev CentralVacuumRowPair := EdgeLabelling × EdgeLabelling

def centralVacuumRowPairs : List CentralVacuumRowPair :=
  (centralHalfStates 1 0).flatMap fun right =>
    (centralBoundaryChannels 1 0).map fun boundary => (right, boundary)

def assembleCentralVacuumRowPair
    (pair : CentralVacuumRowPair) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 zeroEdgeLabelling pair.2 pair.1

def centralVacuumRowAssembledLabellings : List EdgeLabelling :=
  centralVacuumRowPairs.map assembleCentralVacuumRowPair

private theorem nodupCartesian {A B : Type}
    (xs : List A) (ys : List B)
    (hxs : xs.Nodup) (hys : ys.Nodup) :
    (xs.flatMap fun x => ys.map fun y => (x, y)).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs induction =>
      have hparts := List.nodup_cons.mp hxs
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨?_, induction hparts.2, ?_⟩
      · exact nodup_map_of_injOn (fun y => (x, y)) ys hys
          (fun _ _ _ _ heq => by injection heq)
      · intro left hleft right hright heq
        obtain ⟨y, _, hleftEq⟩ := List.mem_map.mp hleft
        obtain ⟨z, hz, hrightMap⟩ := List.mem_flatMap.mp hright
        obtain ⟨t, _, hrightEq⟩ := List.mem_map.mp hrightMap
        rw [← hleftEq, ← hrightEq] at heq
        have hxz : x = z := by injection heq
        exact hparts.1 (hxz ▸ hz)

theorem centralVacuumRowPairs_nodup : centralVacuumRowPairs.Nodup := by
  unfold centralVacuumRowPairs
  exact nodupCartesian
    (centralHalfStates 1 0) (centralBoundaryChannels 1 0)
    (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralHalfStates_nodup
      1 0)
    (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralBoundaryChannels_nodup
      1 0)

theorem zeroEdgeLabelling_mem_centralHalfStates_one :
    zeroEdgeLabelling ∈ centralHalfStates 1 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < 2
    decide
  · intro _ _
    rfl

theorem mem_centralVacuumRowPairs
    (pair : CentralVacuumRowPair) :
    pair ∈ centralVacuumRowPairs ↔
      pair.1 ∈ centralHalfStates 1 0 ∧
      pair.2 ∈ centralBoundaryChannels 1 0 := by
  constructor
  · intro hpair
    unfold centralVacuumRowPairs at hpair
    obtain ⟨right, hright, hboundaryMap⟩ := List.mem_flatMap.mp hpair
    obtain ⟨boundary, hboundary, heq⟩ := List.mem_map.mp hboundaryMap
    rw [← heq]
    exact ⟨hright, hboundary⟩
  · intro hparts
    unfold centralVacuumRowPairs
    apply List.mem_flatMap.mpr
    exact ⟨pair.1, hparts.1,
      List.mem_map.mpr ⟨pair.2, hparts.2, rfl⟩⟩

theorem assembleCentralVacuumRowPair_injective_on
    {left right : CentralVacuumRowPair}
    (hleft : left ∈ centralVacuumRowPairs)
    (hright : right ∈ centralVacuumRowPairs)
    (heq : assembleCentralVacuumRowPair left =
      assembleCentralVacuumRowPair right) :
    left = right := by
  let leftTriple :
      YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.CentralReflectionTriple :=
    (zeroEdgeLabelling, (left.1, left.2))
  let rightTriple :
      YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.CentralReflectionTriple :=
    (zeroEdgeLabelling, (right.1, right.2))
  have hleftParts := mem_centralVacuumRowPairs left |>.mp hleft
  have hrightParts := mem_centralVacuumRowPairs right |>.mp hright
  have hleftTriple : leftTriple ∈
      YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectionTriples
        1 0 := by
    apply YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.mem_centralReflectionTriples.mpr
    exact ⟨zeroEdgeLabelling_mem_centralHalfStates_one,
      hleftParts.1, hleftParts.2⟩
  have hrightTriple : rightTriple ∈
      YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectionTriples
        1 0 := by
    apply YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.mem_centralReflectionTriples.mpr
    exact ⟨zeroEdgeLabelling_mem_centralHalfStates_one,
      hrightParts.1, hrightParts.2⟩
  have htriple :=
    YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.assembleCentralReflectionTriple_injective_on
      hleftTriple hrightTriple heq
  injection htriple

theorem centralVacuumRowAssembledLabellings_nodup :
    centralVacuumRowAssembledLabellings.Nodup := by
  unfold centralVacuumRowAssembledLabellings
  exact nodup_map_of_injOn assembleCentralVacuumRowPair
    centralVacuumRowPairs centralVacuumRowPairs_nodup
    (fun _ hleft _ hright heq =>
      assembleCentralVacuumRowPair_injective_on hleft hright heq)

theorem slabLowerVacuum_assemble_zero
    (boundary right : EdgeLabelling) :
    slabLowerVacuum
        (assembleReflectedSlabLabelling
          0 zeroEdgeLabelling boundary right) = true := by
  unfold slabLowerVacuum
  apply List.all_eq_true.mpr
  intro faceId hfaceId
  have hparts := mem_centralLowerFaceIds.mp hfaceId
  rw [assembleReflectedSlabLabelling_lower hparts.1 hparts.2]
  rfl

theorem centralLowerRestriction_eq_zero_of_slabLowerVacuum
    (physical : EdgeLabelling)
    (hlower : slabLowerVacuum physical = true) :
    YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralLowerRestriction
        0 physical = zeroEdgeLabelling := by
  funext faceId
  unfold YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralLowerRestriction
  by_cases hfaceId : faceId ∈ centralLowerFaceIds 0
  · rw [if_pos hfaceId]
    exact of_decide_eq_true
      (List.all_eq_true.mp hlower faceId hfaceId)
  · rw [if_neg hfaceId]
    rfl

def cutoffOneVacuumRowSlabLabellings : List EdgeLabelling :=
  cutoffOneFullSlabLabellings.filter slabLowerVacuum

theorem mem_centralVacuumRowAssembledLabellings_iff
    (physical : EdgeLabelling) :
    physical ∈ centralVacuumRowAssembledLabellings ↔
      physical ∈ cutoffOneVacuumRowSlabLabellings := by
  constructor
  · intro hphysical
    obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp hphysical
    rw [← heq]
    have hparts := mem_centralVacuumRowPairs pair |>.mp hpair
    apply List.mem_filter.mpr
    refine ⟨?_, slabLowerVacuum_assemble_zero pair.2 pair.1⟩
    unfold cutoffOneFullSlabLabellings
    exact assembleReflectedSlabLabelling_mem_full
      zeroEdgeLabelling_mem_centralHalfStates_one hparts.2 hparts.1
  · intro hphysical
    have hparts := List.mem_filter.mp hphysical
    have hfull := hparts.1
    unfold cutoffOneFullSlabLabellings at hfull
    have hfullCentral : physical ∈ boundedEdgeLabellings 1
        (slabPhysicalFaceEdges (centralExtent 0)) := by
      rw [show centralExtent 0 = 1 from rfl]
      exact hfull
    let pair : CentralVacuumRowPair :=
      (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectedUpperRestriction
          0 physical,
        YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralBoundaryRestriction
          0 physical)
    have hpair : pair ∈ centralVacuumRowPairs := by
      apply (mem_centralVacuumRowPairs pair).mpr
      exact ⟨
        YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectedUpperRestriction_mem
          hfullCentral,
        YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralBoundaryRestriction_mem
          hfullCentral⟩
    apply List.mem_map.mpr
    refine ⟨pair, hpair, ?_⟩
    have hlower := centralLowerRestriction_eq_zero_of_slabLowerVacuum
      physical hparts.2
    have hassemble :=
      YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.assembleReflectedSlabLabelling_restrictions
        hfullCentral
    rw [hlower] at hassemble
    change assembleReflectedSlabLabelling 0 zeroEdgeLabelling
      (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralBoundaryRestriction
        0 physical)
      (YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectedUpperRestriction
        0 physical) = physical
    exact hassemble

theorem centralVacuumRowAssembledLabellings_perm_fullRow :
    centralVacuumRowAssembledLabellings.Perm
      cutoffOneVacuumRowSlabLabellings := by
  apply permOfNodupMemIff
  · exact centralVacuumRowAssembledLabellings_nodup
  · exact cutoffOneFullSlabLabellings_nodup.filter _
  · exact mem_centralVacuumRowAssembledLabellings_iff

private theorem filter_filter_comm {A : Type}
    (first second : A -> Bool) : forall items : List A,
    (items.filter first).filter second =
      (items.filter second).filter first
  | [] => rfl
  | head :: tail => by
      simp only [List.filter_cons]
      cases hfirst : first head <;> cases hsecond : second head <;>
        simp [hfirst, hsecond, filter_filter_comm first second tail]

theorem cutoffOneVacuumRow_filter_closed :
    cutoffOneVacuumRowSlabLabellings.filter
        (fun physical => slabSurfaceIsClosed (cutoffOneSlabMask physical)) =
      cutoffOneVacuumClosedSlabLabellings := by
  unfold cutoffOneVacuumRowSlabLabellings
    cutoffOneVacuumClosedSlabLabellings cutoffOneClosedSlabLabellings
  exact filter_filter_comm slabLowerVacuum
    (fun physical => slabSurfaceIsClosed (cutoffOneSlabMask physical))
    cutoffOneFullSlabLabellings

theorem cutoffOneVacuumRowDualSum_eq_embeddedSurfaceDualSum
    (w : Q') :
    listQSum (exactCorrectedSlabDualTerm w 1 1)
        cutoffOneVacuumRowSlabLabellings ≈
      exactEmbeddedSurfaceDualSum w vacuumRowSurfaceMasks := by
  refine Q'.eqv_trans _
    (listQSum (exactCorrectedSlabDualTerm w 1 1)
      (cutoffOneVacuumRowSlabLabellings.filter fun physical =>
        slabSurfaceIsClosed (cutoffOneSlabMask physical))) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero
    intro physical hphysical hclosed
    have hfull := (List.mem_filter.mp hphysical).1
    exact exactCorrectedSlabDualTerm_cutoffOne_eq_zero_of_not_closed
      w physical hfull hclosed
  · rw [cutoffOneVacuumRow_filter_closed]
    refine Q'.eqv_trans _
      (listQSum (exactCorrectedSlabDualTerm w 1 1)
        embeddedVacuumRowSurfaceLabellings) _
      (listQSumPerm _
        cutoffOneVacuumClosedSlabLabellings_perm_embedded) ?_
    unfold embeddedVacuumRowSurfaceLabellings exactEmbeddedSurfaceDualSum
    rw [listQSum_map]
    exact Q'.eqv_refl _

def centralVacuumRowPairDualTerm
    (w : Q') (pair : CentralVacuumRowPair) : Q' :=
  exactCorrectedSlabDualTerm w 1 1 (assembleCentralVacuumRowPair pair)

private theorem centralVacuumRowPairDualSum_eq_nested (w : Q') :
    listQSum (centralVacuumRowPairDualTerm w) centralVacuumRowPairs ≈
      listQSum
        (fun right => listQSum
          (fun boundary => exactCorrectedSlabDualTerm w 1 1
            (assembleReflectedSlabLabelling
              0 zeroEdgeLabelling boundary right))
          (centralBoundaryChannels 1 0))
        (centralHalfStates 1 0) := by
  unfold centralVacuumRowPairs
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (centralVacuumRowPairDualTerm w)
      (fun right => (centralBoundaryChannels 1 0).map fun boundary =>
        (right, boundary))
      (centralHalfStates 1 0)) ?_
  apply listQSum_congr
  intro right
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem exactVacuumRightConstantCrossMoment_cutoffOne_eq_fullRowDualSum
    (w : Q') :
    exactVacuumRightConstantCrossMoment w 1 ≈
      listQSum (exactCorrectedSlabDualTerm w 1 1)
        cutoffOneVacuumRowSlabLabellings := by
  refine Q'.eqv_trans _
    (listQSum
      (fun right => listQSum
        (fun boundary => exactCorrectedSlabDualTerm w 1 1
          (assembleReflectedSlabLabelling
            0 zeroEdgeLabelling boundary right))
        (centralBoundaryChannels 1 0))
      (centralHalfStates 1 0)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (exactCorrectedSlabReflectedKernel
          w 1 0 zeroEdgeLabelling)
        (centralHalfStates 1 0)) _
      (exactVacuumRightConstantCrossMoment_eq_vacuumRowSum w 1) ?_
    apply listQSum_congr
    intro right
    unfold exactCorrectedSlabReflectedKernel
    exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      (listQSum (centralVacuumRowPairDualTerm w)
        centralVacuumRowPairs) _
      (Q'.eqv_symm (centralVacuumRowPairDualSum_eq_nested w)) ?_
    refine Q'.eqv_trans _
      (listQSum (exactCorrectedSlabDualTerm w 1 1)
        centralVacuumRowAssembledLabellings) _ ?_ ?_
    · unfold centralVacuumRowAssembledLabellings
        centralVacuumRowPairDualTerm
      rw [listQSum_map]
      exact Q'.eqv_refl _
    · exact listQSumPerm _
        centralVacuumRowAssembledLabellings_perm_fullRow

theorem vacuumRowHaarFive_reindex (w : Q') :
    quaternionHaar 5
        (exactVacuumRowBasedCycleFivePolynomialCutoffOne w) ≈
      exactEmbeddedSurfaceDualSum w vacuumRowSurfaceMasks := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (exactVacuumRightConstantCrossMoment_cutoffOne_eq_basedCycleFiveHaar w))
    (Q'.eqv_trans _ _ _
      (exactVacuumRightConstantCrossMoment_cutoffOne_eq_fullRowDualSum w)
      (cutoffOneVacuumRowDualSum_eq_embeddedSurfaceDualSum w))

/-- The actual cutoff-one character-expansion bridge: the two five-based-cycle
Haar integrals reindex exactly over the literal rank-seven closed surfaces. -/
def cutoffOneCharacterExpansionReindex :
    CutoffOneCharacterExpansionReindex where
  vacuumRowReindex := vacuumRowHaarFive_reindex
  constantReindex := constantHaarFive_reindex

end YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.exactCorrectedSlabDualTerm_cutoffOne_eq_zero_of_not_closed
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.cutoffOneSlabMask_not_closed_has_odd_degree
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.boundedCutoffOneSlabLabelling_le_one
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.cutoffOneClosedSlabLabellings_perm_embedded
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.cutoffOneFullDualSum_eq_embeddedSurfaceDualSum
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.exactConstantQuadraticMoment_cutoffOne_eq_fullDualSum
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.exactVacuumRightConstantCrossMoment_cutoffOne_eq_fullRowDualSum
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.vacuumRowHaarFive_reindex
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.constantHaarFive_reindex
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex.cutoffOneCharacterExpansionReindex
