/-
# Closed two-child bubbles in every dyadic plaquette fibre

A coarse twice-spin value two cannot be represented by the literal four-cell
subdivision of a binary support: that subdivision contributes only one
nondegenerate child to each coarse fibre.  This module supplies the missing
local geometric generator.

For each coarse plaquette and either transverse dyadic layer, we translate the
boundary of a fine unit cube whose two opposite target-plane faces are exactly
one adjacent pair in the four-element nondegenerate fibre.  The other four
cube faces are dyadically degenerate.  Thus the support is duplicate-free and
closed at every fine link, while its target packet is respectively
`(1,1,0,0)` or `(0,0,1,1)`.

This is finite cubical geometry only.  It does not yet combine bubbles over a
whole accepted spin assignment, establish corrected-slab containment at the
spatial boundary, or assert a measure, continuum, or mass-gap theorem.
-/

import YMGap.Continuum.Z4DyadicSubdivisionClosure
import YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier

namespace YMGap.Continuum.Z4DyadicClosedPairBubble

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. The three coordinate orientations of a unit-cube boundary -/

/-- Boundary of the unit cube in coordinate directions `0,1,3`. -/
def unitCube013Surface : List Z4Plaq :=
  [((0, 0, 0, 0), .p01), ((0, 0, 0, 1), .p01),
   ((0, 0, 0, 0), .p03), ((0, 1, 0, 0), .p03),
   ((0, 0, 0, 0), .p13), ((1, 0, 0, 0), .p13)]

/-- Boundary of the unit cube in coordinate directions `0,2,3`. -/
def unitCube023Surface : List Z4Plaq :=
  [((0, 0, 0, 0), .p02), ((0, 0, 0, 1), .p02),
   ((0, 0, 0, 0), .p03), ((0, 0, 1, 0), .p03),
   ((0, 0, 0, 0), .p23), ((1, 0, 0, 0), .p23)]

theorem unitCube013Surface_nodup : unitCube013Surface.Nodup := by
  decide

theorem unitCube023Surface_nodup : unitCube023Surface.Nodup := by
  decide

theorem unitCube013Surface_evenFaceIncidence :
    EvenFaceIncidence unitCube013Surface := by
  intro link
  rw [← occurrenceCount_flatMap_edgesOf]
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := link
  cases direction <;>
    simp [unitCube013Surface, edgesOf, dirsOf, addE, occurrenceCount] <;>
    omega

theorem unitCube023Surface_evenFaceIncidence :
    EvenFaceIncidence unitCube023Surface := by
  intro link
  rw [← occurrenceCount_flatMap_edgesOf]
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := link
  cases direction <;>
    simp [unitCube023Surface, edgesOf, dirsOf, addE, occurrenceCount] <;>
    omega

/-! ## 2. A translated pair bubble over an arbitrary coarse face -/

/-- Choose a cube orientation containing the target plane.  The remaining
cube direction is the first transverse dyadic bit of that plane. -/
def pairBubbleShape : Z4Plane → List Z4Plaq
  | .p01 | .p02 | .p12 => unitCubeSurface
  | .p03 | .p13 => unitCube013Surface
  | .p23 => unitCube023Surface

theorem pairBubbleShape_nodup (plane : Z4Plane) :
    (pairBubbleShape plane).Nodup := by
  cases plane <;>
    simp only [pairBubbleShape] <;>
    first
    | exact unitCubeSurface_nodup
    | exact unitCube013Surface_nodup
    | exact unitCube023Surface_nodup

theorem pairBubbleShape_evenFaceIncidence (plane : Z4Plane) :
    EvenFaceIncidence (pairBubbleShape plane) := by
  cases plane <;>
    simp only [pairBubbleShape] <;>
    first
    | exact unitCubeSurface_evenFaceIncidence
    | exact unitCube013Surface_evenFaceIncidence
    | exact unitCube023Surface_evenFaceIncidence

/-- Translation placing the two target-plane cube faces in slots `0,1` when
`upper = false` and slots `2,3` when `upper = true`. -/
def pairBubbleOffset : Z4Plaq → Bool → AxisOffset
  | ((a, b, c, d), .p01), upper =>
      ⟨2 * a + 1, 2 * b + 1, 2 * c, 2 * d + upper.toNat⟩
  | ((a, b, c, d), .p02), upper =>
      ⟨2 * a + 1, 2 * b, 2 * c + 1, 2 * d + upper.toNat⟩
  | ((a, b, c, d), .p03), upper =>
      ⟨2 * a + 1, 2 * b, 2 * c + upper.toNat, 2 * d + 1⟩
  | ((a, b, c, d), .p12), upper =>
      ⟨2 * a, 2 * b + 1, 2 * c + 1, 2 * d + upper.toNat⟩
  | ((a, b, c, d), .p13), upper =>
      ⟨2 * a, 2 * b + 1, 2 * c + upper.toNat, 2 * d + 1⟩
  | ((a, b, c, d), .p23), upper =>
      ⟨2 * a, 2 * b + upper.toNat, 2 * c + 1, 2 * d + 1⟩

/-- Six-face closed fine support whose only nondegenerate dyadic faces are an
adjacent pair over `coarse`. -/
def dyadicPairBubble (coarse : Z4Plaq) (upper : Bool) : List Z4Plaq :=
  (pairBubbleShape coarse.2).map
    (axisShiftPlaquette (pairBubbleOffset coarse upper))

private theorem nodup_map_of_injective_local {A B : Type}
    (map : A → B) (hinjective : Function.Injective map) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective_local map hinjective hparts.2⟩
      intro hmem
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective heq).symm ▸ hsource)

theorem dyadicPairBubble_nodup (coarse : Z4Plaq) (upper : Bool) :
    (dyadicPairBubble coarse upper).Nodup := by
  unfold dyadicPairBubble
  exact nodup_map_of_injective_local _
    (axisShiftPlaquette_injective (pairBubbleOffset coarse upper))
    (pairBubbleShape_nodup coarse.2)

theorem dyadicPairBubble_evenFaceIncidence
    (coarse : Z4Plaq) (upper : Bool) :
    EvenFaceIncidence (dyadicPairBubble coarse upper) := by
  exact axisShift_evenFaceIncidence (pairBubbleOffset coarse upper)
    (pairBubbleShape_evenFaceIncidence coarse.2)

/-! ## 3. Exact nondegenerate image and target packet -/

/-- Origin face of the selected plane in its pair-bubble cube. -/
def pairBubbleSourceFirst (plane : Z4Plane) : Z4Plaq :=
  ((0, 0, 0, 0), plane)

/-- Opposite selected-plane face of the unit cube. -/
def pairBubbleSourceSecond : Z4Plane → Z4Plaq
  | .p01 => ((0, 0, 1, 0), .p01)
  | .p02 => ((0, 1, 0, 0), .p02)
  | .p03 => ((0, 1, 0, 0), .p03)
  | .p12 => ((1, 0, 0, 0), .p12)
  | .p13 => ((1, 0, 0, 0), .p13)
  | .p23 => ((1, 0, 0, 0), .p23)

theorem pairBubbleSourceFirst_mem (plane : Z4Plane) :
    pairBubbleSourceFirst plane ∈ pairBubbleShape plane := by
  cases plane <;>
    simp only [pairBubbleSourceFirst, pairBubbleShape,
      unitCubeSurface, unitCube013Surface, unitCube023Surface] <;>
    first
    | exact List.mem_cons_self
    | exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)
    | exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem pairBubbleSourceSecond_mem (plane : Z4Plane) :
    pairBubbleSourceSecond plane ∈ pairBubbleShape plane := by
  cases plane <;>
    simp only [pairBubbleSourceSecond, pairBubbleShape,
      unitCubeSurface, unitCube013Surface, unitCube023Surface] <;>
    first
    | exact List.mem_cons_of_mem _ List.mem_cons_self
    | exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
    | exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))

def pairBubbleFirstSlotIndex : Bool → Nat
  | false => 0
  | true => 2

def pairBubbleSecondSlotIndex : Bool → Nat
  | false => 1
  | true => 3

theorem pairBubble_shift_first_eq_preimage
    (coarse : Z4Plaq) (upper : Bool) :
    axisShiftPlaquette (pairBubbleOffset coarse upper)
        (pairBubbleSourceFirst coarse.2) =
      (dyadicFacePreimages coarse).getD
        (pairBubbleFirstSlotIndex upper) fallbackPlaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;> cases upper <;>
    simp [pairBubbleOffset, pairBubbleSourceFirst,
      pairBubbleFirstSlotIndex, dyadicFacePreimages,
      axisShiftPlaquette, axisShiftVertex]

theorem pairBubble_shift_second_eq_preimage
    (coarse : Z4Plaq) (upper : Bool) :
    axisShiftPlaquette (pairBubbleOffset coarse upper)
        (pairBubbleSourceSecond coarse.2) =
      (dyadicFacePreimages coarse).getD
        (pairBubbleSecondSlotIndex upper) fallbackPlaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;> cases upper <;>
    simp [pairBubbleOffset, pairBubbleSourceSecond,
      pairBubbleSecondSlotIndex, dyadicFacePreimages,
      axisShiftPlaquette, axisShiftVertex] <;>
    omega

theorem pairBubble_selected_preimages_mem
    (coarse : Z4Plaq) (upper : Bool) :
    (dyadicFacePreimages coarse).getD
          (pairBubbleFirstSlotIndex upper) fallbackPlaquette ∈
        dyadicPairBubble coarse upper ∧
      (dyadicFacePreimages coarse).getD
          (pairBubbleSecondSlotIndex upper) fallbackPlaquette ∈
        dyadicPairBubble coarse upper := by
  constructor
  · rw [← pairBubble_shift_first_eq_preimage coarse upper]
    unfold dyadicPairBubble
    apply List.mem_map.mpr
    exact ⟨pairBubbleSourceFirst coarse.2,
      pairBubbleSourceFirst_mem coarse.2, rfl⟩
  · rw [← pairBubble_shift_second_eq_preimage coarse upper]
    unfold dyadicPairBubble
    apply List.mem_map.mpr
    exact ⟨pairBubbleSourceSecond coarse.2,
      pairBubbleSourceSecond_mem coarse.2, rfl⟩

/-- The second transverse dyadic bit, whose false/true values distinguish
fibre slots `0,1` from slots `2,3`. -/
def dyadicFaceUpperLayerB : Z4Plaq → Bool
  | ((_, _, _, d), .p01) => decide (d % 2 = 1)
  | ((_, _, _, d), .p02) => decide (d % 2 = 1)
  | ((_, _, c, _), .p03) => decide (c % 2 = 1)
  | ((_, _, _, d), .p12) => decide (d % 2 = 1)
  | ((_, _, c, _), .p13) => decide (c % 2 = 1)
  | ((_, b, _, _), .p23) => decide (b % 2 = 1)

theorem dyadicFacePreimages_upperLayerB (coarse : Z4Plaq) :
    (dyadicFacePreimages coarse).map dyadicFaceUpperLayerB =
      [false, false, true, true] := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [dyadicFacePreimages, dyadicFaceUpperLayerB] <;>
    omega

/-- Every nondegenerate bubble face lies in the chosen lower or upper pair. -/
theorem dyadicPairBubble_nondegenerate_upperLayerB
    {coarse fine : Z4Plaq} {upper : Bool}
    (hmem : fine ∈ dyadicPairBubble coarse upper)
    (hnondegenerate : dyadicPlaquetteNondegenerateB fine = true) :
    dyadicFaceUpperLayerB fine = upper := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;> cases upper <;>
    simp only [dyadicPairBubble, pairBubbleShape, pairBubbleOffset,
      unitCubeSurface, unitCube013Surface, unitCube023Surface,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hmem <;>
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [axisShiftPlaquette, axisShiftVertex,
      dyadicPlaquetteNondegenerateB, vertexCoord, dirsOf,
      dyadicFaceUpperLayerB] at hnondegenerate ⊢ <;>
    omega

private theorem getD_mem_of_lt_local {A : Type} (fallback : A) :
    ∀ (items : List A) (index : Nat), index < items.length →
      items.getD index fallback ∈ items
  | [], _, hindex => by simp at hindex
  | head :: tail, 0, _ => by simp
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ, List.mem_cons]
      exact Or.inr
        (getD_mem_of_lt_local fallback tail index (by simpa using hindex))

theorem dyadicFacePreimage_slots_mem (coarse : Z4Plaq) :
    (dyadicFacePreimages coarse).getD 0 fallbackPlaquette ∈
        dyadicFacePreimages coarse ∧
      (dyadicFacePreimages coarse).getD 1 fallbackPlaquette ∈
        dyadicFacePreimages coarse ∧
      (dyadicFacePreimages coarse).getD 2 fallbackPlaquette ∈
        dyadicFacePreimages coarse ∧
      (dyadicFacePreimages coarse).getD 3 fallbackPlaquette ∈
        dyadicFacePreimages coarse := by
  have hlength : (dyadicFacePreimages coarse).length = 4 := by
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
    cases plane <;> rfl
  have hmem : ∀ i, i < 4 →
      (dyadicFacePreimages coarse).getD i fallbackPlaquette ∈
        dyadicFacePreimages coarse := by
    intro i hi
    apply getD_mem_of_lt_local fallbackPlaquette
    rw [hlength]
    exact hi
  exact ⟨hmem 0 (by decide), hmem 1 (by decide),
    hmem 2 (by decide), hmem 3 (by decide)⟩

private theorem supportCoefficient_toNat_one_of_mem
    {support : List Z4Plaq} {fine : Z4Plaq} (hmem : fine ∈ support) :
    (supportCoefficient support fine).toNat = 1 := by
  unfold supportCoefficient
  rw [show decide (fine ∈ support) = true from decide_eq_true hmem]
  rfl

private theorem supportCoefficient_toNat_zero_of_not_mem
    {support : List Z4Plaq} {fine : Z4Plaq} (hnot : fine ∉ support) :
    (supportCoefficient support fine).toNat = 0 := by
  unfold supportCoefficient
  rw [show decide (fine ∈ support) = false from decide_eq_false hnot]
  rfl

theorem dyadicFacePreimage_slot0_upperLayerB (coarse : Z4Plaq) :
    dyadicFaceUpperLayerB
        ((dyadicFacePreimages coarse).getD 0 fallbackPlaquette) = false := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [dyadicFacePreimages, dyadicFaceUpperLayerB] <;>
    omega

theorem dyadicFacePreimage_slot1_upperLayerB (coarse : Z4Plaq) :
    dyadicFaceUpperLayerB
        ((dyadicFacePreimages coarse).getD 1 fallbackPlaquette) = false := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [dyadicFacePreimages, dyadicFaceUpperLayerB] <;>
    omega

theorem dyadicFacePreimage_slot2_upperLayerB (coarse : Z4Plaq) :
    dyadicFaceUpperLayerB
        ((dyadicFacePreimages coarse).getD 2 fallbackPlaquette) = true := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [dyadicFacePreimages, dyadicFaceUpperLayerB] <;>
    omega

theorem dyadicFacePreimage_slot3_upperLayerB (coarse : Z4Plaq) :
    dyadicFaceUpperLayerB
        ((dyadicFacePreimages coarse).getD 3 fallbackPlaquette) = true := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [dyadicFacePreimages, dyadicFaceUpperLayerB] <;>
    omega

private theorem odd_half_local (coordinate : Nat) :
    (2 * coordinate + 1) / 2 = coordinate := by
  rw [Nat.mul_add_div (m := 2) (by omega) coordinate 1]
  simp

/-- Every nondegenerate face of the bubble projects to its selected coarse
face.  The four side faces are excluded precisely by the nondegeneracy test. -/
theorem dyadicPairBubble_nondegenerate_projection
    {coarse fine : Z4Plaq} {upper : Bool}
    (hmem : fine ∈ dyadicPairBubble coarse upper)
    (hnondegenerate : dyadicPlaquetteNondegenerateB fine = true) :
    dyadicPlaquetteProjection fine = coarse := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;> cases upper <;>
    simp only [dyadicPairBubble, pairBubbleShape, pairBubbleOffset,
      unitCubeSurface, unitCube013Surface, unitCube023Surface,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hmem <;>
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [axisShiftPlaquette, axisShiftVertex,
      dyadicPlaquetteNondegenerateB, vertexCoord, dirsOf,
      dyadicPlaquetteProjection, dyadicVertexProjection, odd_half_local]
      at hnondegenerate ⊢ <;>
    omega

/-- The two possible ordered fibre packets contributed by a pair bubble. -/
def pairBubblePacket : Bool → FaceSpinPacket
  | false => ⟨1, 1, 0, 0⟩
  | true => ⟨0, 0, 1, 1⟩

/-- Exact ordered packet over the selected coarse face. -/
theorem dyadicFaceSpinPacket_pairBubble_target
    (coarse : Z4Plaq) (upper : Bool) :
    dyadicFaceSpinPacket
        (fun fine => (supportCoefficient
          (dyadicPairBubble coarse upper) fine).toNat)
        coarse =
      pairBubblePacket upper := by
  have hslots := dyadicFacePreimage_slots_mem coarse
  have hproperties0 :=
    facePreimage_is_nondegenerate_projection hslots.1
  have hproperties1 :=
    facePreimage_is_nondegenerate_projection hslots.2.1
  have hproperties2 :=
    facePreimage_is_nondegenerate_projection hslots.2.2.1
  have hproperties3 :=
    facePreimage_is_nondegenerate_projection hslots.2.2.2
  have hlayer0 := dyadicFacePreimage_slot0_upperLayerB coarse
  have hlayer1 := dyadicFacePreimage_slot1_upperLayerB coarse
  have hlayer2 := dyadicFacePreimage_slot2_upperLayerB coarse
  have hlayer3 := dyadicFacePreimage_slot3_upperLayerB coarse
  cases upper with
  | false =>
      have hselected := pairBubble_selected_preimages_mem coarse false
      simp only [pairBubbleFirstSlotIndex,
        pairBubbleSecondSlotIndex] at hselected
      have hnot2 : (dyadicFacePreimages coarse).getD 2 fallbackPlaquette ∉
          dyadicPairBubble coarse false := by
        intro hmem
        have hlayer := dyadicPairBubble_nondegenerate_upperLayerB
          hmem hproperties2.1
        rw [hlayer2] at hlayer
        cases hlayer
      have hnot3 : (dyadicFacePreimages coarse).getD 3 fallbackPlaquette ∉
          dyadicPairBubble coarse false := by
        intro hmem
        have hlayer := dyadicPairBubble_nondegenerate_upperLayerB
          hmem hproperties3.1
        rw [hlayer3] at hlayer
        cases hlayer
      simp only [dyadicFaceSpinPacket, pairBubblePacket]
      rw [supportCoefficient_toNat_one_of_mem hselected.1,
        supportCoefficient_toNat_one_of_mem hselected.2,
        supportCoefficient_toNat_zero_of_not_mem hnot2,
        supportCoefficient_toNat_zero_of_not_mem hnot3]
  | true =>
      have hselected := pairBubble_selected_preimages_mem coarse true
      simp only [pairBubbleFirstSlotIndex,
        pairBubbleSecondSlotIndex] at hselected
      have hnot0 : (dyadicFacePreimages coarse).getD 0 fallbackPlaquette ∉
          dyadicPairBubble coarse true := by
        intro hmem
        have hlayer := dyadicPairBubble_nondegenerate_upperLayerB
          hmem hproperties0.1
        rw [hlayer0] at hlayer
        cases hlayer
      have hnot1 : (dyadicFacePreimages coarse).getD 1 fallbackPlaquette ∉
          dyadicPairBubble coarse true := by
        intro hmem
        have hlayer := dyadicPairBubble_nondegenerate_upperLayerB
          hmem hproperties1.1
        rw [hlayer1] at hlayer
        cases hlayer
      simp only [dyadicFaceSpinPacket, pairBubblePacket]
      rw [supportCoefficient_toNat_zero_of_not_mem hnot0,
        supportCoefficient_toNat_zero_of_not_mem hnot1,
        supportCoefficient_toNat_one_of_mem hselected.1,
        supportCoefficient_toNat_one_of_mem hselected.2]

/-- A nondegenerate fibre face over another coarse plaquette cannot belong to
the bubble. -/
theorem supportCoefficient_pairBubble_eq_false_of_ne
    {coarse query fine : Z4Plaq} {upper : Bool}
    (hquery : fine ∈ dyadicFacePreimages query)
    (hne : query ≠ coarse) :
    supportCoefficient (dyadicPairBubble coarse upper) fine = false := by
  unfold supportCoefficient
  apply decide_eq_false
  intro hmem
  have hqueryProperties :=
    facePreimage_is_nondegenerate_projection hquery
  have hbubbleProjection :=
    dyadicPairBubble_nondegenerate_projection
      hmem hqueryProperties.1
  exact hne (hqueryProperties.2.symm.trans hbubbleProjection)

/-- Every off-target coarse fibre has the zero packet. -/
theorem dyadicFaceSpinPacket_pairBubble_off_target
    {coarse query : Z4Plaq} (upper : Bool) (hne : query ≠ coarse) :
    dyadicFaceSpinPacket
        (fun fine => (supportCoefficient
          (dyadicPairBubble coarse upper) fine).toNat)
        query =
      ⟨0, 0, 0, 0⟩ := by
  have hslots := dyadicFacePreimage_slots_mem query
  have hzero0 := supportCoefficient_pairBubble_eq_false_of_ne
    hslots.1 hne (upper := upper)
  have hzero1 := supportCoefficient_pairBubble_eq_false_of_ne
    hslots.2.1 hne (upper := upper)
  have hzero2 := supportCoefficient_pairBubble_eq_false_of_ne
    hslots.2.2.1 hne (upper := upper)
  have hzero3 := supportCoefficient_pairBubble_eq_false_of_ne
    hslots.2.2.2 hne (upper := upper)
  simp only [dyadicFaceSpinPacket]
  rw [hzero0, hzero1, hzero2, hzero3]
  rfl

/-- Complete packet formula: a pair bubble affects exactly one coarse fibre. -/
theorem dyadicFaceSpinPacket_pairBubble
    (coarse query : Z4Plaq) (upper : Bool) :
    dyadicFaceSpinPacket
        (fun fine => (supportCoefficient
          (dyadicPairBubble coarse upper) fine).toNat)
        query =
      if query = coarse then pairBubblePacket upper else ⟨0, 0, 0, 0⟩ := by
  by_cases heq : query = coarse
  · subst query
    rw [if_pos rfl]
    exact dyadicFaceSpinPacket_pairBubble_target coarse upper
  · rw [if_neg heq]
    exact dyadicFaceSpinPacket_pairBubble_off_target upper heq

#print axioms unitCube013Surface_evenFaceIncidence
#print axioms unitCube023Surface_evenFaceIncidence
#print axioms dyadicPairBubble_nodup
#print axioms dyadicPairBubble_evenFaceIncidence
#print axioms pairBubble_selected_preimages_mem
#print axioms dyadicFacePreimages_upperLayerB
#print axioms dyadicPairBubble_nondegenerate_upperLayerB
#print axioms dyadicFacePreimage_slots_mem
#print axioms dyadicFacePreimage_slot0_upperLayerB
#print axioms dyadicFacePreimage_slot1_upperLayerB
#print axioms dyadicFacePreimage_slot2_upperLayerB
#print axioms dyadicFacePreimage_slot3_upperLayerB
#print axioms dyadicPairBubble_nondegenerate_projection
#print axioms supportCoefficient_toNat_one_of_mem
#print axioms supportCoefficient_toNat_zero_of_not_mem
#print axioms dyadicFaceSpinPacket_pairBubble_target
#print axioms supportCoefficient_pairBubble_eq_false_of_ne
#print axioms dyadicFaceSpinPacket_pairBubble_off_target
#print axioms dyadicFaceSpinPacket_pairBubble

end YMGap.Continuum.Z4DyadicClosedPairBubble
