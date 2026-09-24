/-
# Active and spectator channels for a literal padded dyadic Wilson square

The split is the Boolean partition of the complete fixed-spatial carrier by
the block slots occurring in the actual ordered square word.  Only the Wilson
insertion is proved independent of the complementary blocks; the projected
endpoint source remains unchanged and arbitrary.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
import YMGap.Continuum.SU2QuaternionProductHeatWilsonWord

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceCharacter)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
  (wordAt word_independent)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
  (character_independent)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
  (degree_zero_independent)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- The actual carrier slots, in the order in which the square traverses them. -/
def loopSlots (scale width : Nat) (hwidth : side scale < width) : List Nat :=
  (paddedSquare scale width hwidth).edges.map
    (fun e => (baseLinks width).idxOf e.link)

/-- Complete-carrier blocks touched by the square word. -/
def observableBlocks (scale width : Nat) (hwidth : side scale < width) : List Nat :=
  (List.range (N width)).filter
    (fun i => decide (i ∈ loopSlots scale width hwidth))

/-- Complete-carrier blocks not touched by the square word. -/
def spectatorBlocks (scale width : Nat) (hwidth : side scale < width) : List Nat :=
  (List.range (N width)).filter
    (fun i => !decide (i ∈ loopSlots scale width hwidth))

theorem loopSlots_length (scale width : Nat) (hwidth : side scale < width) :
    (loopSlots scale width hwidth).length = 4 * side scale := by
  unfold loopSlots
  rw [List.length_map, paddedSquare_edges, square_length]

theorem loopSlots_nodup (scale width : Nat) (hwidth : side scale < width) :
    (loopSlots scale width hwidth).Nodup := by
  exact paddedSquare_indices_nodup scale width hwidth

theorem observableBlocks_nodup (scale width : Nat) (hwidth : side scale < width) :
    (observableBlocks scale width hwidth).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))

theorem spectatorBlocks_nodup (scale width : Nat) (hwidth : side scale < width) :
    (spectatorBlocks scale width hwidth).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))

theorem observableBlocks_lt (scale width : Nat) (hwidth : side scale < width)
    (i : Nat) (hi : i ∈ observableBlocks scale width hwidth) : i < N width := by
  exact List.mem_range.mp (List.mem_filter.mp hi).1

theorem spectatorBlocks_lt (scale width : Nat) (hwidth : side scale < width)
    (i : Nat) (hi : i ∈ spectatorBlocks scale width hwidth) : i < N width := by
  exact List.mem_range.mp (List.mem_filter.mp hi).1

theorem spectator_not_observable (scale width : Nat) (hwidth : side scale < width)
    (i : Nat) (hs : i ∈ spectatorBlocks scale width hwidth) :
    i ∉ observableBlocks scale width hwidth := by
  intro ho
  have hs' := (List.mem_filter.mp hs).2
  have ho' := (List.mem_filter.mp ho).2
  simp_all

theorem spectator_observable_cover (scale width : Nat) (hwidth : side scale < width) :
    (spectatorBlocks scale width hwidth ++ observableBlocks scale width hwidth).Perm
      (List.range (N width)) := by
  simpa only [spectatorBlocks, observableBlocks, Bool.not_not] using
    (List.filter_append_perm
      (fun i => !decide (i ∈ loopSlots scale width hwidth))
      (List.range (N width)))

private theorem wordAt_sourceWord (width : Nat) :
    ∀ (es : List OrientedBF4Link),
      (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e :: es, hphysical => by
      have he := hphysical e List.mem_cons_self
      have ht : ∀ f, f ∈ es → f.link ∈ baseLinks width :=
        fun f hf => hphysical f (List.mem_cons_of_mem e hf)
      change PolyQuaternion.mul
          (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
          (wordAt (fun f => (baseLinks width).idxOf f.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es ht]
      unfold orientedLink link
      rw [if_pos he]
      rfl

private theorem padded_wordAt_sourceWord (scale width : Nat)
    (hwidth : side scale < width) :
    wordAt (fun e => (baseLinks width).idxOf e.link)
        (paddedSquare scale width hwidth).edges =
      sourceWord width (paddedSquare scale width hwidth).edges := by
  apply wordAt_sourceWord
  exact (paddedSquare scale width hwidth).physical

/-- Every spectator block is absent from every character of the literal square word. -/
theorem sourceCharacter_spectator_independent_allSpin
    (scale width : Nat) (hwidth : side scale < width) (i : Nat)
    (hi : i ∈ spectatorBlocks scale width hwidth) (spin : Nat) :
    QuaternionBlockIndependent i
      (sourceCharacter width (paddedSquare scale width hwidth).edges spin) := by
  have hnot : i ∉ loopSlots scale width hwidth := by
    intro hm
    have hb := (List.mem_filter.mp hi).2
    simp [hm] at hb
  have hd := word_independent i (fun e => (baseLinks width).idxOf e.link)
    (paddedSquare scale width hwidth).edges (by
      intro e he heq
      apply hnot
      exact List.mem_map.mpr ⟨e, he, heq.symm⟩)
  rw [padded_wordAt_sourceWord scale width hwidth] at hd
  exact degree_zero_independent (character_independent hd.scalar spin)

/-- Fundamental-character specialization used by the signed source-energy split. -/
theorem sourceCharacter_spectator_independent
    (scale width : Nat) (hwidth : side scale < width) (i : Nat)
    (hi : i ∈ spectatorBlocks scale width hwidth) :
    QuaternionBlockIndependent i
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) :=
  sourceCharacter_spectator_independent_allSpin scale width hwidth i hi 1

#print axioms loopSlots
#print axioms observableBlocks
#print axioms spectatorBlocks
#print axioms loopSlots_length
#print axioms loopSlots_nodup
#print axioms observableBlocks_nodup
#print axioms spectatorBlocks_nodup
#print axioms observableBlocks_lt
#print axioms spectatorBlocks_lt
#print axioms spectator_not_observable
#print axioms spectator_observable_cover
#print axioms sourceCharacter_spectator_independent_allSpin
#print axioms sourceCharacter_spectator_independent

end YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
