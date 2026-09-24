/-
# Exact time placement of the dyadic Wilson square's selected edge

The literal padded square remains a forward selected head followed by a tail
that omits the selected underlying link after the exact `shiftEntry` placement
used by `placedPolynomial`.  The selected head and every tail entry are also
physical in each admissible original ambient slab.  This is finite geometry
for the original window action, not an action comparison or variance theorem.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe

namespace YMGap.Continuum.BF4DyadicWilsonSquarePlacedGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (shiftEntry placeLoop)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge

/-- The selected underlying link on the literal time-`time` placement. -/
def placedSelectedLink (time : Nat) : Z4Link :=
  timeShiftLink time selectedLink

/-- The selected incidence stays forward under time placement. -/
def placedSelectedEdge (time : Nat) : OrientedBF4Link :=
  ⟨placedSelectedLink time, false⟩

/-- The canonical dyadic tail after the same literal time placement. -/
def placedDyadicTail (scale time : Nat) : List OrientedBF4Link :=
  (dyadicTail scale).map (shiftEntry time)

/-- The placed padded word has the exact selected-forward-head shape consumed
by the arbitrary selected-action one-link theorem. -/
theorem paddedSquare_placed_edges_split
    (scale width : Nat) (hwidth : side scale < width) (time : Nat) :
    (paddedSquare scale width hwidth).edges.map (shiftEntry time) =
      placedSelectedEdge time :: placedDyadicTail scale time := by
  rw [paddedSquare_edges_split]
  rfl

private theorem timeShiftLink_injective (time : Nat) {left right : Z4Link}
    (h : timeShiftLink time left = timeShiftLink time right) : left = right := by
  rcases left with ⟨⟨x,y,z,t⟩,dir⟩
  rcases right with ⟨⟨x',y',z',t'⟩,dir'⟩
  simpa only [timeShiftLink, timeShiftVertex, Prod.mk.injEq,
    Nat.add_right_cancel_iff] using h

/-- No orientation of the shifted selected underlying link occurs in the
placed tail. -/
theorem placedSelectedLink_not_mem_placedDyadicTail (scale time : Nat) :
    ∀ entry, entry ∈ placedDyadicTail scale time →
      entry.link ≠ placedSelectedLink time := by
  intro entry he hlink
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp he
  have hsource : source.link = selectedLink :=
    timeShiftLink_injective time hlink
  exact (selectedLink_not_mem_dyadicTail scale source hs) hsource

private theorem placedEdge_physical
    (scale width extent : Nat) (hwidth : side scale < width)
    (hambient : width ≤ extent) (time : Nat) (htime : time ≤ extent)
    (entry : OrientedBF4Link)
    (he : entry ∈ (paddedSquare scale width hwidth).edges.map (shiftEntry time)) :
    entry.link ∈ boundaryCompleteSlabLinks extent := by
  exact (placeLoop hambient htime (paddedSquare scale width hwidth)).physical entry he

/-- The placed selected head is an actual physical link of the same ambient
original slab used by the window finite value. -/
theorem placedSelectedLink_physical
    (scale width extent : Nat) (hwidth : side scale < width)
    (hambient : width ≤ extent) (time : Nat) (htime : time ≤ extent) :
    placedSelectedLink time ∈ boundaryCompleteSlabLinks extent := by
  have he : placedSelectedEdge time ∈
      (paddedSquare scale width hwidth).edges.map (shiftEntry time) := by
    rw [paddedSquare_placed_edges_split]
    exact List.mem_cons_self
  exact placedEdge_physical scale width extent hwidth hambient time htime
    (placedSelectedEdge time) he

/-- Every entry of the placed canonical tail is physical in the same ambient
original slab. -/
theorem placedDyadicTail_physical
    (scale width extent : Nat) (hwidth : side scale < width)
    (hambient : width ≤ extent) (time : Nat) (htime : time ≤ extent) :
    ∀ entry, entry ∈ placedDyadicTail scale time →
      entry.link ∈ boundaryCompleteSlabLinks extent := by
  intro entry he
  have hall : entry ∈
      (paddedSquare scale width hwidth).edges.map (shiftEntry time) := by
    rw [paddedSquare_placed_edges_split]
    exact List.mem_cons_of_mem (placedSelectedEdge time) he
  exact placedEdge_physical scale width extent hwidth hambient time htime entry hall

#print axioms placedSelectedLink
#print axioms placedSelectedEdge
#print axioms placedDyadicTail
#print axioms paddedSquare_placed_edges_split
#print axioms placedSelectedLink_not_mem_placedDyadicTail
#print axioms placedSelectedLink_physical
#print axioms placedDyadicTail_physical

end YMGap.Continuum.BF4DyadicWilsonSquarePlacedGeometry
