/-
# Single-link moments of the actual padded dyadic Wilson square

The canonical southwest edge of the literal padded dyadic square occurs as
the forward head and nowhere in its tail.  After placing the width carrier in
an admissible original slab, the existing one-link word calculation therefore
gives exact first and second moments against the unchanged complementary heat
product.  This is finite original-carrier input only, not a variance or
scaling theorem.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge
import YMGap.Continuum.BF4ExactSlabWilsonWordSingleLinkMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier

namespace YMGap.Continuum.BF4DyadicWilsonSquareSingleLinkMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (character)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry (complementHeat)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge
open YMGap.Continuum.BF4ExactSlabWilsonWordSingleLinkMoments

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem baseLink_physical_in_ambient
    {width extent : Nat} (hambient : width ≤ extent) {link : Z4Link}
    (hlink : link ∈ BF4ExactSlabFixedSpatialSliceCarrier.baseLinks width) :
    link ∈ boundaryCompleteSlabLinks extent :=
  BF4ExactSlabFixedSpatialBoundaryCarrier.sliceLink_physical
    hambient (Nat.zero_le extent) ((baseLinks_mem_iff width link).mp hlink)

private theorem selectedLink_physical
    (scale width extent : Nat) (hwidth : side scale < width)
    (hambient : width ≤ extent) :
    selectedLink ∈ boundaryCompleteSlabLinks extent := by
  have hm := selectedEdge_mem_paddedSquare scale width hwidth
  have hb := (paddedSquare scale width hwidth).physical selectedEdge hm
  change selectedLink ∈ _
  exact baseLink_physical_in_ambient hambient hb

private theorem dyadicTail_physical
    (scale width extent : Nat) (hwidth : side scale < width)
    (hambient : width ≤ extent) :
    ∀ entry, entry ∈ dyadicTail scale →
      entry.link ∈ boundaryCompleteSlabLinks extent := by
  intro entry he
  have hall : entry ∈ (paddedSquare scale width hwidth).edges := by
    rw [paddedSquare_edges_split]
    exact List.mem_cons_of_mem selectedEdge he
  exact baseLink_physical_in_ambient hambient
    ((paddedSquare scale width hwidth).physical entry hall)

/-- The actual padded square character has zero first moment against the full
selected-link complementary heat product in every admissible ambient slab. -/
theorem paddedSquare_complement_first_moment
    (w : Q') (K scale width extent : Nat)
    (hwidth : side scale < width) (hambient : width ≤ extent) :
    quaternionHaar (B extent)
      (polyMul (character extent (paddedSquare scale width hwidth).edges 1)
        (complementHeat w K extent selectedLink)) ≈ 0 := by
  rw [paddedSquare_edges_split]
  simpa only [selectedEdge, selectedLink] using
    (original_word_complement_first_moment w K extent selectedLink
      (selectedLink_physical scale width extent hwidth hambient)
      (dyadicTail scale) (selectedLink_not_mem_dyadicTail scale))

/-- The square of the same actual padded character integrates to the
untouched complementary heat spectator. -/
theorem paddedSquare_complement_second_moment
    (w : Q') (K scale width extent : Nat)
    (hwidth : side scale < width) (hambient : width ≤ extent) :
    quaternionHaar (B extent)
      (polyMul
        (polyMul (character extent (paddedSquare scale width hwidth).edges 1)
          (character extent (paddedSquare scale width hwidth).edges 1))
        (complementHeat w K extent selectedLink)) ≈
      quaternionHaar (B extent) (complementHeat w K extent selectedLink) := by
  rw [paddedSquare_edges_split]
  simpa only [selectedEdge, selectedLink] using
    (original_word_complement_second_moment w K extent selectedLink
      (selectedLink_physical scale width extent hwidth hambient)
      (dyadicTail scale)
      (dyadicTail_physical scale width extent hwidth hambient)
      (selectedLink_not_mem_dyadicTail scale))

#print axioms paddedSquare_complement_first_moment
#print axioms paddedSquare_complement_second_moment

end YMGap.Continuum.BF4DyadicWilsonSquareSingleLinkMoments
