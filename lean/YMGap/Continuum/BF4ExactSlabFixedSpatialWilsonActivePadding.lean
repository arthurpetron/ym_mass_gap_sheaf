/-
# Strict spatial padding activates a fixed Wilson loop

A source loop at `base` uses spatial links whose three base coordinates are
at most `base`.  Once it is included without translation into a strictly
larger width, those coordinates are strictly interior, hence every literal
loop edge belongs to the original kinetic active-index list.  The strict
width guard is retained: this does not claim that fringe edges are active at
their source width, and it adds no analytic assumption.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
  (StrictSliceLink active_index_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeLoop_edges)

/-- Every edge of a fixed source loop is active at any strictly larger width.
The link itself is unchanged; only the ambient source-box witness grows. -/
theorem source_edges_active_after_padding {base width : Nat} (hwidth : base < width)
    (loop : SourceLoop base) (e : OrientedBF4Link) (he : e ∈ loop.edges) :
    (baseLinks width).idxOf e.link ∈ activeBlocks width := by
  have hb := loop.physical e he
  rcases e with ⟨⟨⟨x, y, z, t⟩, dir⟩, reverse⟩
  have hs := (baseLinks_mem_iff base ((x, y, z, t), dir)).mp hb
  change dir ≠ .x3 ∧ x ≤ base ∧ y ≤ base ∧ z ≤ base ∧ t = 0 at hs
  have hw : ((x, y, z, t), dir) ∈ baseLinks width := by
    apply (baseLinks_mem_iff width _).mpr
    change dir ≠ .x3 ∧ x ≤ width ∧ y ≤ width ∧ z ≤ width ∧ t = 0
    exact ⟨hs.1, by omega, by omega, by omega, hs.2.2.2.2⟩
  apply (active_index_iff width ((x, y, z, t), dir) hw).mpr
  simp only [StrictSliceLink, SliceLink]
  exact ⟨⟨hs.1, by omega, by omega, by omega, hs.2.2.2.2⟩,
    by omega, by omega, by omega⟩

/-- The existing zero-translation inclusion of a source loop has only active
edges whenever the target width is strictly larger than the source width. -/
theorem includedLoop_edges_active {base width : Nat} (hwidth : base < width)
    (loop : SourceLoop base) :
    ∀ e, e ∈ (recenterLoop (space := 0)
        (by omega : base + 0 ≤ width) loop).edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width := by
  intro e he
  apply source_edges_active_after_padding hwidth loop e
  rw [← includeLoop_edges (Nat.le_of_lt hwidth) loop]
  exact he

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding.source_edges_active_after_padding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding.includedLoop_edges_active
