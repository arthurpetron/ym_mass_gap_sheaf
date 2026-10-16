/-
# Four-link physical support of the actual bulk-source rows

Each physical row underlying the heat-normalized bulk-source `A2` carrier is
one comb-gauge plaquette curl on one history slice.  This leaf gives an
explicit four-coordinate candidate list, one candidate for each oriented
link of the selected source face, and proves that every in-range coordinate
outside that list has coefficient zero.

The list is a support superset: a tree link may map to an out-of-range chord
index, and repeated candidates are harmless.  The result localizes the source
row itself but does not yet bound the LDL residual coefficients on those
coordinates or prove cutoff-uniform control.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourcePhysicalSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope

private def fallbackLink : Z4Link := ((0, 0, 0, 0), .x0)

private theorem getD_mem_local : ∀ {items : List Z4Link} {index : Nat},
    index < items.length → items.getD index fallbackLink ∈ items
  | [], _, hindex => absurd hindex (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: _tail, _index + 1, hindex =>
      List.mem_cons_of_mem _
        (getD_mem_local (Nat.lt_of_succ_lt_succ hindex))

private theorem idxOf_getD_local : ∀ (items : List Z4Link), items.Nodup →
    ∀ index, index < items.length →
      items.idxOf (items.getD index fallbackLink) = index
  | [], _, index, hindex => absurd hindex (Nat.not_lt_zero _)
  | head :: tail, _, 0, _ => by
      show (head :: tail).idxOf head = 0
      rw [List.idxOf_cons,
        show (head == head) = true from beq_iff_eq.mpr rfl]
      rfl
  | head :: tail, hnodup, index + 1, hindex => by
      have hnodup' := List.nodup_cons.mp hnodup
      have hindex' : index < tail.length := Nat.lt_of_succ_lt_succ hindex
      have hmem : tail.getD index fallbackLink ∈ tail :=
        getD_mem_local hindex'
      have hne : (head == tail.getD index fallbackLink) = false := by
        cases heq : (head == tail.getD index fallbackLink) with
        | false => rfl
        | true => exact absurd ((beq_iff_eq.mp heq) ▸ hmem) hnodup'.1
      show (head :: tail).idxOf
          (tail.getD index fallbackLink) = index + 1
      rw [List.idxOf_cons, hne, cond_false,
        idxOf_getD_local tail hnodup'.2 index hindex']

private theorem idxOf_selectedCombGaugeLink
    {width gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    (combGaugeLinks width).idxOf
        (selectedCombGaugeLink width gaugeIndex) = gaugeIndex := by
  unfold selectedCombGaugeLink
  unfold combGaugeEdgeCount at hgauge
  exact idxOf_getD_local (combGaugeLinks width)
    (combGaugeLinks_nodup width) gaugeIndex hgauge

private theorem historyIndex_decode
    {spatialSize coordinate : Nat} :
    historyIndex spatialSize
        (historyTime spatialSize coordinate)
        (historySpatial spatialSize coordinate) = coordinate := by
  unfold historyIndex historyTime historySpatial
  exact Nat.div_add_mod coordinate spatialSize

private theorem historySpatial_lt
    {timeBonds width coordinate : Nat}
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    historySpatial (combGaugeEdgeCount width) coordinate <
      combGaugeEdgeCount width := by
  unfold historySpatial
  apply Nat.mod_lt
  apply Nat.pos_of_ne_zero
  intro hzero
  unfold historyCoordinateCount at hcoordinate
  rw [hzero, Nat.mul_zero] at hcoordinate
  exact Nat.not_lt_zero coordinate hcoordinate

/-- Four explicit candidate history coordinates for one physical source curl
row, in the plaquette's oriented link order. -/
def bulkSourcePhysicalColorCurlCandidateCoordinates
    (side time rowIndex : Nat) : List Nat :=
  let width := bulkSourceWidth side
  let spatialSize := combGaugeEdgeCount width
  (edgesOf (selectedBulkSourceFace side (rowIndex / 3))).map fun link =>
    historyIndex spatialSize time ((combGaugeLinks width).idxOf link)

theorem bulkSourcePhysicalColorCurlCandidateCoordinates_length
    (side time rowIndex : Nat) :
    (bulkSourcePhysicalColorCurlCandidateCoordinates
      side time rowIndex).length = 4 := by
  rfl

/-- On the physical history prefix, every coordinate outside the four-link
candidate list has zero coefficient in the actual bulk-source physical row. -/
theorem bulkSourcePhysicalColorCurlRow_eq_zero_of_not_mem_candidates
    (timeBonds side time rowIndex coordinate : Nat)
    (hrowIndex : rowIndex < 3 * (bulkSourceFaces side).length)
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds
        (combGaugeEdgeCount (bulkSourceWidth side)))
    (hnot : coordinate ∉
      bulkSourcePhysicalColorCurlCandidateCoordinates
        side time rowIndex) :
    bulkSourcePhysicalColorCurlRow side time rowIndex coordinate = 0 := by
  let width := bulkSourceWidth side
  let spatialSize := combGaugeEdgeCount width
  let faceIndex := bulkSourceInternalFaceIndex side (rowIndex / 3)
  let face := selectedBulkSourceFace side (rowIndex / 3)
  have hsourceIndex : rowIndex / 3 < (bulkSourceFaces side).length := by
    omega
  have hsourceFace : face ∈ bulkSourceFaces side := by
    exact selectedBulkSourceFace_mem hsourceIndex
  have hinternalFace : face ∈ internalOpenCubeFaces width := by
    exact bulkSourceFace_internal hsourceFace
  have hfaceIndex : faceIndex < internalOpenCubeFaceCount width := by
    exact List.idxOf_lt_length_of_mem hinternalFace
  have hspatial : historySpatial spatialSize coordinate < spatialSize := by
    exact historySpatial_lt hcoordinate
  by_cases htime : historyTime spatialSize coordinate = time
  · let link := selectedCombGaugeLink width
      (historySpatial spatialSize coordinate)
    by_cases hlink : link ∈ edgesOf face
    · have hlinkGauge : link ∈ combGaugeLinks width := by
        exact selectedCombGaugeLink_mem hspatial
      have hlinkIndex :
          (combGaugeLinks width).idxOf link =
            historySpatial spatialSize coordinate := by
        exact idxOf_selectedCombGaugeLink hspatial
      have hcandidate : coordinate ∈
          bulkSourcePhysicalColorCurlCandidateCoordinates
            side time rowIndex := by
        unfold bulkSourcePhysicalColorCurlCandidateCoordinates
        apply List.mem_map.mpr
        refine ⟨link, ?_, ?_⟩
        · exact hlink
        · rw [hlinkIndex, ← htime]
          exact historyIndex_decode
      exact False.elim (hnot hcandidate)
    · unfold bulkSourcePhysicalColorCurlRow
        combGaugeFreeHistoryCurlRow
      rw [if_pos htime]
      unfold combGaugeCurl
      rw [if_pos ⟨hfaceIndex, hspatial⟩]
      have hselectedFace :
          selectedInternalOpenCubeFace width faceIndex = face := by
        exact selectedInternalOpenCubeFace_bulkSourceIndex hsourceIndex
      rw [hselectedFace]
      exact internalBoundaryCoefficient_zero_of_not_mem hlink
  · unfold bulkSourcePhysicalColorCurlRow
      combGaugeFreeHistoryCurlRow
    rw [if_neg htime]

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourcePhysicalSupport

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourcePhysicalSupport.bulkSourcePhysicalColorCurlCandidateCoordinates_length
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourcePhysicalSupport.bulkSourcePhysicalColorCurlRow_eq_zero_of_not_mem_candidates
