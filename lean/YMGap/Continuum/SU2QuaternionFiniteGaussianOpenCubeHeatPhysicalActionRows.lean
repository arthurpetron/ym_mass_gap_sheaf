/-
# Literal open-cube action rows equal the canonical physical rows

The spatial heat action is written using the four directed link rows of each
plaquette, while the precision theorem uses one comb-curl row.  The kinetic
heat action uses the difference `slice(bond)-slice(bond+1)`, while the
canonical temporal incidence uses the opposite orientation.  This leaf proves
the exact pointwise identifications on the finite physical history carrier:

* the directed plaquette link sum is the corresponding comb-curl row;
* the kinetic link difference is the negative temporal-incidence row.

The kinetic sign disappears in the quadratic action Gram.  This file does not
yet pull these physical identities through the three-color Heron transform,
bound the covariance residual, compare the ORIGINAL law, control higher
remainders, or establish a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlKernel
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_congr_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (listQSum_congr_local left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem listQSum_zero_local {Index : Type} :
    ∀ items : List Index, listQSum (fun _item => (0 : Q')) items ≈ 0
  | [] => Q'.eqv_refl _
  | _item :: items =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_zero_local items))
        (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem listQSum_indicator_present_local
    (bound selected : Nat) (value : Q') (hselected : selected < bound) :
    listQSum
        (fun index => if selected = index then value else 0)
        (List.range bound) ≈ value := by
  exact listQSum_ite_single selected (fun _index => value)
    (List.range bound) (rangeNodupLocal bound)
    (List.mem_range.mpr hselected)

private theorem historyIndex_decode
    {spatialSize coordinate : Nat} :
    historyIndex spatialSize
        (historyTime spatialSize coordinate)
        (historySpatial spatialSize coordinate) = coordinate := by
  unfold historyIndex historyTime historySpatial
  exact Nat.div_add_mod coordinate spatialSize

private theorem historyCoordinate_data
    {timeBonds width coordinate : Nat}
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    let spatialSize := combGaugeEdgeCount width
    0 < spatialSize ∧
      historyTime spatialSize coordinate < timeBonds + 1 ∧
      historySpatial spatialSize coordinate < spatialSize := by
  let spatialSize := combGaugeEdgeCount width
  have hspatialSize : 0 < spatialSize := by
    apply Nat.pos_of_ne_zero
    intro hzero
    unfold historyCoordinateCount at hcoordinate
    rw [show combGaugeEdgeCount width = spatialSize from rfl,
      hzero, Nat.mul_zero] at hcoordinate
    exact Nat.not_lt_zero coordinate hcoordinate
  have htime : historyTime spatialSize coordinate < timeBonds + 1 := by
    unfold historyTime
    apply (Nat.div_lt_iff_lt_mul hspatialSize).2
    simpa only [historyCoordinateCount, historySliceCount,
      show combGaugeEdgeCount width = spatialSize from rfl] using hcoordinate
  have hspatial : historySpatial spatialSize coordinate < spatialSize := by
    unfold historySpatial
    exact Nat.mod_lt coordinate hspatialSize
  exact ⟨hspatialSize, htime, hspatial⟩

/-- The literal directed physical link sum in plaquette word order. -/
def combGaugeFreeHistoryPlaquettePhysicalActionRow
    (width time : Nat) (face : Z4Plaq) (coordinate : Nat) : Q' :=
  combGaugeFreeHistoryLinkRow width time (faceLinkA face) coordinate +
    (combGaugeFreeHistoryLinkRow width time (faceLinkB face) coordinate +
      (-combGaugeFreeHistoryLinkRow width time (faceLinkC face) coordinate +
        -combGaugeFreeHistoryLinkRow width time (faceLinkD face) coordinate))

/-- The literal physical forward link difference used by the kinetic action. -/
def combGaugeFreeHistoryKineticPhysicalActionRow
    (width bond : Nat) (link : Z4Link) (coordinate : Nat) : Q' :=
  combGaugeFreeHistoryLinkRow width bond link coordinate +
    -combGaugeFreeHistoryLinkRow width (bond + 1) link coordinate

private theorem combGaugeFreeHistoryLinkRow_components
    {timeBonds width time coordinate : Nat} {link : Z4Link}
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hlink : link ∈ combGaugeLinks width) :
    combGaugeFreeHistoryLinkRow width time link coordinate =
      if historyTime (combGaugeEdgeCount width) coordinate = time ∧
          historySpatial (combGaugeEdgeCount width) coordinate =
            (combGaugeLinks width).idxOf link then 1 else 0 := by
  have hdata := historyCoordinate_data hcoordinate
  have hlinkIndex :
      (combGaugeLinks width).idxOf link < combGaugeEdgeCount width :=
    List.idxOf_lt_length_of_mem hlink
  unfold combGaugeFreeHistoryLinkRow
  rw [if_pos hlink]
  by_cases hcomponents :
      historyTime (combGaugeEdgeCount width) coordinate = time ∧
        historySpatial (combGaugeEdgeCount width) coordinate =
          (combGaugeLinks width).idxOf link
  · rw [if_pos hcomponents, if_pos]
    · simpa only [hcomponents.1, hcomponents.2] using
        (historyIndex_decode
          (spatialSize := combGaugeEdgeCount width)
          (coordinate := coordinate)).symm
  · rw [if_neg hcomponents, if_neg]
    intro heq
    apply hcomponents
    constructor
    · have htime := congrArg
        (historyTime (combGaugeEdgeCount width)) heq
      rw [historyTime_index hdata.1 hlinkIndex] at htime
      exact htime
    · have hspatial := congrArg
        (historySpatial (combGaugeEdgeCount width)) heq
      rw [historySpatial_index hlinkIndex] at hspatial
      exact hspatial

private theorem combGaugeFreeHistoryLinkRow_zero_of_time_ne
    {timeBonds width time coordinate : Nat} {link : Z4Link}
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (htime : historyTime (combGaugeEdgeCount width) coordinate ≠ time) :
    combGaugeFreeHistoryLinkRow width time link coordinate = 0 := by
  by_cases hlink : link ∈ combGaugeLinks width
  · rw [combGaugeFreeHistoryLinkRow_components hcoordinate hlink,
      if_neg]
    exact fun hcomponents => htime hcomponents.1
  · unfold combGaugeFreeHistoryLinkRow
    rw [if_neg hlink]

private theorem combGaugeFreeHistoryLinkRow_eq_coordinateField
    {timeBonds width time coordinate : Nat} (link : Z4Link)
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (htime : historyTime (combGaugeEdgeCount width) coordinate = time) :
    combGaugeFreeHistoryLinkRow width time link coordinate =
      combGaugeCoordinateField width
        (fun gaugeIndex =>
          if gaugeIndex =
              historySpatial (combGaugeEdgeCount width) coordinate then 1 else 0)
        link := by
  by_cases hlink : link ∈ combGaugeLinks width
  · rw [combGaugeFreeHistoryLinkRow_components hcoordinate hlink]
    unfold combGaugeCoordinateField
    rw [if_pos hlink]
    change (if historyTime (combGaugeEdgeCount width) coordinate = time ∧
          historySpatial (combGaugeEdgeCount width) coordinate =
            (combGaugeLinks width).idxOf link then 1 else 0) =
      (if (combGaugeLinks width).idxOf link =
          historySpatial (combGaugeEdgeCount width) coordinate then 1 else 0)
    by_cases hspatial :
        historySpatial (combGaugeEdgeCount width) coordinate =
          (combGaugeLinks width).idxOf link
    · rw [if_pos ⟨htime, hspatial⟩, if_pos hspatial.symm]
    · rw [if_neg, if_neg]
      · exact fun hreverse => hspatial hreverse.symm
      · exact fun hcomponents => hspatial hcomponents.2
  · unfold combGaugeFreeHistoryLinkRow combGaugeCoordinateField
    rw [if_neg hlink, if_neg hlink]

private theorem combGaugeCurlApply_coordinate_indicator
    {width faceIndex gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    combGaugeCurlApply width faceIndex
        (fun index => if index = gaugeIndex then 1 else 0) ≈
      combGaugeCurl width faceIndex gaugeIndex := by
  unfold combGaugeCurlApply
  refine Q'.eqv_trans _
    (listQSum
      (fun index => if gaugeIndex = index then
        combGaugeCurl width faceIndex gaugeIndex else 0)
      (List.range (combGaugeEdgeCount width))) _ ?_ ?_
  · apply listQSum_congr_local
    intro index _membership
    change combGaugeCurl width faceIndex index *
        (if index = gaugeIndex then 1 else 0) ≈
      if gaugeIndex = index then
        combGaugeCurl width faceIndex gaugeIndex else 0
    by_cases heq : index = gaugeIndex
    · subst index
      simp only
      exact Q'.mul_one_eqv _
    · have hreverse : gaugeIndex ≠ index := fun h => heq h.symm
      simp only [if_neg heq, if_neg hreverse]
      exact Q'.mul_zero_eqv _
  · exact listQSum_indicator_present_local
      (combGaugeEdgeCount width) gaugeIndex
      (combGaugeCurl width faceIndex gaugeIndex) hgauge

/-- On the finite physical history prefix, the literal directed plaquette
link sum is exactly the corresponding canonical comb-curl action row. -/
theorem combGaugeFreeHistoryPlaquettePhysicalActionRow_eq_spatialActionRow
    (timeBonds width time coordinate : Nat) (face : Z4Plaq)
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hface : face ∈ internalOpenCubeFaces width) :
    combGaugeFreeHistoryPlaquettePhysicalActionRow
        width time face coordinate ≈
      combGaugeFreeHistorySpatialActionRow width time
        ((internalOpenCubeFaces width).idxOf face) coordinate := by
  let faceIndex := (internalOpenCubeFaces width).idxOf face
  have hfaceIndex : faceIndex < internalOpenCubeFaceCount width :=
    List.idxOf_lt_length_of_mem hface
  have hdata := historyCoordinate_data hcoordinate
  by_cases htime :
      historyTime (combGaugeEdgeCount width) coordinate = time
  · have hA := combGaugeFreeHistoryLinkRow_eq_coordinateField
      (timeBonds := timeBonds) (faceLinkA face) hcoordinate htime
    have hB := combGaugeFreeHistoryLinkRow_eq_coordinateField
      (timeBonds := timeBonds) (faceLinkB face) hcoordinate htime
    have hC := combGaugeFreeHistoryLinkRow_eq_coordinateField
      (timeBonds := timeBonds) (faceLinkC face) hcoordinate htime
    have hD := combGaugeFreeHistoryLinkRow_eq_coordinateField
      (timeBonds := timeBonds) (faceLinkD face) hcoordinate htime
    let coordinateField := combGaugeCoordinateField width
      (fun gaugeIndex =>
        if gaugeIndex =
            historySpatial (combGaugeEdgeCount width) coordinate then 1 else 0)
    have hphysical :
        combGaugeFreeHistoryPlaquettePhysicalActionRow
            width time face coordinate ≈
          combGaugeFaceCurl coordinateField face := by
      unfold combGaugeFreeHistoryPlaquettePhysicalActionRow
        combGaugeFaceCurl coordinateField
      exact Q'.add_eqv_congr' (Q'.eqv_of_eq hA)
        (Q'.add_eqv_congr' (Q'.eqv_of_eq hB)
          (Q'.add_eqv_congr'
            (Q'.neg_eqv_congr _ _ (Q'.eqv_of_eq hC))
            (Q'.neg_eqv_congr _ _ (Q'.eqv_of_eq hD))))
    have hsemantic := combGaugeCurlApply_eq_faceCurl
      (width := width) (faceIndex := faceIndex)
      (fun gaugeIndex =>
        if gaugeIndex =
            historySpatial (combGaugeEdgeCount width) coordinate then 1 else 0)
      hfaceIndex
    rw [selectedInternalOpenCubeFace_idxOf hface] at hsemantic
    unfold combGaugeFreeHistorySpatialActionRow
      combGaugeFreeHistoryCurlRow
    rw [if_pos htime]
    exact Q'.eqv_trans _ _ _ hphysical
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hsemantic)
        (combGaugeCurlApply_coordinate_indicator hdata.2.2))
  · have hA := combGaugeFreeHistoryLinkRow_zero_of_time_ne
      (timeBonds := timeBonds) (link := faceLinkA face) hcoordinate htime
    have hB := combGaugeFreeHistoryLinkRow_zero_of_time_ne
      (timeBonds := timeBonds) (link := faceLinkB face) hcoordinate htime
    have hC := combGaugeFreeHistoryLinkRow_zero_of_time_ne
      (timeBonds := timeBonds) (link := faceLinkC face) hcoordinate htime
    have hD := combGaugeFreeHistoryLinkRow_zero_of_time_ne
      (timeBonds := timeBonds) (link := faceLinkD face) hcoordinate htime
    unfold combGaugeFreeHistoryPlaquettePhysicalActionRow
      combGaugeFreeHistorySpatialActionRow combGaugeFreeHistoryCurlRow
    rw [hA, hB, hC, hD, if_neg htime]
    decide

/-- On the finite physical history prefix, the literal kinetic link
difference is the negative canonical temporal-incidence row. -/
theorem combGaugeFreeHistoryKineticPhysicalActionRow_eq_neg_temporalActionRow
    (timeBonds width bond coordinate : Nat) (link : Z4Link)
    (hcoordinate : coordinate <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hlink : link ∈ combGaugeLinks width) :
    combGaugeFreeHistoryKineticPhysicalActionRow
        width bond link coordinate ≈
      -combGaugeFreeHistoryTemporalActionRow width bond
        ((combGaugeLinks width).idxOf link) coordinate := by
  have hleft := combGaugeFreeHistoryLinkRow_components
    (time := bond) hcoordinate hlink
  have hright := combGaugeFreeHistoryLinkRow_components
    (time := bond + 1) hcoordinate hlink
  let coordinateTime := historyTime (combGaugeEdgeCount width) coordinate
  let coordinateSpatial := historySpatial (combGaugeEdgeCount width) coordinate
  let gaugeIndex := (combGaugeLinks width).idxOf link
  unfold combGaugeFreeHistoryKineticPhysicalActionRow
    combGaugeFreeHistoryTemporalActionRow
  rw [hleft, hright]
  by_cases hspace : coordinateSpatial = gaugeIndex
  · rw [if_pos hspace]
    by_cases hbond : coordinateTime = bond
    · have hnext : coordinateTime ≠ bond + 1 := by omega
      rw [if_pos ⟨hbond, hspace⟩, if_neg, freeTemporalDifference,
        if_pos hbond]
      · decide
      · exact fun h => hnext h.1
    · by_cases hnext : coordinateTime = bond + 1
      · rw [if_neg, if_pos ⟨hnext, hspace⟩, freeTemporalDifference,
          if_neg hbond, if_pos hnext]
        · decide
        · exact fun h => hbond h.1
      · rw [if_neg, if_neg, freeTemporalDifference,
          if_neg hbond, if_neg hnext]
        · decide
        · exact fun h => hnext h.1
        · exact fun h => hbond h.1
  · rw [if_neg hspace, if_neg, if_neg]
    · decide
    · exact fun h => hspace h.2
    · exact fun h => hspace h.2

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows.combGaugeFreeHistoryPlaquettePhysicalActionRow_eq_spatialActionRow
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows.combGaugeFreeHistoryKineticPhysicalActionRow_eq_neg_temporalActionRow
