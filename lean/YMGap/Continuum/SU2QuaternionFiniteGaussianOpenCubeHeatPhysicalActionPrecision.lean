/-
# Physical action rows realize the open-cube FREE-history precision

The complete positive quadratic action uses one spatial-curl row for every
history slice and internal face, together with one forward temporal-difference
row for every temporal bond and comb-gauge coordinate.  This leaf proves
entrywise that the Gram of those physical rows is exactly the finite
FREE-history precision `L`.  Consequently twice this Gram is the heat
precision `2L` used by the checked heat covariance.

This is the physical-coordinate structural bridge only.  It does not yet
identify the literal three-color Heron-pulled plaquette/link row list with
these rows, bound the Heron residual, compare the ORIGINAL law, control higher
remainders, or establish a continuum theory or mass gap.
-/

import YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite

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

private theorem listQSum_append_local {Index : Type}
    (value : Index → Q') : ∀ left right : List Index,
    listQSum value (left ++ right) ≈
      listQSum value left + listQSum value right
  | [], _right => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _item :: items, right =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_append_local value items right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_indicator_present_local
    (bound selected : Nat) (value : Q') (hselected : selected < bound) :
    listQSum
        (fun index => if selected = index then value else 0)
        (List.range bound) ≈ value := by
  induction bound with
  | zero => exact False.elim (Nat.not_lt_zero selected hselected)
  | succ bound induction =>
      rw [List.range_succ]
      refine Q'.eqv_trans _
        (listQSum
            (fun index => if selected = index then value else 0)
            (List.range bound) +
          listQSum
            (fun index => if selected = index then value else 0)
            [bound]) _
        (listQSum_append_local
          (fun index => if selected = index then value else 0)
          (List.range bound) [bound]) ?_
      simp only [listQSum]
      rw [Q'.add_zero']
      by_cases heq : selected = bound
      · subst selected
        rw [if_pos rfl]
        have habsent : ∀ index, index ∈ List.range bound →
            (if bound = index then value else 0) ≈ 0 := by
          intro index membership
          rw [if_neg (Nat.ne_of_gt (List.mem_range.mp membership))]
          exact Q'.eqv_refl _
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _
              (listQSum_congr_local _ _ (List.range bound) habsent)
              (listQSum_zero_local (List.range bound)))
            (Q'.eqv_refl _))
          (Q'.eqv_of_eq (Q'.zero_add' _))
      · have hlt : selected < bound := by omega
        rw [if_neg heq]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (induction hlt)
            (Q'.eqv_refl _))
          (Q'.eqv_of_eq (Q'.add_zero' _))

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
  have htime :
      historyTime spatialSize coordinate < timeBonds + 1 := by
    unfold historyTime
    apply (Nat.div_lt_iff_lt_mul hspatialSize).2
    simpa only [historyCoordinateCount, historySliceCount,
      show combGaugeEdgeCount width = spatialSize from rfl] using hcoordinate
  have hspatial : historySpatial spatialSize coordinate < spatialSize := by
    unfold historySpatial
    exact Nat.mod_lt coordinate hspatialSize
  exact ⟨hspatialSize, htime, hspatial⟩

/-- One canonical physical spatial-action row: the selected comb curl on one
history slice. -/
def combGaugeFreeHistorySpatialActionRow
    (width time faceIndex coordinate : Nat) : Q' :=
  combGaugeFreeHistoryCurlRow width time faceIndex coordinate

/-- One canonical physical temporal-action row: the selected comb coordinate
on one forward temporal bond. -/
def combGaugeFreeHistoryTemporalActionRow
    (width bond gaugeIndex coordinate : Nat) : Q' :=
  if historySpatial (combGaugeEdgeCount width) coordinate = gaugeIndex then
    freeTemporalDifference bond
      (historyTime (combGaugeEdgeCount width) coordinate)
  else 0

/-- Complete physical action-row Gram: all spatial curls on all slices plus
all forward temporal differences on all comb-gauge coordinates. -/
def combGaugeFreeHistoryPhysicalActionGram
    (timeBonds width left right : Nat) : Q' :=
  listQSum
      (fun time => listQSum
        (fun faceIndex =>
          combGaugeFreeHistorySpatialActionRow width time faceIndex left *
            combGaugeFreeHistorySpatialActionRow width time faceIndex right)
        (List.range (internalOpenCubeFaceCount width)))
      (List.range (timeBonds + 1)) +
    listQSum
      (fun bond => listQSum
        (fun gaugeIndex =>
          combGaugeFreeHistoryTemporalActionRow width bond gaugeIndex left *
            combGaugeFreeHistoryTemporalActionRow width bond gaugeIndex right)
        (List.range (combGaugeEdgeCount width)))
      (List.range timeBonds)

private theorem spatialActionRow_face_sum
    (width time left right : Nat) :
    listQSum
        (fun faceIndex =>
          combGaugeFreeHistorySpatialActionRow width time faceIndex left *
            combGaugeFreeHistorySpatialActionRow width time faceIndex right)
        (List.range (internalOpenCubeFaceCount width)) ≈
      if historyTime (combGaugeEdgeCount width) left = time ∧
          historyTime (combGaugeEdgeCount width) right = time then
        combGaugeSpatialPrecision width
          (historySpatial (combGaugeEdgeCount width) left)
          (historySpatial (combGaugeEdgeCount width) right)
      else 0 := by
  by_cases htime :
      historyTime (combGaugeEdgeCount width) left = time ∧
        historyTime (combGaugeEdgeCount width) right = time
  · rw [if_pos htime]
    unfold combGaugeFreeHistorySpatialActionRow
      combGaugeFreeHistoryCurlRow combGaugeSpatialPrecision
      finiteCurlPrecision
    apply listQSum_congr_local
    intro faceIndex _membership
    rw [if_pos htime.1, if_pos htime.2]
    exact Q'.eqv_refl _
  · rw [if_neg htime]
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_local _ _
        (List.range (internalOpenCubeFaceCount width)) ?_)
      (listQSum_zero_local _)
    intro faceIndex _membership
    unfold combGaugeFreeHistorySpatialActionRow
      combGaugeFreeHistoryCurlRow
    by_cases hleft :
        historyTime (combGaugeEdgeCount width) left = time
    · have hright :
          historyTime (combGaugeEdgeCount width) right ≠ time := by
        intro hright
        exact htime ⟨hleft, hright⟩
      rw [if_pos hleft, if_neg hright]
      exact Q'.mul_zero_eqv _
    · rw [if_neg hleft]
      exact Q'.zero_mul_eqv _

private theorem spatialActionRow_slice_sum
    (timeBonds width left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    listQSum
        (fun time => listQSum
          (fun faceIndex =>
            combGaugeFreeHistorySpatialActionRow width time faceIndex left *
              combGaugeFreeHistorySpatialActionRow width time faceIndex right)
          (List.range (internalOpenCubeFaceCount width)))
        (List.range (timeBonds + 1)) ≈
      if historyTime (combGaugeEdgeCount width) left =
          historyTime (combGaugeEdgeCount width) right then
        combGaugeSpatialPrecision width
          (historySpatial (combGaugeEdgeCount width) left)
          (historySpatial (combGaugeEdgeCount width) right)
      else 0 := by
  have hleftData := historyCoordinate_data hleft
  have hrightData := historyCoordinate_data hright
  let leftTime := historyTime (combGaugeEdgeCount width) left
  let rightTime := historyTime (combGaugeEdgeCount width) right
  let spatialValue := combGaugeSpatialPrecision width
    (historySpatial (combGaugeEdgeCount width) left)
    (historySpatial (combGaugeEdgeCount width) right)
  refine Q'.eqv_trans _
    (listQSum
      (fun time => if leftTime = time ∧ rightTime = time then
        spatialValue else 0)
      (List.range (timeBonds + 1))) _ ?_ ?_
  · apply listQSum_congr_local
    intro time _membership
    exact spatialActionRow_face_sum width time left right
  · by_cases heq : leftTime = rightTime
    · rw [if_pos heq]
      refine Q'.eqv_trans _
        (listQSum
          (fun time => if leftTime = time then spatialValue else 0)
          (List.range (timeBonds + 1))) _ ?_ ?_
      · apply listQSum_congr_local
        intro time _membership
        by_cases htime : leftTime = time
        · have hrightTime : rightTime = time := heq.symm.trans htime
          rw [if_pos htime, if_pos ⟨htime, hrightTime⟩]
          exact Q'.eqv_refl _
        · rw [if_neg htime, if_neg]
          · exact Q'.eqv_refl _
          · intro both
            exact htime both.1
      · exact listQSum_indicator_present_local
          (timeBonds + 1) leftTime spatialValue hleftData.2.1
    · rw [if_neg heq]
      refine Q'.eqv_trans _ _ _
        (listQSum_congr_local _ _ (List.range (timeBonds + 1)) ?_)
        (listQSum_zero_local _)
      intro time _membership
      rw [if_neg]
      · exact Q'.eqv_refl _
      · intro both
        exact heq (both.1.trans both.2.symm)

private theorem temporalActionRow_gauge_sum
    (width bond left right : Nat)
    (hleftSpatial :
      historySpatial (combGaugeEdgeCount width) left <
        combGaugeEdgeCount width) :
    listQSum
        (fun gaugeIndex =>
          combGaugeFreeHistoryTemporalActionRow width bond gaugeIndex left *
            combGaugeFreeHistoryTemporalActionRow width bond gaugeIndex right)
        (List.range (combGaugeEdgeCount width)) ≈
      if historySpatial (combGaugeEdgeCount width) left =
          historySpatial (combGaugeEdgeCount width) right then
        freeTemporalDifference bond
            (historyTime (combGaugeEdgeCount width) left) *
          freeTemporalDifference bond
            (historyTime (combGaugeEdgeCount width) right)
      else 0 := by
  let leftSpatial := historySpatial (combGaugeEdgeCount width) left
  let rightSpatial := historySpatial (combGaugeEdgeCount width) right
  let temporalProduct :=
    freeTemporalDifference bond
        (historyTime (combGaugeEdgeCount width) left) *
      freeTemporalDifference bond
        (historyTime (combGaugeEdgeCount width) right)
  change listQSum
      (fun gaugeIndex =>
        (if leftSpatial = gaugeIndex then
            freeTemporalDifference bond
              (historyTime (combGaugeEdgeCount width) left)
          else 0) *
        (if rightSpatial = gaugeIndex then
            freeTemporalDifference bond
              (historyTime (combGaugeEdgeCount width) right)
          else 0))
      (List.range (combGaugeEdgeCount width)) ≈
    if leftSpatial = rightSpatial then temporalProduct else 0
  by_cases heq : leftSpatial = rightSpatial
  · rw [if_pos heq]
    refine Q'.eqv_trans _
      (listQSum
        (fun gaugeIndex =>
          if leftSpatial = gaugeIndex then temporalProduct else 0)
        (List.range (combGaugeEdgeCount width))) _ ?_ ?_
    · apply listQSum_congr_local
      intro gaugeIndex _membership
      by_cases hgauge : leftSpatial = gaugeIndex
      · have hrightGauge : rightSpatial = gaugeIndex := by
          exact heq.symm.trans hgauge
        simp only [if_pos hgauge, if_pos hrightGauge]
        exact Q'.eqv_refl _
      · have hrightGauge : rightSpatial ≠ gaugeIndex := by
          intro hrightGauge
          exact hgauge (heq.trans hrightGauge)
        simp only [if_neg hgauge, if_neg hrightGauge]
        exact Q'.zero_mul_eqv _
    · exact listQSum_indicator_present_local
        (combGaugeEdgeCount width) leftSpatial temporalProduct hleftSpatial
  · rw [if_neg heq]
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_local _ _
        (List.range (combGaugeEdgeCount width)) ?_)
      (listQSum_zero_local _)
    intro gaugeIndex _membership
    by_cases hleftGauge : leftSpatial = gaugeIndex
    · have hrightGauge : rightSpatial ≠ gaugeIndex := by
        intro hrightGauge
        exact heq (hleftGauge.trans hrightGauge.symm)
      simp only [if_pos hleftGauge, if_neg hrightGauge]
      exact Q'.mul_zero_eqv _
    · simp only [if_neg hleftGauge]
      exact Q'.zero_mul_eqv _

private theorem temporalActionRow_bond_sum
    (timeBonds width left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    listQSum
        (fun bond => listQSum
          (fun gaugeIndex =>
            combGaugeFreeHistoryTemporalActionRow width bond gaugeIndex left *
              combGaugeFreeHistoryTemporalActionRow width bond gaugeIndex right)
          (List.range (combGaugeEdgeCount width)))
        (List.range timeBonds) ≈
      if historySpatial (combGaugeEdgeCount width) left =
          historySpatial (combGaugeEdgeCount width) right then
        freeTemporalPrecision timeBonds
          (historyTime (combGaugeEdgeCount width) left)
          (historyTime (combGaugeEdgeCount width) right)
      else 0 := by
  have hleftData := historyCoordinate_data hleft
  have hrightData := historyCoordinate_data hright
  let leftTime := historyTime (combGaugeEdgeCount width) left
  let rightTime := historyTime (combGaugeEdgeCount width) right
  by_cases hspace :
      historySpatial (combGaugeEdgeCount width) left =
        historySpatial (combGaugeEdgeCount width) right
  · rw [if_pos hspace]
    refine Q'.eqv_trans _
      (listQSum
        (fun bond =>
          freeTemporalDifference bond leftTime *
            freeTemporalDifference bond rightTime)
        (List.range timeBonds)) _ ?_ ?_
    · apply listQSum_congr_local
      intro bond _membership
      exact Q'.eqv_trans _ _ _
        (temporalActionRow_gauge_sum
          width bond left right hleftData.2.2)
        (Q'.eqv_of_eq (if_pos hspace))
    · refine Q'.eqv_trans _
        (weightedGram (List.range timeBonds) (fun _bond => (1 : Q'))
          (fun time bond => freeTemporalDifference bond time)
          leftTime rightTime) _ ?_ ?_
      · unfold weightedGram
        apply listQSum_congr_local
        intro bond _membership
        exact Q'.eqv_symm (Q'.one_mul_eqv _)
      · exact freeTemporalDifference_gram timeBonds leftTime rightTime
          hleftData.2.1 hrightData.2.1
  · rw [if_neg hspace]
    refine Q'.eqv_trans _
      (listQSum (fun _bond => (0 : Q')) (List.range timeBonds)) _ ?_ ?_
    · apply listQSum_congr_local
      intro bond _membership
      exact Q'.eqv_trans _ _ _
        (temporalActionRow_gauge_sum
          width bond left right hleftData.2.2)
        (Q'.eqv_of_eq (if_neg hspace))
    · exact listQSum_zero_local _

/-- Entrywise Gram identity for the complete physical spatial-plus-temporal
action row family. -/
theorem combGaugeFreeHistoryPhysicalActionGram_eq_precision
    (timeBonds width left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    combGaugeFreeHistoryPhysicalActionGram
        timeBonds width left right ≈
      combGaugeFreeHistoryPrecision timeBonds width left right := by
  unfold combGaugeFreeHistoryPhysicalActionGram
    combGaugeFreeHistoryPrecision freeHistoryCurlPrecision
    freeHistoryPrecision
  exact Q'.add_eqv_congr'
    (spatialActionRow_slice_sum timeBonds width left right hleft hright)
    (temporalActionRow_bond_sum timeBonds width left right hleft hright)

/-- Twice the complete physical action-row Gram is exactly the doubled heat
precision used by the finite heat covariance. -/
theorem twice_combGaugeFreeHistoryPhysicalActionGram_eq_heatPrecision
    (timeBonds width left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    2 * combGaugeFreeHistoryPhysicalActionGram
        timeBonds width left right ≈
      combGaugeHeatFreeHistoryPrecision timeBonds width left right := by
  unfold combGaugeHeatFreeHistoryPrecision
  exact Q'.mul_eqv_congr_left 2 _ _
    (combGaugeFreeHistoryPhysicalActionGram_eq_precision
      timeBonds width left right hleft hright)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision.combGaugeFreeHistoryPhysicalActionGram_eq_precision
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision.twice_combGaugeFreeHistoryPhysicalActionGram_eq_heatPrecision
