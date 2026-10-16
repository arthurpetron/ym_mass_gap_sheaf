/-
# Four-support localization of the bulk-source first-order heat coefficient

The source-specialized first-order coefficient from the complete heat action
scaling-kernel bound is initially written as a double sum over the entire
physical history carrier.  The checked four-link support certificate allows
both sums to be filtered exactly to coordinates belonging to the corresponding
source-row candidate lists.

This removes dimension growth coming merely from summing zero source-row
coordinates.  The surviving LDL residual coefficients can still depend on
cutoff and volume, and no uniform bound or sign is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourcePhysicalSupport

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourcePhysicalSupport

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem listQSum_eq_filter_of_zero_local
    {Index : Type} (value : Index → Q') (test : Index → Bool) :
    ∀ items : List Index,
      (∀ item, item ∈ items → test item = false → value item ≈ 0) →
      listQSum value items ≈ listQSum value (items.filter test)
  | [], _ => Q'.eqv_refl 0
  | item :: items, hzero => by
      have htail : ∀ other, other ∈ items → test other = false →
          value other ≈ 0 := by
        intro other membership htest
        exact hzero other (List.mem_cons_of_mem item membership) htest
      cases htest : test item with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum value (items.filter test)) _
            (Q'.add_eqv_congr'
              (hzero item List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test items htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test items htail)

private theorem listQSum_eqv_zero_of_pointwise_local
    {Index : Type} (value : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | item :: items, hzero => by
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (hzero item List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise_local value items
            (fun other membership =>
              hzero other (List.mem_cons_of_mem item membership)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem envelopeTerm_eqv_zero_of_left_zero
    (left right entry : Q') (hleft : left = 0) :
    Q'.abs (left * right) * entry ≈ 0 := by
  subst left
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ entry
      (Q'.eqv_trans _ _ _
        (ExpNeg.abs_eqv_congr (Q'.zero_mul_eqv right))
        (Q'.eqv_of_eq TrigAdd.abs_zero_eq)))
    (Q'.zero_mul_eqv entry)

private theorem envelopeTerm_eqv_zero_of_right_zero
    (left right entry : Q') (hright : right = 0) :
    Q'.abs (left * right) * entry ≈ 0 := by
  subst right
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ entry
      (Q'.eqv_trans _ _ _
        (ExpNeg.abs_eqv_congr (Q'.mul_zero_eqv left))
        (Q'.eqv_of_eq TrigAdd.abs_zero_eq)))
    (Q'.zero_mul_eqv entry)

/-- In-range physical coordinates retained by the four-link support candidate
for one actual bulk-source row. -/
def bulkSourcePhysicalColorCurlSupportedCoordinates
    (timeBonds side time rowIndex : Nat) : List Nat :=
  let n := historyCoordinateCount timeBonds
    (combGaugeEdgeCount (bulkSourceWidth side))
  (List.range n).filter fun coordinate =>
    decide (coordinate ∈
      bulkSourcePhysicalColorCurlCandidateCoordinates side time rowIndex)

theorem bulkSourcePhysicalColorCurlSupportedCoordinates_mem
    {timeBonds side time rowIndex coordinate : Nat}
    (hmembership : coordinate ∈
      bulkSourcePhysicalColorCurlSupportedCoordinates
        timeBonds side time rowIndex) :
    coordinate < historyCoordinateCount timeBonds
        (combGaugeEdgeCount (bulkSourceWidth side)) ∧
      coordinate ∈ bulkSourcePhysicalColorCurlCandidateCoordinates
        side time rowIndex := by
  unfold bulkSourcePhysicalColorCurlSupportedCoordinates at hmembership
  have hparts := List.mem_filter.mp hmembership
  exact ⟨List.mem_range.mp hparts.1, of_decide_eq_true hparts.2⟩

/-- First-order heat-scaling coefficient with both physical sums localized to
the four-link candidate supports of the actual source rows. -/
def bulkSourceHeatActionScalingFirstOrderSupportCoefficient
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) : Q' :=
  let n := historyCoordinateCount timeBonds
    (combGaugeEdgeCount (bulkSourceWidth side))
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
    timeBonds (bulkSourceWidth side)
  let entryCoefficient :=
    ldlFactorResidualCoefficient n data.lower data.diagonal
  let leftRow := bulkSourcePhysicalColorCurlRow
    side leftTime leftRowIndex
  let rightRow := bulkSourcePhysicalColorCurlRow
    side rightTime rightRowIndex
  listQSum
    (fun left => listQSum
      (fun right =>
        Q'.abs (leftRow left * rightRow right) *
          entryCoefficient left right)
      (bulkSourcePhysicalColorCurlSupportedCoordinates
        timeBonds side rightTime rightRowIndex))
    (bulkSourcePhysicalColorCurlSupportedCoordinates
      timeBonds side leftTime leftRowIndex)

/-- The actual source-specialized first-order coefficient is exactly its
four-support localization. -/
theorem bulkSourceHeatActionScalingFirstOrderCoefficient_eq_support
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat)
    (hleftRowIndex :
      leftRowIndex < 3 * (bulkSourceFaces side).length)
    (hrightRowIndex :
      rightRowIndex < 3 * (bulkSourceFaces side).length) :
    bulkSourceHeatActionScalingFirstOrderCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex ≈
      bulkSourceHeatActionScalingFirstOrderSupportCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex := by
  unfold bulkSourceHeatActionScalingFirstOrderCoefficient
    combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
    physicalCovarianceBilinearResidualEnvelope
    bulkSourceHeatActionScalingFirstOrderSupportCoefficient
    bulkSourcePhysicalColorCurlSupportedCoordinates
  simp only [qListSum_map_eq_listQSum_local]
  let n := historyCoordinateCount timeBonds
    (combGaugeEdgeCount (bulkSourceWidth side))
  let entryCoefficient := ldlFactorResidualCoefficient n
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds (bulkSourceWidth side)).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds (bulkSourceWidth side)).diagonal
  let leftRow := bulkSourcePhysicalColorCurlRow
    side leftTime leftRowIndex
  let rightRow := bulkSourcePhysicalColorCurlRow
    side rightTime rightRowIndex
  let leftTest := fun coordinate => decide (coordinate ∈
    bulkSourcePhysicalColorCurlCandidateCoordinates
      side leftTime leftRowIndex)
  let rightTest := fun coordinate => decide (coordinate ∈
    bulkSourcePhysicalColorCurlCandidateCoordinates
      side rightTime rightRowIndex)
  let term := fun left right =>
    Q'.abs (leftRow left * rightRow right) *
      entryCoefficient left right
  have hleftFilter :
      listQSum
          (fun left => listQSum (term left) (List.range n))
          (List.range n) ≈
        listQSum
          (fun left => listQSum (term left) (List.range n))
          ((List.range n).filter leftTest) := by
    apply listQSum_eq_filter_of_zero_local
    intro left hleft hleftTest
    have hleftCoordinate : left < n := List.mem_range.mp hleft
    have hleftNot : left ∉
        bulkSourcePhysicalColorCurlCandidateCoordinates
          side leftTime leftRowIndex := by
      exact of_decide_eq_false hleftTest
    have hleftZero : leftRow left = 0 := by
      exact bulkSourcePhysicalColorCurlRow_eq_zero_of_not_mem_candidates
        timeBonds side leftTime leftRowIndex left
        hleftRowIndex hleftCoordinate hleftNot
    apply listQSum_eqv_zero_of_pointwise_local
    intro right _hright
    exact envelopeTerm_eqv_zero_of_left_zero
      (leftRow left) (rightRow right) (entryCoefficient left right)
      hleftZero
  refine Q'.eqv_trans _ _ _ hleftFilter ?_
  apply listQSum_congr
  intro left
  apply listQSum_eq_filter_of_zero_local
  intro right hright hrightTest
  have hrightCoordinate : right < n := List.mem_range.mp hright
  have hrightNot : right ∉
      bulkSourcePhysicalColorCurlCandidateCoordinates
        side rightTime rightRowIndex := by
    exact of_decide_eq_false hrightTest
  have hrightZero : rightRow right = 0 := by
    exact bulkSourcePhysicalColorCurlRow_eq_zero_of_not_mem_candidates
      timeBonds side rightTime rightRowIndex right
      hrightRowIndex hrightCoordinate hrightNot
  exact envelopeTerm_eqv_zero_of_right_zero
    (leftRow left) (rightRow right) (entryCoefficient left right)
    hrightZero

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderSupport

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderSupport.bulkSourceHeatActionScalingFirstOrderCoefficient_eq_support
