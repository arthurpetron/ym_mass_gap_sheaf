/-
# Complete heat action list after Heron pullback

Every corrected heat action insertion contributes three disjoint color-row
squares.  The preceding row theorem identifies each literal plaquette or
kinetic row with the three-color pullback of its physical row.  This leaf sums
the complete weighted action list and proves that its row-Gram sandwich is
color diagonal.  On the matching color it is exactly the finite physical
staged-covariance sandwich over the actual face and link carriers.

This is an exact finite representation theorem.  It does not yet rewrite the
physical sandwich as a matrix product with the checked precision, identify the
full scaling kernel with the covariance-residual contraction, prove a uniform
bound, compare the ORIGINAL law, control higher remainders, or establish a
continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompletePhysicalActionGram
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteActionPullbackGram

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_congr_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    qListSum (items.map left) ≈ qListSum (items.map right)
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (qListSum_congr_local left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

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

private theorem listQSum_mul_left_local {Index : Type}
    (scale : Q') (value : Index → Q') : ∀ items : List Index,
    scale * listQSum value items ≈
      listQSum (fun item => scale * value item) items
  | [] => Q'.mul_zero_eqv _
  | item :: items =>
      Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv scale (value item) (listQSum value items))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_mul_left_local scale value items))

private theorem listQSum_if_eq_local {Index : Type}
    (leftComponent rightComponent : Nat) (value : Index → Q')
    (items : List Index) :
    listQSum
        (fun item => if leftComponent = rightComponent then value item else 0)
        items ≈
      if leftComponent = rightComponent then listQSum value items else 0 := by
  by_cases hcomponent : leftComponent = rightComponent
  · simp only [if_pos hcomponent]
    exact Q'.eqv_refl _
  · simp only [if_neg hcomponent]
    exact listQSum_zero_local items

private theorem mul_congr_local {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem finiteRowGram_congr_right_local
    (count : Nat) (left right right' : Nat → Q')
    (hrow : ∀ coordinate, right coordinate ≈ right' coordinate) :
    finiteRowGram count left right ≈ finiteRowGram count left right' := by
  unfold finiteRowGram
  apply qListSum_congr_local
  intro coordinate _membership
  exact Q'.mul_eqv_congr_left _ _ _ (hrow coordinate)

private theorem sum_three_at_local
    (component : Nat) (hcomponent : component < 3) (value : Q') :
    listQSum (fun other => if component = other then value else 0)
      (List.range 3) ≈ value := by
  have componentCases :
      component = 0 ∨ component = 1 ∨ component = 2 := by omega
  rcases componentCases with rfl | rfl | rfl
  · change value + (0 + (0 + 0)) ≈ value
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.add (.const 0) (.add (.const 0) (.const 0))))
      (.var 0) (by decide) (fun _ => value)
  · change 0 + (value + (0 + 0)) ≈ value
    exact poly_identity_of_normal_eq
      (.add (.const 0) (.add (.var 0) (.add (.const 0) (.const 0))))
      (.var 0) (by decide) (fun _ => value)
  · change 0 + (0 + (value + 0)) ≈ value
    exact poly_identity_of_normal_eq
      (.add (.const 0) (.add (.const 0) (.add (.var 0) (.const 0))))
      (.var 0) (by decide) (fun _ => value)

private theorem delta_pair_local
    (leftComponent rightComponent actionComponent : Nat)
    (leftValue rightValue : Q') :
    (if leftComponent = actionComponent then leftValue else 0) *
        (if rightComponent = actionComponent then rightValue else 0) ≈
      if leftComponent = rightComponent then
        if leftComponent = actionComponent then leftValue * rightValue else 0
      else 0 := by
  by_cases hcomponents : leftComponent = rightComponent
  · subst rightComponent
    by_cases haction : leftComponent = actionComponent
    · simp only [if_pos haction]
      exact Q'.eqv_refl _
    · simp only [if_neg haction]
      exact Q'.zero_mul_eqv 0
  · simp only [if_neg hcomponents]
    by_cases hleft : leftComponent = actionComponent
    · have hright : rightComponent ≠ actionComponent := by
        intro hright
        exact hcomponents (hleft.trans hright.symm)
      simp only [if_pos hleft, if_neg hright]
      exact Q'.mul_zero_eqv _
    · simp only [if_neg hleft]
      exact Q'.zero_mul_eqv _

private theorem sum_three_pair_local
    (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (leftValue rightValue : Q') :
    listQSum (fun actionComponent =>
      (if leftComponent = actionComponent then leftValue else 0) *
        (if rightComponent = actionComponent then rightValue else 0))
      (List.range 3) ≈
      if leftComponent = rightComponent then leftValue * rightValue else 0 := by
  refine Q'.eqv_trans _ _ _
    (listQSum_congr_local _ _ (List.range 3)
      (fun actionComponent _membership =>
        delta_pair_local leftComponent rightComponent actionComponent
          leftValue rightValue)) ?_
  by_cases hcomponents : leftComponent = rightComponent
  · simp only [if_pos hcomponents]
    exact sum_three_at_local leftComponent hleftComponent
      (leftValue * rightValue)
  · simp only [if_neg hcomponents]
    change (0 : Q') + (0 + (0 + 0)) ≈ 0
    exact poly_identity_of_normal_eq
      (.add (.const 0) (.add (.const 0) (.add (.const 0) (.const 0))))
      (.const 0) (by decide) (fun _ => leftValue)

/-- Weighted row-Gram sandwich of a finite action-square list. -/
def finiteGaussianWeightedActionGramSum
    (noiseCount : Nat) (action : List WeightedRowSquare)
    (left right : Nat → Q') : Q' :=
  listQSum
    (fun actionTerm => actionTerm.weight *
      (finiteRowGram noiseCount left actionTerm.row *
        finiteRowGram noiseCount right actionTerm.row))
    action

/-- Physical staged-covariance sandwich over the actual complete plaquette
and kinetic insertion carriers. -/
def combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  let physicalSize :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let covariance := fun source action =>
    physicalCovarianceBilinear physicalSize physicalSize
      transform source action
  listQSum
      (fun time => listQSum
        (fun face =>
          covariance leftRow
              (combGaugeFreeHistoryPlaquettePhysicalActionRow
                width time face) *
            covariance rightRow
              (combGaugeFreeHistoryPlaquettePhysicalActionRow
                width time face))
        (internalOpenCubeFaces width))
      (List.range (timeBonds + 1)) +
    listQSum
      (fun bond => listQSum
        (fun link =>
          covariance leftRow
              (combGaugeFreeHistoryKineticPhysicalActionRow
                width bond link) *
            covariance rightRow
              (combGaugeFreeHistoryKineticPhysicalActionRow
                width bond link))
        (combGaugeLinks width))
      (List.range timeBonds)

private theorem scaledThreeColorActionSquares_gram_sum
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (leftRow rightRow actionRow : Nat → Q')
    (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3)
    (scale : Q') (literalRows : Nat → Nat → Q')
    (hpullback : ∀ component coordinate,
      literalRows component coordinate ≈
        heatColorPulledRow physicalSize transform actionRow
          component coordinate) :
    finiteGaussianWeightedActionGramSum
        (physicalSize + (physicalSize + physicalSize))
        ((finiteGaussianWeightedRowNormSquares 1 literalRows).map
          (scaleCommonActionWeightedRowSquare scale))
        (heatColorPulledRow physicalSize transform leftRow leftComponent)
        (heatColorPulledRow physicalSize transform rightRow rightComponent) ≈
      if leftComponent = rightComponent then
        scale *
          (physicalCovarianceBilinear physicalSize physicalSize
              transform leftRow actionRow *
            physicalCovarianceBilinear physicalSize physicalSize
              transform rightRow actionRow)
      else 0 := by
  unfold finiteGaussianWeightedActionGramSum
    finiteGaussianWeightedRowNormSquares
  rw [listQSum_map, listQSum_map]
  simp only [scaleCommonActionWeightedRowSquare]
  let diagonalValue := fun actionComponent =>
    scale *
      ((if leftComponent = actionComponent then
          physicalCovarianceBilinear physicalSize physicalSize
            transform leftRow actionRow
        else 0) *
      (if rightComponent = actionComponent then
          physicalCovarianceBilinear physicalSize physicalSize
            transform rightRow actionRow
        else 0))
  refine Q'.eqv_trans _
    (listQSum diagonalValue (List.range 3)) _ ?_ ?_
  · apply listQSum_congr_local
    intro actionComponent hactionComponent
    have haction : actionComponent < 3 :=
      List.mem_range.mp hactionComponent
    have hleftGram :
        finiteRowGram (physicalSize + (physicalSize + physicalSize))
            (heatColorPulledRow physicalSize transform leftRow leftComponent)
            (literalRows actionComponent) ≈
          if leftComponent = actionComponent then
            physicalCovarianceBilinear physicalSize physicalSize
              transform leftRow actionRow
          else 0 := by
      exact Q'.eqv_trans _ _ _
        (finiteRowGram_congr_right_local
          (physicalSize + (physicalSize + physicalSize))
          (heatColorPulledRow physicalSize transform leftRow leftComponent)
          (literalRows actionComponent)
          (heatColorPulledRow physicalSize transform actionRow actionComponent)
          (hpullback actionComponent))
        (finiteRowGram_heatColorPulledRow physicalSize transform
          leftRow actionRow leftComponent actionComponent
          hleftComponent haction)
    have hrightGram :
        finiteRowGram (physicalSize + (physicalSize + physicalSize))
            (heatColorPulledRow physicalSize transform rightRow rightComponent)
            (literalRows actionComponent) ≈
          if rightComponent = actionComponent then
            physicalCovarianceBilinear physicalSize physicalSize
              transform rightRow actionRow
          else 0 := by
      exact Q'.eqv_trans _ _ _
        (finiteRowGram_congr_right_local
          (physicalSize + (physicalSize + physicalSize))
          (heatColorPulledRow physicalSize transform rightRow rightComponent)
          (literalRows actionComponent)
          (heatColorPulledRow physicalSize transform actionRow actionComponent)
          (hpullback actionComponent))
        (finiteRowGram_heatColorPulledRow physicalSize transform
          rightRow actionRow rightComponent actionComponent
          hrightComponent haction)
    unfold diagonalValue
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (scale * 1) _ _
        (mul_congr_local hleftGram hrightGram))
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.const 1))
          (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => scale
          | 1 => if leftComponent = actionComponent then
              physicalCovarianceBilinear physicalSize physicalSize
                transform leftRow actionRow
            else 0
          | _ => if rightComponent = actionComponent then
              physicalCovarianceBilinear physicalSize physicalSize
                transform rightRow actionRow
            else 0))
  · unfold diagonalValue
    let base := fun actionComponent =>
      (if leftComponent = actionComponent then
          physicalCovarianceBilinear physicalSize physicalSize
            transform leftRow actionRow
        else 0) *
      (if rightComponent = actionComponent then
          physicalCovarianceBilinear physicalSize physicalSize
            transform rightRow actionRow
        else 0)
    have hsum := sum_three_pair_local leftComponent rightComponent
      hleftComponent
      (physicalCovarianceBilinear physicalSize physicalSize
        transform leftRow actionRow)
      (physicalCovarianceBilinear physicalSize physicalSize
        transform rightRow actionRow)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (listQSum_mul_left_local scale base (List.range 3)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left scale _ _ hsum) ?_)
    by_cases hcomponents : leftComponent = rightComponent
    · simp only [if_pos hcomponents]
      exact Q'.eqv_refl _
    · simp only [if_neg hcomponents]
      exact Q'.mul_zero_eqv scale

private theorem plaquetteActionSquares_gram_sum
    (timeBonds width stage time : Nat) (face : Z4Plaq)
    (leftRow rightRow : Nat → Q') (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) (scale : Q') :
    let physicalSize :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    finiteGaussianWeightedActionGramSum
        (combGaugePlaquetteNoiseCount timeBonds width)
        ((openCubeHeatPlaquetteGaussianActionRowSquares
          timeBonds width stage time face).map
            (scaleCommonActionWeightedRowSquare scale))
        (heatColorPulledRow physicalSize
          (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
          leftRow leftComponent)
        (heatColorPulledRow physicalSize
          (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
          rightRow rightComponent) ≈
      if leftComponent = rightComponent then
        scale *
          (physicalCovarianceBilinear physicalSize physicalSize
              (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
              leftRow
              (combGaugeFreeHistoryPlaquettePhysicalActionRow
                width time face) *
            physicalCovarianceBilinear physicalSize physicalSize
              (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
              rightRow
              (combGaugeFreeHistoryPlaquettePhysicalActionRow
                width time face))
      else 0 := by
  unfold openCubeHeatPlaquetteGaussianActionRowSquares
  exact scaledThreeColorActionSquares_gram_sum
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
    leftRow rightRow
    (combGaugeFreeHistoryPlaquettePhysicalActionRow width time face)
    leftComponent rightComponent hleftComponent hrightComponent
    scale _
    (fun component coordinate =>
      openCubeHeatPlaquetteTotalRow_eq_physicalPullback
        timeBonds width stage time face component coordinate)

private theorem kineticActionSquares_gram_sum
    (timeBonds width stage bond : Nat) (link : Z4Link)
    (leftRow rightRow : Nat → Q') (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) (scale : Q') :
    let physicalSize :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    finiteGaussianWeightedActionGramSum
        (combGaugePlaquetteNoiseCount timeBonds width)
        ((openCubeHeatKineticGaussianActionRowSquares
          timeBonds width stage bond link).map
            (scaleCommonActionWeightedRowSquare scale))
        (heatColorPulledRow physicalSize
          (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
          leftRow leftComponent)
        (heatColorPulledRow physicalSize
          (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
          rightRow rightComponent) ≈
      if leftComponent = rightComponent then
        scale *
          (physicalCovarianceBilinear physicalSize physicalSize
              (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
              leftRow
              (combGaugeFreeHistoryKineticPhysicalActionRow
                width bond link) *
            physicalCovarianceBilinear physicalSize physicalSize
              (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
              rightRow
              (combGaugeFreeHistoryKineticPhysicalActionRow
                width bond link))
      else 0 := by
  unfold openCubeHeatKineticGaussianActionRowSquares
  exact scaledThreeColorActionSquares_gram_sum
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
    leftRow rightRow
    (combGaugeFreeHistoryKineticPhysicalActionRow width bond link)
    leftComponent rightComponent hleftComponent hrightComponent
    scale _
    (fun component coordinate =>
      openCubeHeatKineticDifferenceRow_eq_physicalPullback
        timeBonds width stage bond link component coordinate)

/-- The complete literal heat action-square list has a color-diagonal Gram
sandwich.  Its matching-color entry is the staged physical covariance
sandwich over the actual complete plaquette and kinetic carriers. -/
theorem completeOpenCubeHeatGaussianActionGramSum_eq_literalSandwich
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q')
    (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) :
    let physicalSize :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    finiteGaussianWeightedActionGramSum
        (combGaugePlaquetteNoiseCount timeBonds width)
        (completeOpenCubeHeatGaussianActionRowSquares
          timeBonds width stage)
        (heatColorPulledRow physicalSize
          (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
          leftRow leftComponent)
        (heatColorPulledRow physicalSize
          (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
          rightRow rightComponent) ≈
      if leftComponent = rightComponent then
        combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
          timeBonds width stage leftRow rightRow
      else 0 := by
  let physicalSize :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let leftNoise := heatColorPulledRow physicalSize transform
    leftRow leftComponent
  let rightNoise := heatColorPulledRow physicalSize transform
    rightRow rightComponent
  let termValue := fun actionTerm : WeightedRowSquare =>
    actionTerm.weight *
      (finiteRowGram (combGaugePlaquetteNoiseCount timeBonds width)
          leftNoise actionTerm.row *
        finiteRowGram (combGaugePlaquetteNoiseCount timeBonds width)
          rightNoise actionTerm.row)
  let spatialValue := fun insertion : OpenCubeSpatialHeatActionFourthInsertion =>
    insertion.weight *
      (physicalCovarianceBilinear physicalSize physicalSize transform
          leftRow
          (combGaugeFreeHistoryPlaquettePhysicalActionRow
            width insertion.time insertion.face) *
        physicalCovarianceBilinear physicalSize physicalSize transform
          rightRow
          (combGaugeFreeHistoryPlaquettePhysicalActionRow
            width insertion.time insertion.face))
  let kineticValue := fun insertion : OpenCubeKineticFourthActionInsertion =>
    insertion.weight *
      (physicalCovarianceBilinear physicalSize physicalSize transform
          leftRow
          (combGaugeFreeHistoryKineticPhysicalActionRow
            width insertion.bond insertion.link) *
        physicalCovarianceBilinear physicalSize physicalSize transform
          rightRow
          (combGaugeFreeHistoryKineticPhysicalActionRow
            width insertion.bond insertion.link))
  unfold finiteGaussianWeightedActionGramSum
    completeOpenCubeHeatGaussianActionRowSquares
  change listQSum termValue (_ ++ _) ≈ _
  refine Q'.eqv_trans _ _ _
    (listQSum_append termValue _ _) ?_
  have hspatial :
      listQSum termValue
          ((completeOpenCubeSpatialHeatActionFourthInsertions
              timeBonds width).flatMap fun insertion =>
            (openCubeHeatPlaquetteGaussianActionRowSquares
              timeBonds width stage insertion.time insertion.face).map
                (scaleCommonActionWeightedRowSquare insertion.weight)) ≈
        if leftComponent = rightComponent then
          listQSum spatialValue
            (completeOpenCubeSpatialHeatActionFourthInsertions
              timeBonds width)
        else 0 := by
    refine Q'.eqv_trans _ _ _
      (listQSum_flatMap termValue _
        (completeOpenCubeSpatialHeatActionFourthInsertions
          timeBonds width)) ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_local _ _
        (completeOpenCubeSpatialHeatActionFourthInsertions
          timeBonds width) ?_)
      (listQSum_if_eq_local leftComponent rightComponent spatialValue
        (completeOpenCubeSpatialHeatActionFourthInsertions
          timeBonds width))
    intro insertion _membership
    unfold termValue spatialValue leftNoise rightNoise physicalSize transform
    exact plaquetteActionSquares_gram_sum
      timeBonds width stage insertion.time insertion.face
      leftRow rightRow leftComponent rightComponent
      hleftComponent hrightComponent insertion.weight
  have hkinetic :
      listQSum termValue
          ((completeOpenCubeKineticFourthActionInsertions
              timeBonds width).flatMap fun insertion =>
            (openCubeHeatKineticGaussianActionRowSquares
              timeBonds width stage insertion.bond insertion.link).map
                (scaleCommonActionWeightedRowSquare insertion.weight)) ≈
        if leftComponent = rightComponent then
          listQSum kineticValue
            (completeOpenCubeKineticFourthActionInsertions
              timeBonds width)
        else 0 := by
    refine Q'.eqv_trans _ _ _
      (listQSum_flatMap termValue _
        (completeOpenCubeKineticFourthActionInsertions
          timeBonds width)) ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_local _ _
        (completeOpenCubeKineticFourthActionInsertions
          timeBonds width) ?_)
      (listQSum_if_eq_local leftComponent rightComponent kineticValue
        (completeOpenCubeKineticFourthActionInsertions
          timeBonds width))
    intro insertion _membership
    unfold termValue kineticValue leftNoise rightNoise physicalSize transform
    exact kineticActionSquares_gram_sum
      timeBonds width stage insertion.bond insertion.link
      leftRow rightRow leftComponent rightComponent
      hleftComponent hrightComponent insertion.weight
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hspatial hkinetic) ?_
  have hspatialReindex :
      listQSum spatialValue
          (completeOpenCubeSpatialHeatActionFourthInsertions
            timeBonds width) ≈
        listQSum
          (fun time => listQSum
            (fun face =>
              physicalCovarianceBilinear physicalSize physicalSize transform
                  leftRow
                  (combGaugeFreeHistoryPlaquettePhysicalActionRow
                    width time face) *
                physicalCovarianceBilinear physicalSize physicalSize transform
                  rightRow
                  (combGaugeFreeHistoryPlaquettePhysicalActionRow
                    width time face))
            (internalOpenCubeFaces width))
          (List.range (timeBonds + 1)) := by
    unfold completeOpenCubeSpatialHeatActionFourthInsertions
    refine Q'.eqv_trans _ _ _
      (listQSum_flatMap spatialValue _ (List.range (timeBonds + 1))) ?_
    apply listQSum_congr_local
    intro time _membership
    rw [listQSum_map]
    unfold spatialValue
    apply listQSum_congr_local
    intro face _faceMembership
    simpa only using (Q'.one_mul_eqv
      (physicalCovarianceBilinear physicalSize physicalSize transform
          leftRow
          (combGaugeFreeHistoryPlaquettePhysicalActionRow width time face) *
        physicalCovarianceBilinear physicalSize physicalSize transform
          rightRow
          (combGaugeFreeHistoryPlaquettePhysicalActionRow width time face)))
  have hkineticReindex :
      listQSum kineticValue
          (completeOpenCubeKineticFourthActionInsertions
            timeBonds width) ≈
        listQSum
          (fun bond => listQSum
            (fun link =>
              physicalCovarianceBilinear physicalSize physicalSize transform
                  leftRow
                  (combGaugeFreeHistoryKineticPhysicalActionRow
                    width bond link) *
                physicalCovarianceBilinear physicalSize physicalSize transform
                  rightRow
                  (combGaugeFreeHistoryKineticPhysicalActionRow
                    width bond link))
            (combGaugeLinks width))
          (List.range timeBonds) := by
    unfold completeOpenCubeKineticFourthActionInsertions
    refine Q'.eqv_trans _ _ _
      (listQSum_flatMap kineticValue _ (List.range timeBonds)) ?_
    apply listQSum_congr_local
    intro bond _membership
    rw [listQSum_map]
    unfold kineticValue
    apply listQSum_congr_local
    intro link _linkMembership
    simpa only using (Q'.one_mul_eqv
      (physicalCovarianceBilinear physicalSize physicalSize transform
          leftRow
          (combGaugeFreeHistoryKineticPhysicalActionRow width bond link) *
        physicalCovarianceBilinear physicalSize physicalSize transform
          rightRow
          (combGaugeFreeHistoryKineticPhysicalActionRow width bond link)))
  by_cases hcomponents : leftComponent = rightComponent
  · simp only [if_pos hcomponents]
    unfold combGaugeHeatFreeHistoryLiteralActionCovarianceSandwich
    exact Q'.add_eqv_congr' hspatialReindex hkineticReindex
  · simp only [if_neg hcomponents]
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_refl _))
      (Q'.eqv_of_eq (Q'.zero_add' 0))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteActionPullbackGram

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompleteActionPullbackGram.completeOpenCubeHeatGaussianActionGramSum_eq_literalSandwich
