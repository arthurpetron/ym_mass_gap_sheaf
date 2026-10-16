/-
# Heron pullback of the literal heat action rows

Finite pullback through the rational heat Heron transform and the disjoint
three-color embedding are rational linear maps.  This leaf proves their
additive and sign laws directly, then identifies the literal heat plaquette
total row and kinetic difference row with the three-color pullbacks of the
physical action rows from the preceding module.

This is a row-representation theorem.  It does not yet sum the complete
weighted action list, identify the full scaling kernel with the covariance
residual matrix, prove a uniform bound, compare the ORIGINAL law, control
higher remainders, or establish a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
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

private theorem qListSum_add_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    qListSum (items.map fun item => left item + right item) ≈
      qListSum (items.map left) + qListSum (items.map right)
  | [] => Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | item :: items =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (qListSum_add_local left right items))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1))
            (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2))
            (.add (.var 1) (.var 3)))
          (by decide) (fun
            | 0 => left item
            | 1 => right item
            | 2 => qListSum (items.map left)
            | _ => qListSum (items.map right)))

private theorem qListSum_neg_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map fun item => -(value item)) ≈
      -(qListSum (items.map value))
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | item :: items =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (qListSum_neg_local value items))
        (Q'.eqv_symm
          (Q'.neg_add_eqv (value item) (qListSum (items.map value))))

private theorem pulledRow_add
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (left right : Nat → Q') (noiseIndex : Nat) :
    pulledRow physicalSize transform (fun index => left index + right index)
        noiseIndex ≈
      pulledRow physicalSize transform left noiseIndex +
        pulledRow physicalSize transform right noiseIndex := by
  unfold pulledRow
  refine Q'.eqv_trans _
    (qListSum ((List.range physicalSize).map fun physicalIndex =>
      left physicalIndex * transform physicalIndex noiseIndex +
        right physicalIndex * transform physicalIndex noiseIndex)) _ ?_ ?_
  · apply qListSum_congr_local
    intro physicalIndex _membership
    exact poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (by decide) (fun
        | 0 => left physicalIndex
        | 1 => right physicalIndex
        | _ => transform physicalIndex noiseIndex)
  · exact qListSum_add_local
      (fun physicalIndex =>
        left physicalIndex * transform physicalIndex noiseIndex)
      (fun physicalIndex =>
        right physicalIndex * transform physicalIndex noiseIndex)
      (List.range physicalSize)

private theorem pulledRow_neg
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (row : Nat → Q') (noiseIndex : Nat) :
    pulledRow physicalSize transform (fun index => -(row index)) noiseIndex ≈
      -(pulledRow physicalSize transform row noiseIndex) := by
  unfold pulledRow
  refine Q'.eqv_trans _
    (qListSum ((List.range physicalSize).map fun physicalIndex =>
      -(row physicalIndex * transform physicalIndex noiseIndex))) _ ?_ ?_
  · apply qListSum_congr_local
    intro physicalIndex _membership
    exact Q'.neg_mul_eqv
      (row physicalIndex) (transform physicalIndex noiseIndex)
  · exact qListSum_neg_local
      (fun physicalIndex =>
        row physicalIndex * transform physicalIndex noiseIndex)
      (List.range physicalSize)

private theorem threeColorRows_congr
    (size component coordinate : Nat) (left right : Nat → Q')
    (rowsEqv : ∀ index, left index ≈ right index) :
    threeColorRows size left component coordinate ≈
      threeColorRows size right component coordinate := by
  rcases component with _ | component
  · simp only [threeColorRows]
    unfold appendRow
    by_cases h0 : coordinate < size
    · rw [if_pos h0, if_pos h0]
      exact rowsEqv coordinate
    · rw [if_neg h0, if_neg h0]
      exact Q'.eqv_refl _
  · rcases component with _ | component
    · simp only [threeColorRows]
      unfold appendRow
      by_cases h0 : coordinate < size
      · rw [if_pos h0, if_pos h0]
        exact Q'.eqv_refl _
      · rw [if_neg h0, if_neg h0]
        by_cases h1 : coordinate - size < size
        · rw [if_pos h1, if_pos h1]
          exact rowsEqv (coordinate - size)
        · rw [if_neg h1, if_neg h1]
          exact Q'.eqv_refl _
    · rcases component with _ | component
      · simp only [threeColorRows]
        unfold appendRow
        by_cases h0 : coordinate < size
        · rw [if_pos h0, if_pos h0]
          exact Q'.eqv_refl _
        · rw [if_neg h0, if_neg h0]
          by_cases h1 : coordinate - size < size
          · rw [if_pos h1, if_pos h1]
            exact Q'.eqv_refl _
          · rw [if_neg h1, if_neg h1]
            exact rowsEqv (coordinate - size - size)
      · simp only [threeColorRows]
        exact Q'.eqv_refl _

private theorem threeColorRows_add
    (size component coordinate : Nat) (left right : Nat → Q') :
    threeColorRows size left component coordinate +
        threeColorRows size right component coordinate ≈
      threeColorRows size (fun index => left index + right index)
        component coordinate := by
  rcases component with _ | component
  · simp only [threeColorRows]
    unfold appendRow
    by_cases h0 : coordinate < size
    · rw [if_pos h0, if_pos h0, if_pos h0]
      exact Q'.eqv_refl _
    · rw [if_neg h0, if_neg h0, if_neg h0]
      by_cases h1 : coordinate - size < size
      · simp only [if_pos h1]
        change (0 : Q') + 0 ≈ 0
        decide
      · simp only [if_neg h1]
        change (0 : Q') + 0 ≈ 0
        decide
  · rcases component with _ | component
    · simp only [threeColorRows]
      unfold appendRow
      by_cases h0 : coordinate < size
      · rw [if_pos h0, if_pos h0, if_pos h0]
        change (0 : Q') + 0 ≈ 0
        decide
      · rw [if_neg h0, if_neg h0, if_neg h0]
        by_cases h1 : coordinate - size < size
        · rw [if_pos h1, if_pos h1, if_pos h1]
          exact Q'.eqv_refl _
        · rw [if_neg h1, if_neg h1, if_neg h1]
          change (0 : Q') + 0 ≈ 0
          decide
    · rcases component with _ | component
      · simp only [threeColorRows]
        unfold appendRow
        by_cases h0 : coordinate < size
        · rw [if_pos h0, if_pos h0, if_pos h0]
          change (0 : Q') + 0 ≈ 0
          decide
        · rw [if_neg h0, if_neg h0, if_neg h0]
          by_cases h1 : coordinate - size < size
          · rw [if_pos h1, if_pos h1, if_pos h1]
            change (0 : Q') + 0 ≈ 0
            decide
          · rw [if_neg h1, if_neg h1, if_neg h1]
            exact Q'.eqv_refl _
      · simp only [threeColorRows]
        change (0 : Q') + 0 ≈ 0
        decide

private theorem threeColorRows_neg
    (size component coordinate : Nat) (row : Nat → Q') :
    -(threeColorRows size row component coordinate) ≈
      threeColorRows size (fun index => -(row index)) component coordinate := by
  rcases component with _ | component
  · simp only [threeColorRows]
    unfold appendRow
    by_cases h0 : coordinate < size
    · rw [if_pos h0, if_pos h0]
      exact Q'.eqv_refl _
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : coordinate - size < size
      · simp only [if_pos h1]
        change -(0 : Q') ≈ 0
        decide
      · simp only [if_neg h1]
        change -(0 : Q') ≈ 0
        decide
  · rcases component with _ | component
    · simp only [threeColorRows]
      unfold appendRow
      by_cases h0 : coordinate < size
      · rw [if_pos h0, if_pos h0]
        change -(0 : Q') ≈ 0
        decide
      · rw [if_neg h0, if_neg h0]
        by_cases h1 : coordinate - size < size
        · rw [if_pos h1, if_pos h1]
          exact Q'.eqv_refl _
        · rw [if_neg h1, if_neg h1]
          change -(0 : Q') ≈ 0
          decide
    · rcases component with _ | component
      · simp only [threeColorRows]
        unfold appendRow
        by_cases h0 : coordinate < size
        · rw [if_pos h0, if_pos h0]
          change -(0 : Q') ≈ 0
          decide
        · rw [if_neg h0, if_neg h0]
          by_cases h1 : coordinate - size < size
          · rw [if_pos h1, if_pos h1]
            change -(0 : Q') ≈ 0
            decide
          · rw [if_neg h1, if_neg h1]
            exact Q'.eqv_refl _
      · simp only [threeColorRows]
        change -(0 : Q') ≈ 0
        decide

/-- One physical row pulled through the finite rational heat transform and
embedded in one of the three disjoint color blocks. -/
def heatColorPulledRow
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (physicalRow : Nat → Q') (component coordinate : Nat) : Q' :=
  threeColorRows physicalSize
    (pulledRow physicalSize transform physicalRow) component coordinate

/-- Grams of heat-color pullbacks are color diagonal, with the matching-color
entry equal to the physical covariance bilinear induced by the transform. -/
theorem finiteRowGram_heatColorPulledRow
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (leftRow rightRow : Nat → Q') (leftComponent rightComponent : Nat)
    (hleftComponent : leftComponent < 3)
    (hrightComponent : rightComponent < 3) :
    finiteRowGram (physicalSize + (physicalSize + physicalSize))
        (heatColorPulledRow physicalSize transform leftRow leftComponent)
        (heatColorPulledRow physicalSize transform rightRow rightComponent) ≈
      if leftComponent = rightComponent then
        physicalCovarianceBilinear physicalSize physicalSize
          transform leftRow rightRow
      else 0 := by
  unfold heatColorPulledRow
  refine Q'.eqv_trans _ _ _
    (finiteRowGram_threeColorRows physicalSize
      leftComponent rightComponent
      (pulledRow physicalSize transform leftRow)
      (pulledRow physicalSize transform rightRow)
      hleftComponent hrightComponent) ?_
  by_cases hcomponent : leftComponent = rightComponent
  · rw [if_pos hcomponent, if_pos hcomponent]
    exact finiteRowGram_pulledRow physicalSize physicalSize
      transform leftRow rightRow
  · rw [if_neg hcomponent, if_neg hcomponent]
    exact Q'.eqv_refl _

private theorem heatColorPulledRow_add
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (left right : Nat → Q') (component coordinate : Nat) :
    heatColorPulledRow physicalSize transform left component coordinate +
        heatColorPulledRow physicalSize transform right component coordinate ≈
      heatColorPulledRow physicalSize transform
        (fun index => left index + right index) component coordinate := by
  unfold heatColorPulledRow
  exact Q'.eqv_trans _ _ _
    (threeColorRows_add physicalSize component coordinate
      (pulledRow physicalSize transform left)
      (pulledRow physicalSize transform right))
    (threeColorRows_congr physicalSize component coordinate _ _
      (fun noiseIndex => Q'.eqv_symm
        (pulledRow_add physicalSize transform left right noiseIndex)))

private theorem heatColorPulledRow_neg
    (physicalSize : Nat) (transform : Nat → Nat → Q')
    (row : Nat → Q') (component coordinate : Nat) :
    -(heatColorPulledRow physicalSize transform row component coordinate) ≈
      heatColorPulledRow physicalSize transform
        (fun index => -(row index)) component coordinate := by
  unfold heatColorPulledRow
  exact Q'.eqv_trans _ _ _
    (threeColorRows_neg physicalSize component coordinate
      (pulledRow physicalSize transform row))
    (threeColorRows_congr physicalSize component coordinate _ _
      (fun noiseIndex => Q'.eqv_symm
        (pulledRow_neg physicalSize transform row noiseIndex)))

/-- Each literal heat plaquette total row is the three-color Heron pullback of
the corresponding directed physical plaquette row. -/
theorem openCubeHeatPlaquetteTotalRow_eq_physicalPullback
    (timeBonds width stage time : Nat) (face : Z4Plaq)
    (component coordinate : Nat) :
    let physicalSize :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    gaussianCayleyTotalRows
        (gaussianCayleySlot
          ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
            timeBonds width stage time face) 0)
          ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
            timeBonds width stage time face) 1)
          ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
            timeBonds width stage time face) 2)
          ((combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
            timeBonds width stage time face) 3))
        component coordinate ≈
      heatColorPulledRow physicalSize
        (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
        (combGaugeFreeHistoryPlaquettePhysicalActionRow width time face)
        component coordinate := by
  let physicalSize :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform := combGaugeHeatFreeHistoryHeronTransform
    timeBonds width stage
  let rowA := combGaugeFreeHistoryLinkRow width time (faceLinkA face)
  let rowB := combGaugeFreeHistoryLinkRow width time (faceLinkB face)
  let rowC := combGaugeFreeHistoryLinkRow width time (faceLinkC face)
  let rowD := combGaugeFreeHistoryLinkRow width time (faceLinkD face)
  let pulledA := heatColorPulledRow physicalSize transform rowA component coordinate
  let pulledB := heatColorPulledRow physicalSize transform rowB component coordinate
  let pulledC := heatColorPulledRow physicalSize transform rowC component coordinate
  let pulledD := heatColorPulledRow physicalSize transform rowD component coordinate
  change ((1 * pulledA + 1 * pulledB) + (-1) * pulledC) + (-1) * pulledD ≈
    heatColorPulledRow physicalSize transform
      (combGaugeFreeHistoryPlaquettePhysicalActionRow width time face)
      component coordinate
  have hnormalize :
      ((1 * pulledA + 1 * pulledB) + (-1) * pulledC) + (-1) * pulledD ≈
        pulledA + (pulledB + (-pulledC + -pulledD)) := by
    exact poly_identity_of_normal_eq
      (.add
        (.add
          (.add (.mul (.const 1) (.var 0))
            (.mul (.const 1) (.var 1)))
          (.mul (.neg (.const 1)) (.var 2)))
        (.mul (.neg (.const 1)) (.var 3)))
      (.add (.var 0)
        (.add (.var 1) (.add (.neg (.var 2)) (.neg (.var 3)))))
      (by decide) (fun
        | 0 => pulledA
        | 1 => pulledB
        | 2 => pulledC
        | _ => pulledD)
  have hCD : -pulledC + -pulledD ≈
      heatColorPulledRow physicalSize transform
        (fun index => -(rowC index) + -(rowD index))
        component coordinate := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (heatColorPulledRow_neg physicalSize transform rowC component coordinate)
        (heatColorPulledRow_neg physicalSize transform rowD component coordinate))
      (heatColorPulledRow_add physicalSize transform
        (fun index => -(rowC index)) (fun index => -(rowD index))
        component coordinate)
  have hBCD : pulledB + (-pulledC + -pulledD) ≈
      heatColorPulledRow physicalSize transform
        (fun index => rowB index + (-(rowC index) + -(rowD index)))
        component coordinate := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hCD)
      (heatColorPulledRow_add physicalSize transform rowB
        (fun index => -(rowC index) + -(rowD index))
        component coordinate)
  have hABCD : pulledA + (pulledB + (-pulledC + -pulledD)) ≈
      heatColorPulledRow physicalSize transform
        (fun index => rowA index +
          (rowB index + (-(rowC index) + -(rowD index))))
        component coordinate := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hBCD)
      (heatColorPulledRow_add physicalSize transform rowA
        (fun index => rowB index + (-(rowC index) + -(rowD index)))
        component coordinate)
  exact Q'.eqv_trans _ _ _ hnormalize (Q'.eqv_trans _ _ _ hABCD (by
    unfold rowA rowB rowC rowD
      combGaugeFreeHistoryPlaquettePhysicalActionRow
    exact Q'.eqv_refl _))

/-- Each literal heat kinetic difference row is the three-color Heron pullback
of the corresponding physical link difference. -/
theorem openCubeHeatKineticDifferenceRow_eq_physicalPullback
    (timeBonds width stage bond : Nat) (link : Z4Link)
    (component coordinate : Nat) :
    let physicalSize :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    combGaugeHeatFreeHistoryHeronKineticDifferenceRows
        timeBonds width stage bond link component coordinate ≈
      heatColorPulledRow physicalSize
        (combGaugeHeatFreeHistoryHeronTransform timeBonds width stage)
        (combGaugeFreeHistoryKineticPhysicalActionRow width bond link)
        component coordinate := by
  let physicalSize :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform := combGaugeHeatFreeHistoryHeronTransform
    timeBonds width stage
  let leftRow := combGaugeFreeHistoryLinkRow width bond link
  let rightRow := combGaugeFreeHistoryLinkRow width (bond + 1) link
  let pulledLeft :=
    heatColorPulledRow physicalSize transform leftRow component coordinate
  let pulledRight :=
    heatColorPulledRow physicalSize transform rightRow component coordinate
  change (1 * pulledLeft) + -(1 * pulledRight) ≈
    heatColorPulledRow physicalSize transform
      (combGaugeFreeHistoryKineticPhysicalActionRow width bond link)
      component coordinate
  have hnormalize : (1 * pulledLeft) + -(1 * pulledRight) ≈
      pulledLeft + -pulledRight := by
    exact poly_identity_of_normal_eq
      (.add (.mul (.const 1) (.var 0))
        (.neg (.mul (.const 1) (.var 1))))
      (.add (.var 0) (.neg (.var 1)))
      (by decide) (fun
        | 0 => pulledLeft
        | _ => pulledRight)
  exact Q'.eqv_trans _ _ _ hnormalize (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (heatColorPulledRow_neg physicalSize transform rightRow
        component coordinate))
    (Q'.eqv_trans _ _ _
      (heatColorPulledRow_add physicalSize transform leftRow
        (fun index => -(rightRow index)) component coordinate)
      (by
        unfold leftRow rightRow
          combGaugeFreeHistoryKineticPhysicalActionRow
        exact Q'.eqv_refl _)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback.openCubeHeatPlaquetteTotalRow_eq_physicalPullback
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback.openCubeHeatKineticDifferenceRow_eq_physicalPullback
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback.finiteRowGram_heatColorPulledRow
