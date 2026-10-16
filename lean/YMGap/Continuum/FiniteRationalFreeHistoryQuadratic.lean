/-
# Exact quadratic decomposition of finite FREE histories

This module rewrites the flattened finite FREE-history quadratic as the sum of
its spatial-slice quadratics and its independent temporal-path quadratics.  The
mixed-radix reindexing is explicit and finite; no Fourier modes, eigenvectors,
or classical finite-dimensional algebra are used.

The immediate consumer proves strict positivity of the comb-gauge history
precision and then applies the generic constructive inverse/positive-LDL
producer.  This file alone proves no inverse, Gaussian law, continuum limit,
or mass gap.
-/

import YMGap.Continuum.FiniteRationalPositiveDefiniteInverse

namespace YMGap.Continuum.FiniteRationalFreeHistoryQuadratic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

private theorem listQSum_append_local
    {A : Type} (value : A → Q') : ∀ left right : List A,
    listQSum value (left ++ right) ≈
      listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _head :: tail, right => by
      simp only [List.cons_append, listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_append_local value tail right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_flatMap_local
    {A B : Type} (value : B → Q') (map : A → List B) :
    ∀ items : List A,
      listQSum value (items.flatMap map) ≈
        listQSum (fun item => listQSum value (map item)) items
  | [] => Q'.eqv_refl _
  | head :: tail => by
      simp only [List.flatMap_cons, listQSum]
      exact Q'.eqv_trans _ _ _
        (listQSum_append_local value (map head) (tail.flatMap map))
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_flatMap_local value map tail))

private theorem historyIndices_flatMap : ∀ (timeCount spatialSize : Nat),
    (List.range timeCount).flatMap
        (fun time => (List.range spatialSize).map
          (fun spatial => historyIndex spatialSize time spatial)) =
      List.range (timeCount * spatialSize)
  | 0, spatialSize => by simp
  | timeCount + 1, spatialSize => by
      rw [List.range_succ, List.flatMap_append,
        historyIndices_flatMap timeCount spatialSize]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [Nat.succ_mul, List.range_add]
      apply congrArg (List.append (List.range (timeCount * spatialSize)))
      apply List.map_congr_left
      intro spatial _hspatial
      unfold historyIndex
      rw [Nat.mul_comm spatialSize timeCount]

/-- Exact mixed-radix reindexing of a finite rational sum. -/
theorem listQSum_historyIndex
    (timeCount spatialSize : Nat) (value : Nat → Q') :
    listQSum value (List.range (timeCount * spatialSize)) ≈
      listQSum
        (fun time => listQSum
          (fun spatial => value (historyIndex spatialSize time spatial))
          (List.range spatialSize))
        (List.range timeCount) := by
  rw [← historyIndices_flatMap timeCount spatialSize]
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap_local value
      (fun time => (List.range spatialSize).map
        (fun spatial => historyIndex spatialSize time spatial))
      (List.range timeCount)) ?_
  apply listQSum_congr
  intro time
  exact Q'.eqv_of_eq (listQSum_map_local value
    (fun spatial => historyIndex spatialSize time spatial)
    (List.range spatialSize))

/-- Coefficients on one fixed spatial slice. -/
def historySpatialSlice
    (spatialSize : Nat) (coefficient : Nat → Q')
    (time spatial : Nat) : Q' :=
  coefficient (historyIndex spatialSize time spatial)

/-- Coefficients on one fixed spatial coordinate through time. -/
def historyTemporalFiber
    (spatialSize : Nat) (coefficient : Nat → Q')
    (spatial time : Nat) : Q' :=
  coefficient (historyIndex spatialSize time spatial)

/-- The block-diagonal spatial part of the FREE-history precision. -/
def freeHistorySpatialPart
    (spatialSize : Nat) (spatialPrecision : Nat → Nat → Q')
    (left right : Nat) : Q' :=
  if historyTime spatialSize left = historyTime spatialSize right then
    spatialPrecision (historySpatial spatialSize left)
      (historySpatial spatialSize right)
  else 0

/-- The repeated temporal-path part of the FREE-history precision. -/
def freeHistoryTemporalPart
    (timeBonds spatialSize : Nat) (left right : Nat) : Q' :=
  if historySpatial spatialSize left = historySpatial spatialSize right then
    freeTemporalPrecision timeBonds
      (historyTime spatialSize left) (historyTime spatialSize right)
  else 0

theorem freeHistoryPrecision_eq_parts
    (timeBonds spatialSize : Nat)
    (spatialPrecision : Nat → Nat → Q')
    (left right : Nat) :
    freeHistoryPrecision timeBonds spatialSize spatialPrecision left right =
      freeHistorySpatialPart spatialSize spatialPrecision left right +
        freeHistoryTemporalPart timeBonds spatialSize left right := by
  rfl

private theorem finiteMatrixQuadratic_historyIndex
    (timeCount spatialSize : Nat) (matrix : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic (timeCount * spatialSize) matrix coefficient ≈
      listQSum
        (fun leftTime => listQSum
          (fun leftSpatial => listQSum
            (fun rightTime => listQSum
              (fun rightSpatial =>
                (coefficient
                    (historyIndex spatialSize leftTime leftSpatial) *
                  coefficient
                    (historyIndex spatialSize rightTime rightSpatial)) *
                  matrix
                    (historyIndex spatialSize leftTime leftSpatial)
                    (historyIndex spatialSize rightTime rightSpatial))
              (List.range spatialSize))
            (List.range timeCount))
          (List.range spatialSize))
        (List.range timeCount) := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun leftTime => listQSum
        (fun leftSpatial => listQSum
          (fun right =>
            (coefficient
                (historyIndex spatialSize leftTime leftSpatial) *
              coefficient right) *
              matrix
                (historyIndex spatialSize leftTime leftSpatial) right)
          (List.range (timeCount * spatialSize)))
        (List.range spatialSize))
      (List.range timeCount)) _
    (listQSum_historyIndex timeCount spatialSize
      (fun left => listQSum
        (fun right =>
          (coefficient left * coefficient right) * matrix left right)
        (List.range (timeCount * spatialSize)))) ?_
  apply listQSum_congr
  intro leftTime
  apply listQSum_congr
  intro leftSpatial
  exact listQSum_historyIndex timeCount spatialSize
    (fun right =>
      (coefficient (historyIndex spatialSize leftTime leftSpatial) *
        coefficient right) *
        matrix (historyIndex spatialSize leftTime leftSpatial) right)

/-- The flattened spatial quadratic is the sum of the same spatial quadratic
over every history slice. -/
theorem finiteMatrixQuadratic_freeHistorySpatialPart
    (timeCount spatialSize : Nat)
    (spatialPrecision : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic (timeCount * spatialSize)
        (freeHistorySpatialPart spatialSize spatialPrecision) coefficient ≈
      listQSum
        (fun time => finiteMatrixQuadratic spatialSize spatialPrecision
          (historySpatialSlice spatialSize coefficient time))
        (List.range timeCount) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun leftTime => listQSum
        (fun leftSpatial => listQSum
          (fun rightTime => listQSum
            (fun rightSpatial =>
              (coefficient
                  (historyIndex spatialSize leftTime leftSpatial) *
                coefficient
                  (historyIndex spatialSize rightTime rightSpatial)) *
                freeHistorySpatialPart spatialSize spatialPrecision
                  (historyIndex spatialSize leftTime leftSpatial)
                  (historyIndex spatialSize rightTime rightSpatial))
            (List.range spatialSize))
          (List.range timeCount))
        (List.range spatialSize))
      (List.range timeCount)) _
    (finiteMatrixQuadratic_historyIndex timeCount spatialSize
      (freeHistorySpatialPart spatialSize spatialPrecision) coefficient) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun leftTime => listQSum
        (fun leftSpatial => listQSum
          (fun rightSpatial =>
            (coefficient
                (historyIndex spatialSize leftTime leftSpatial) *
              coefficient
                (historyIndex spatialSize leftTime rightSpatial)) *
              spatialPrecision leftSpatial rightSpatial)
          (List.range spatialSize))
        (List.range spatialSize))
      (List.range timeCount)) _
    ?_ ?_
  · apply listQSum_congr_on
    intro leftTime hleftTime
    apply listQSum_congr_on
    intro leftSpatial hleftSpatial
    let rowValue := fun rightSpatial =>
      (coefficient (historyIndex spatialSize leftTime leftSpatial) *
        coefficient (historyIndex spatialSize leftTime rightSpatial)) *
        spatialPrecision leftSpatial rightSpatial
    refine Q'.eqv_trans _
      (listQSum
        (fun rightTime =>
          if leftTime = rightTime then
            listQSum rowValue (List.range spatialSize)
          else 0)
        (List.range timeCount)) _ ?_ ?_
    · apply listQSum_congr_on
      intro rightTime _hrightTime
      by_cases htime : leftTime = rightTime
      · subst rightTime
        rw [if_pos rfl]
        apply listQSum_congr_on
        intro rightSpatial hrightSpatial
        have hleft : leftSpatial < spatialSize :=
          List.mem_range.mp hleftSpatial
        have hright : rightSpatial < spatialSize :=
          List.mem_range.mp hrightSpatial
        have hsize : 0 < spatialSize := by omega
        unfold freeHistorySpatialPart rowValue
        rw [historyTime_index hsize hleft,
          historyTime_index hsize hright,
          historySpatial_index hleft, historySpatial_index hright,
          if_pos rfl]
        exact Q'.eqv_refl _
      · rw [if_neg htime]
        refine Q'.eqv_trans _
          (listQSum (fun _rightSpatial => (0 : Q'))
            (List.range spatialSize)) _ ?_ ?_
        · apply listQSum_congr_on
          intro rightSpatial hrightSpatial
          have hleft : leftSpatial < spatialSize :=
            List.mem_range.mp hleftSpatial
          have hright : rightSpatial < spatialSize :=
            List.mem_range.mp hrightSpatial
          have hsize : 0 < spatialSize := by omega
          unfold freeHistorySpatialPart
          rw [historyTime_index hsize hleft,
            historyTime_index hsize hright, if_neg htime]
          exact Q'.mul_zero_eqv _
        · exact listQSum_zero (List.range spatialSize)
    · exact listQSum_ite_single leftTime
        (fun _rightTime => listQSum rowValue (List.range spatialSize))
        (List.range timeCount) (rangeNodupLocal timeCount)
        hleftTime
  · exact Q'.eqv_refl _

/-- The flattened temporal quadratic is the sum of the scalar temporal path
quadratic over every spatial coordinate. -/
theorem finiteMatrixQuadratic_freeHistoryTemporalPart
    (timeBonds spatialSize : Nat) (coefficient : Nat → Q') :
    finiteMatrixQuadratic
        (historySliceCount timeBonds * spatialSize)
        (freeHistoryTemporalPart timeBonds spatialSize) coefficient ≈
      listQSum
        (fun spatial =>
          finiteMatrixQuadratic (historySliceCount timeBonds)
            (freeTemporalPrecision timeBonds)
            (historyTemporalFiber spatialSize coefficient spatial))
        (List.range spatialSize) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun leftTime => listQSum
        (fun leftSpatial => listQSum
          (fun rightTime =>
            (coefficient
                (historyIndex spatialSize leftTime leftSpatial) *
              coefficient
                (historyIndex spatialSize rightTime leftSpatial)) *
              freeTemporalPrecision timeBonds leftTime rightTime)
          (List.range (historySliceCount timeBonds)))
        (List.range spatialSize))
      (List.range (historySliceCount timeBonds))) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (finiteMatrixQuadratic_historyIndex
        (historySliceCount timeBonds) spatialSize
        (freeHistoryTemporalPart timeBonds spatialSize) coefficient) ?_
    apply listQSum_congr_on
    intro leftTime _hleftTime
    apply listQSum_congr_on
    intro leftSpatial hleftSpatial
    apply listQSum_congr_on
    intro rightTime _hrightTime
    refine Q'.eqv_trans _
      (listQSum
        (fun rightSpatial =>
          if leftSpatial = rightSpatial then
            (coefficient
                (historyIndex spatialSize leftTime leftSpatial) *
              coefficient
                (historyIndex spatialSize rightTime rightSpatial)) *
              freeTemporalPrecision timeBonds leftTime rightTime
          else 0)
        (List.range spatialSize)) _ ?_ ?_
    · apply listQSum_congr_on
      intro rightSpatial hrightSpatial
      have hright : rightSpatial < spatialSize :=
        List.mem_range.mp hrightSpatial
      have hleft : leftSpatial < spatialSize :=
        List.mem_range.mp hleftSpatial
      unfold freeHistoryTemporalPart
      have hsize : 0 < spatialSize := by omega
      rw [historySpatial_index hleft, historySpatial_index hright,
        historyTime_index hsize hleft, historyTime_index hsize hright]
      by_cases hspace : leftSpatial = rightSpatial
      · rw [if_pos hspace, if_pos hspace]
        exact Q'.eqv_refl _
      · rw [if_neg hspace, if_neg hspace]
        exact Q'.mul_zero_eqv _
    · exact listQSum_ite_single leftSpatial
        (fun rightSpatial =>
          (coefficient
              (historyIndex spatialSize leftTime leftSpatial) *
            coefficient
              (historyIndex spatialSize rightTime rightSpatial)) *
            freeTemporalPrecision timeBonds leftTime rightTime)
        (List.range spatialSize) (rangeNodupLocal spatialSize)
        hleftSpatial
  · exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (listQSum_swap
      (fun leftTime leftSpatial => listQSum
        (fun rightTime =>
          (coefficient
              (historyIndex spatialSize leftTime leftSpatial) *
            coefficient
              (historyIndex spatialSize rightTime leftSpatial)) *
            freeTemporalPrecision timeBonds leftTime rightTime)
        (List.range (historySliceCount timeBonds)))
      (List.range (historySliceCount timeBonds))
      (List.range spatialSize)))
      (Q'.eqv_refl _)

/-- Exact decomposition of the complete flattened FREE-history quadratic. -/
theorem finiteMatrixQuadratic_freeHistoryPrecision
    (timeBonds spatialSize : Nat)
    (spatialPrecision : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic
        (historyCoordinateCount timeBonds spatialSize)
        (freeHistoryPrecision timeBonds spatialSize spatialPrecision)
        coefficient ≈
      listQSum
          (fun time => finiteMatrixQuadratic spatialSize spatialPrecision
            (historySpatialSlice spatialSize coefficient time))
          (List.range (historySliceCount timeBonds)) +
        listQSum
          (fun spatial =>
            finiteMatrixQuadratic (historySliceCount timeBonds)
              (freeTemporalPrecision timeBonds)
              (historyTemporalFiber spatialSize coefficient spatial))
          (List.range spatialSize) := by
  unfold historyCoordinateCount
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic
        (historySliceCount timeBonds * spatialSize)
        (freeHistorySpatialPart spatialSize spatialPrecision) coefficient +
      finiteMatrixQuadratic
        (historySliceCount timeBonds * spatialSize)
        (freeHistoryTemporalPart timeBonds spatialSize) coefficient) _ ?_ ?_
  · unfold finiteMatrixQuadratic
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum
              (fun right =>
                (coefficient left * coefficient right) *
                  freeHistorySpatialPart spatialSize spatialPrecision
                    left right)
              (List.range (historySliceCount timeBonds * spatialSize)) +
            listQSum
              (fun right =>
                (coefficient left * coefficient right) *
                  freeHistoryTemporalPart timeBonds spatialSize left right)
              (List.range (historySliceCount timeBonds * spatialSize)))
        (List.range (historySliceCount timeBonds * spatialSize))) _ ?_ ?_
    · apply listQSum_congr_on
      intro left _hleft
      refine Q'.eqv_trans _
        (listQSum
          (fun right =>
            (coefficient left * coefficient right) *
                freeHistorySpatialPart spatialSize spatialPrecision left right +
              (coefficient left * coefficient right) *
                freeHistoryTemporalPart timeBonds spatialSize left right)
          (List.range (historySliceCount timeBonds * spatialSize))) _ ?_ ?_
      · apply listQSum_congr_on
        intro right _hright
        rw [freeHistoryPrecision_eq_parts]
        exact Q'.mul_add_eqv _ _ _
      · exact listQSum_add _ _ _
    · exact listQSum_add _ _ _
  · exact Q'.add_eqv_congr'
      (finiteMatrixQuadratic_freeHistorySpatialPart
        (historySliceCount timeBonds) spatialSize spatialPrecision coefficient)
      (finiteMatrixQuadratic_freeHistoryTemporalPart
        timeBonds spatialSize coefficient)

end YMGap.Continuum.FiniteRationalFreeHistoryQuadratic

#print axioms YMGap.Continuum.FiniteRationalFreeHistoryQuadratic.listQSum_historyIndex
#print axioms YMGap.Continuum.FiniteRationalFreeHistoryQuadratic.finiteMatrixQuadratic_freeHistorySpatialPart
#print axioms YMGap.Continuum.FiniteRationalFreeHistoryQuadratic.finiteMatrixQuadratic_freeHistoryTemporalPart
#print axioms YMGap.Continuum.FiniteRationalFreeHistoryQuadratic.finiteMatrixQuadratic_freeHistoryPrecision
