/-
# Exact two-slice cross covariance for the finite comb FREE history

For every nonempty finite comb-gauge coordinate space, the canonical exact
one-bond FREE-history covariance has the explicit two-by-two block form whose
cross block is the constructive inverse of `A^T A + 2 A`, where `A` is the
comb spatial precision.  In particular that cross block is strictly positive
on every spatial row carrying an explicit nonzero coordinate.

This is an exact finite rational identity.  It proves no Gaussian-law limit,
compact-Haar comparison, continuum construction, Hamiltonian statement, or
Clay mass gap.
-/

import YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _ :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem listQSum_append_local {A : Type} (value : A → Q') :
    ∀ left right : List A,
      listQSum value (left ++ right) ≈
        listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | head :: tail, right => by
      change value head + listQSum value (tail ++ right) ≈
        (value head + listQSum value tail) + listQSum value right
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_append_local value tail right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

/-- A spatial row placed on the first slice of a two-slice flattened row. -/
def twoSliceTopRow
    (n : Nat) (coefficient : Nat → Q') (index : Nat) : Q' :=
  if index < n then coefficient index else 0

/-- A spatial row placed on the second slice of a two-slice flattened row. -/
def twoSliceBottomRow
    (n : Nat) (coefficient : Nat → Q') (index : Nat) : Q' :=
  if index < n then 0 else coefficient (index - n)

/-- A top-slice/bottom-slice bilinear through a literal two-by-two block
matrix is exactly the quadratic form of its top-right block. -/
theorem finiteMatrixBilinear_twoByTwoBlock_top_bottom
    (n : Nat) (topLeft topRight bottomLeft bottomRight : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixBilinear (n + n)
        (twoByTwoBlock n topLeft topRight bottomLeft bottomRight)
        (twoSliceTopRow n coefficient)
        (twoSliceBottomRow n coefficient) ≈
      finiteMatrixQuadratic n topRight coefficient := by
  unfold finiteMatrixBilinear
  simp only [qListSum_map_eq_listQSum_local]
  rw [List.range_add]
  refine Q'.eqv_trans _ _ _
    (listQSum_append_local _ (List.range n)
      ((List.range n).map fun index => n + index)) ?_
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic n topRight coefficient + 0) _ ?_
    (Q'.eqv_of_eq (Q'.add_zero' _))
  apply Q'.add_eqv_congr'
  · unfold finiteMatrixQuadratic
    apply listQSum_congr_on
    intro left hleft
    have hleftLt : left < n := List.mem_range.mp hleft
    refine Q'.eqv_trans _ _ _
      (listQSum_append_local _ (List.range n)
        ((List.range n).map fun index => n + index)) ?_
    refine Q'.eqv_trans _
      (0 + listQSum
        (fun right =>
          (coefficient left * coefficient right) * topRight left right)
        (List.range n)) _ ?_ (QPoly.q_zero_add_eqv _)
    apply Q'.add_eqv_congr'
    · refine Q'.eqv_trans _
        (listQSum (fun _index => (0 : Q')) (List.range n)) _ ?_
        (listQSum_zero (List.range n))
      apply listQSum_congr_on
      intro right hright
      have hrightLt : right < n := List.mem_range.mp hright
      simp only [twoSliceTopRow, twoSliceBottomRow,
        if_pos hleftLt, if_pos hrightLt]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
        (Q'.zero_mul_eqv _)
    · rw [listQSum_map_local]
      apply listQSum_congr_on
      intro right hright
      have hrightLt : right < n := List.mem_range.mp hright
      have hshift : ¬n + right < n := by omega
      simp only [twoSliceTopRow, twoSliceBottomRow, twoByTwoBlock,
        if_pos hleftLt, if_neg hshift, Nat.add_sub_cancel_left]
      exact Q'.eqv_refl _
  · rw [listQSum_map_local]
    refine Q'.eqv_trans _
      (listQSum (fun _index => (0 : Q')) (List.range n)) _ ?_
      (listQSum_zero (List.range n))
    apply listQSum_congr_on
    intro left hleft
    have hleftLt : left < n := List.mem_range.mp hleft
    have hshift : ¬n + left < n := by omega
    refine Q'.eqv_trans _
      (listQSum (fun _index => (0 : Q'))
        (List.range n ++ (List.range n).map fun index => n + index)) _ ?_
      (listQSum_zero
        (List.range n ++ (List.range n).map fun index => n + index))
    apply listQSum_congr_on
    intro right _hright
    simp only [twoSliceTopRow, if_neg hshift]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
      (Q'.zero_mul_eqv _)

private theorem qmul_congr_local {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem finiteMatrixBilinear_congr_local
    {n : Nat} {matrix matrix' : Nat → Nat → Q'}
    {left left' right right' : Nat → Q'}
    (hmatrix : FiniteMatrixEqv n matrix matrix')
    (hleft : ∀ {index : Nat}, index < n → left index ≈ left' index)
    (hright : ∀ {index : Nat}, index < n → right index ≈ right' index) :
    finiteMatrixBilinear n matrix left right ≈
      finiteMatrixBilinear n matrix' left' right' := by
  unfold finiteMatrixBilinear
  simp only [qListSum_map_eq_listQSum_local]
  apply listQSum_congr_on
  intro leftIndex hleftIndex
  have hleftIndexLt : leftIndex < n := List.mem_range.mp hleftIndex
  apply listQSum_congr_on
  intro rightIndex hrightIndex
  have hrightIndexLt : rightIndex < n := List.mem_range.mp hrightIndex
  exact qmul_congr_local
    (qmul_congr_local (hleft hleftIndexLt) (hright hrightIndexLt))
    (hmatrix hleftIndexLt hrightIndexLt)

/-- On the two-slice finite prefix, a time-zero comb curl row is the literal
top-slice embedding of its spatial curl row. -/
theorem combGaugeFreeHistoryCurlRow_zero_eq_top
    (width faceIndex : Nat) (hsize : 0 < combGaugeEdgeCount width)
    {coordinate : Nat}
    (hcoordinate : coordinate <
      combGaugeEdgeCount width + combGaugeEdgeCount width) :
    combGaugeFreeHistoryCurlRow width 0 faceIndex coordinate ≈
      twoSliceTopRow (combGaugeEdgeCount width)
        (combGaugeCurl width faceIndex) coordinate := by
  let spatialSize := combGaugeEdgeCount width
  by_cases htop : coordinate < spatialSize
  · have hindex : historyIndex spatialSize 0 coordinate = coordinate := by
      simp [historyIndex]
    have hvalue :
        combGaugeFreeHistoryCurlRow width 0 faceIndex coordinate =
          combGaugeCurl width faceIndex coordinate := by
      have hraw := combGaugeFreeHistoryCurlRow_historyIndex
        (width := width) (time := 0) (faceIndex := faceIndex)
        (gaugeIndex := coordinate) htop
      rw [hindex] at hraw
      exact hraw
    unfold twoSliceTopRow
    rw [if_pos htop]
    exact Q'.eqv_of_eq hvalue
  · have hlower : spatialSize ≤ coordinate := Nat.le_of_not_gt htop
    have hsub : coordinate - spatialSize < spatialSize := by omega
    have hindex :
        historyIndex spatialSize 1 (coordinate - spatialSize) = coordinate := by
      unfold historyIndex
      omega
    have htime : historyTime spatialSize coordinate = 1 := by
      rw [← hindex]
      exact historyTime_index hsize hsub
    unfold combGaugeFreeHistoryCurlRow twoSliceTopRow
    rw [htime, if_neg (by decide : (1 : Nat) ≠ 0), if_neg htop]
    exact Q'.eqv_refl _

/-- On the two-slice finite prefix, a time-one comb curl row is the literal
bottom-slice embedding of its spatial curl row. -/
theorem combGaugeFreeHistoryCurlRow_one_eq_bottom
    (width faceIndex : Nat) (hsize : 0 < combGaugeEdgeCount width)
    {coordinate : Nat}
    (hcoordinate : coordinate <
      combGaugeEdgeCount width + combGaugeEdgeCount width) :
    combGaugeFreeHistoryCurlRow width 1 faceIndex coordinate ≈
      twoSliceBottomRow (combGaugeEdgeCount width)
        (combGaugeCurl width faceIndex) coordinate := by
  let spatialSize := combGaugeEdgeCount width
  by_cases htop : coordinate < spatialSize
  · have hindex : historyIndex spatialSize 0 coordinate = coordinate := by
      simp [historyIndex]
    have htime : historyTime spatialSize coordinate = 0 := by
      rw [← hindex]
      exact historyTime_index hsize htop
    unfold combGaugeFreeHistoryCurlRow twoSliceBottomRow
    rw [htime, if_neg (by decide : (0 : Nat) ≠ 1), if_pos htop]
    exact Q'.eqv_refl _
  · have hlower : spatialSize ≤ coordinate := Nat.le_of_not_gt htop
    have hsub : coordinate - spatialSize < spatialSize := by omega
    have hindex :
        historyIndex spatialSize 1 (coordinate - spatialSize) = coordinate := by
      unfold historyIndex
      omega
    have hvalue :
        combGaugeFreeHistoryCurlRow width 1 faceIndex coordinate =
          combGaugeCurl width faceIndex (coordinate - spatialSize) := by
      have hraw := combGaugeFreeHistoryCurlRow_historyIndex
        (width := width) (time := 1) (faceIndex := faceIndex)
        (gaugeIndex := coordinate - spatialSize) hsub
      rw [hindex] at hraw
      exact hraw
    unfold twoSliceBottomRow
    rw [if_neg htop]
    exact Q'.eqv_of_eq hvalue

/-- The canonical one-bond comb FREE-history covariance is exactly the
explicit two-slice block covariance. -/
theorem combGaugeFreeHistoryCovariance_one_eq_twoSliceBlock
    (width : Nat) (hsize : 0 < combGaugeEdgeCount width) :
    FiniteMatrixEqv
      (combGaugeEdgeCount width + combGaugeEdgeCount width)
      (combGaugeFreeHistoryCovariance 1 width)
      (twoSliceBlockCovariance
        (combGaugeEdgeCount width)
        (combGaugeSpatialPrecision width)
        (combGaugeSpatialPrecision_symmetric width)
        (combGaugeSpatialPrecision_strictlyPositive width)) := by
  let spatialSize := combGaugeEdgeCount width
  have hprecision :
      FiniteMatrixEqv (spatialSize + spatialSize)
        (combGaugeFreeHistoryPrecision 1 width)
        (twoSliceBlockPrecision spatialSize
          (combGaugeSpatialPrecision width)) := by
    intro row column hrow hcolumn
    simpa only [spatialSize, combGaugeFreeHistoryPrecision,
      freeHistoryCurlPrecision, combGaugeSpatialPrecision] using
      (freeHistoryPrecision_one_eq_twoSliceBlock spatialSize
        (combGaugeSpatialPrecision width) hsize hrow hcolumn)
  let originalData := combGaugeFreeHistoryInverseData 1 width
  let hdata :
      FiniteMatrixInverseData (spatialSize + spatialSize)
        (combGaugeFreeHistoryPrecision 1 width) :=
    { inverse := originalData.inverse
      matrix_inverse := by
        intro row column hrow hcolumn
        have hrow' : row <
            historyCoordinateCount 1 (combGaugeEdgeCount width) := by
          simpa [spatialSize, historyCoordinateCount, historySliceCount,
            Nat.succ_mul] using hrow
        have hcolumn' : column <
            historyCoordinateCount 1 (combGaugeEdgeCount width) := by
          simpa [spatialSize, historyCoordinateCount, historySliceCount,
            Nat.succ_mul] using hcolumn
        simpa [spatialSize, historyCoordinateCount, historySliceCount,
          Nat.succ_mul, originalData] using
          originalData.matrix_inverse hrow' hcolumn'
      inverse_matrix := by
        intro row column hrow hcolumn
        have hrow' : row <
            historyCoordinateCount 1 (combGaugeEdgeCount width) := by
          simpa [spatialSize, historyCoordinateCount, historySliceCount,
            Nat.succ_mul] using hrow
        have hcolumn' : column <
            historyCoordinateCount 1 (combGaugeEdgeCount width) := by
          simpa [spatialSize, historyCoordinateCount, historySliceCount,
            Nat.succ_mul] using hcolumn
        simpa [spatialSize, historyCoordinateCount, historySliceCount,
          Nat.succ_mul, originalData] using
          originalData.inverse_matrix hrow' hcolumn' }
  intro row column hrow hcolumn
  simpa [spatialSize, combGaugeFreeHistoryCovariance, hdata, originalData] using
    (finiteMatrixInverse_eq_twoSliceBlockCovariance_of_precision
      spatialSize (combGaugeSpatialPrecision width)
      (combGaugeFreeHistoryPrecision 1 width)
      (combGaugeSpatialPrecision_symmetric width)
      (combGaugeSpatialPrecision_strictlyPositive width)
      hprecision hdata hrow hcolumn)

/-- Every endpoint-to-endpoint entry of the canonical one-bond comb
covariance is the corresponding entry of the constructive cross inverse. -/
theorem combGaugeFreeHistoryCovariance_one_cross_entry
    (width : Nat) (hsize : 0 < combGaugeEdgeCount width)
    {left right : Nat}
    (hleft : left < combGaugeEdgeCount width)
    (hright : right < combGaugeEdgeCount width) :
    combGaugeFreeHistoryCovariance 1 width
        (historyIndex (combGaugeEdgeCount width) 0 left)
        (historyIndex (combGaugeEdgeCount width) 1 right) ≈
      twoSliceCrossCovariance
        (combGaugeEdgeCount width)
        (combGaugeSpatialPrecision width)
        (combGaugeSpatialPrecision_symmetric width)
        (combGaugeSpatialPrecision_strictlyPositive width)
        left right := by
  have hleftIndex :
      historyIndex (combGaugeEdgeCount width) 0 left <
        combGaugeEdgeCount width + combGaugeEdgeCount width := by
    simp [historyIndex]
    omega
  have hrightIndex :
      historyIndex (combGaugeEdgeCount width) 1 right <
        combGaugeEdgeCount width + combGaugeEdgeCount width := by
    unfold historyIndex
    omega
  have hentry := combGaugeFreeHistoryCovariance_one_eq_twoSliceBlock
    width hsize hleftIndex hrightIndex
  have hrightShift :
      ¬combGaugeEdgeCount width + right < combGaugeEdgeCount width := by
    omega
  simpa [historyIndex, twoSliceBlockCovariance, twoByTwoBlock, hleft,
    hrightShift] using hentry

/-- The exact time-zero/time-one covariance bilinear of one comb curl row is
the strictly positive spatial cross-block quadratic form. -/
theorem combGaugeFreeHistoryCurlCrossBilinear_eq_quadratic
    (width faceIndex : Nat) (hsize : 0 < combGaugeEdgeCount width) :
    combGaugeFreeHistoryCovarianceBilinear 1 width
        (combGaugeFreeHistoryCurlRow width 0 faceIndex)
        (combGaugeFreeHistoryCurlRow width 1 faceIndex) ≈
      finiteMatrixQuadratic
        (combGaugeEdgeCount width)
        (twoSliceCrossCovariance
          (combGaugeEdgeCount width)
          (combGaugeSpatialPrecision width)
          (combGaugeSpatialPrecision_symmetric width)
          (combGaugeSpatialPrecision_strictlyPositive width))
        (combGaugeCurl width faceIndex) := by
  let spatialSize := combGaugeEdgeCount width
  let coefficient := combGaugeCurl width faceIndex
  have hmatrix :
      FiniteMatrixEqv (spatialSize + spatialSize)
        (combGaugeFreeHistoryCovariance 1 width)
        (twoSliceBlockCovariance spatialSize
          (combGaugeSpatialPrecision width)
          (combGaugeSpatialPrecision_symmetric width)
          (combGaugeSpatialPrecision_strictlyPositive width)) := by
    intro row column hrow hcolumn
    exact combGaugeFreeHistoryCovariance_one_eq_twoSliceBlock
      width hsize hrow hcolumn
  have hleft :
      ∀ {index : Nat}, index < spatialSize + spatialSize →
        combGaugeFreeHistoryCurlRow width 0 faceIndex index ≈
          twoSliceTopRow spatialSize coefficient index := by
    intro index hindex
    exact combGaugeFreeHistoryCurlRow_zero_eq_top
      width faceIndex hsize hindex
  have hright :
      ∀ {index : Nat}, index < spatialSize + spatialSize →
        combGaugeFreeHistoryCurlRow width 1 faceIndex index ≈
          twoSliceBottomRow spatialSize coefficient index := by
    intro index hindex
    exact combGaugeFreeHistoryCurlRow_one_eq_bottom
      width faceIndex hsize hindex
  have hcongr :
      finiteMatrixBilinear (spatialSize + spatialSize)
          (combGaugeFreeHistoryCovariance 1 width)
          (combGaugeFreeHistoryCurlRow width 0 faceIndex)
          (combGaugeFreeHistoryCurlRow width 1 faceIndex) ≈
        finiteMatrixBilinear (spatialSize + spatialSize)
          (twoSliceBlockCovariance spatialSize
            (combGaugeSpatialPrecision width)
            (combGaugeSpatialPrecision_symmetric width)
            (combGaugeSpatialPrecision_strictlyPositive width))
          (twoSliceTopRow spatialSize coefficient)
          (twoSliceBottomRow spatialSize coefficient) :=
    finiteMatrixBilinear_congr_local hmatrix hleft hright
  have hblock := finiteMatrixBilinear_twoByTwoBlock_top_bottom
    spatialSize
    (twoSliceDiagonalCovariance spatialSize
      (combGaugeSpatialPrecision width)
      (combGaugeSpatialPrecision_symmetric width)
      (combGaugeSpatialPrecision_strictlyPositive width))
    (twoSliceCrossCovariance spatialSize
      (combGaugeSpatialPrecision width)
      (combGaugeSpatialPrecision_symmetric width)
      (combGaugeSpatialPrecision_strictlyPositive width))
    (twoSliceCrossCovariance spatialSize
      (combGaugeSpatialPrecision width)
      (combGaugeSpatialPrecision_symmetric width)
      (combGaugeSpatialPrecision_strictlyPositive width))
    (twoSliceDiagonalCovariance spatialSize
      (combGaugeSpatialPrecision width)
      (combGaugeSpatialPrecision_symmetric width)
      (combGaugeSpatialPrecision_strictlyPositive width))
    coefficient
  have hresult := Q'.eqv_trans _ _ _ hcongr hblock
  simpa [spatialSize, coefficient, combGaugeFreeHistoryCovarianceBilinear,
    historyCoordinateCount, historySliceCount, Nat.succ_mul,
    twoSliceBlockCovariance] using hresult

/-- The exact one-bond comb cross-covariance block is strictly positive on
every spatial coefficient vector with an explicit nonzero in-range entry. -/
theorem combGaugeOneBondCrossCovariance_strictlyPositive (width : Nat) :
    FiniteMatrixStrictlyPositive
      (combGaugeEdgeCount width)
      (twoSliceCrossCovariance
        (combGaugeEdgeCount width)
        (combGaugeSpatialPrecision width)
        (combGaugeSpatialPrecision_symmetric width)
        (combGaugeSpatialPrecision_strictlyPositive width)) :=
  twoSliceCrossInverse_strictlyPositive
    (combGaugeEdgeCount width)
    (combGaugeSpatialPrecision width)
    (combGaugeSpatialPrecision_symmetric width)
    (combGaugeSpatialPrecision_strictlyPositive width)

/-- Direct quadratic-form interface for consuming strict positivity of the
one-bond comb cross covariance. -/
theorem combGaugeOneBondCrossQuadratic_positive_of_coordinate_not_eqv_zero
    (width : Nat) (coefficient : Nat → Q') {gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width)
    (hcoefficient : ¬ coefficient gaugeIndex ≈ 0) :
    (0 : Q') <
      finiteMatrixQuadratic
        (combGaugeEdgeCount width)
        (twoSliceCrossCovariance
          (combGaugeEdgeCount width)
          (combGaugeSpatialPrecision width)
          (combGaugeSpatialPrecision_symmetric width)
          (combGaugeSpatialPrecision_strictlyPositive width))
        coefficient :=
  combGaugeOneBondCrossCovariance_strictlyPositive width
    coefficient gaugeIndex hgauge hcoefficient

/-- A comb curl row with one explicit nonzero chord coefficient has strictly
positive exact covariance between the two endpoints of one time bond. -/
theorem combGaugeFreeHistoryCurlCrossBilinear_pos_of_coordinate_not_eqv_zero
    (width faceIndex : Nat) (hsize : 0 < combGaugeEdgeCount width)
    {gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width)
    (hcurl : ¬combGaugeCurl width faceIndex gaugeIndex ≈ 0) :
    (0 : Q') <
      combGaugeFreeHistoryCovarianceBilinear 1 width
        (combGaugeFreeHistoryCurlRow width 0 faceIndex)
        (combGaugeFreeHistoryCurlRow width 1 faceIndex) := by
  have hpositive :=
    combGaugeOneBondCrossQuadratic_positive_of_coordinate_not_eqv_zero
      width (combGaugeCurl width faceIndex) hgauge hcurl
  exact Q'.pos_of_lt_of_le hpositive
    (Q'.ge_of_eqv
      (combGaugeFreeHistoryCurlCrossBilinear_eq_quadratic
        width faceIndex hsize))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance.combGaugeFreeHistoryCovariance_one_eq_twoSliceBlock
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance.combGaugeFreeHistoryCovariance_one_cross_entry
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance.combGaugeFreeHistoryCurlCrossBilinear_eq_quadratic
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance.combGaugeOneBondCrossCovariance_strictlyPositive
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance.combGaugeOneBondCrossQuadratic_positive_of_coordinate_not_eqv_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance.combGaugeFreeHistoryCurlCrossBilinear_pos_of_coordinate_not_eqv_zero
