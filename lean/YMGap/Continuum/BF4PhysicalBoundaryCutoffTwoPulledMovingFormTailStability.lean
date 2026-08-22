/-
# Full moving-form tail stability on the cutoff-two physical carrier

The cutoff law and the root-centered coefficient both move with the
representation cutoff.  This module combines their two independent Cauchy
controls.  First, the corrected-slab entry modulus is packaged as uniform
relative kernel and weight errors on the fixed cutoff-two carrier.  Those
uniform entry errors can then be applied to the coefficient centered at the
first cutoff, while the same-law recentering theorem compares that coefficient
with the one centered at the later cutoff.

The result is a genuine late-pair stability theorem for the actual moving
matrix and diagonal forms.  It does not control the finite segment from the
verified cutoff-two gap anchor to the beginning of the tail.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Uniform entry errors from the corrected-slab modulus -/

def cutoffTwoPulledEntryErrorAnchor (epsilon : Q') : Nat :=
  max cutoffTwoPulledRowFloorAnchor
    (slabNomeBoundedObservableModulus
      cutoffTwoHalfCoupling (centralExtent 0) epsilon)

theorem cutoffTwoPulledEntryErrorAnchor_ge_floor (epsilon : Q') :
    cutoffTwoPulledRowFloorAnchor ≤
      cutoffTwoPulledEntryErrorAnchor epsilon := by
  unfold cutoffTwoPulledEntryErrorAnchor
  exact Nat.le_max_left _ _

theorem cutoffTwoPulledEntryErrorAnchor_ge_two (epsilon : Q') :
    2 ≤ cutoffTwoPulledEntryErrorAnchor epsilon := by
  have htwoFloor : 2 ≤ cutoffTwoPulledRowFloorAnchor := by
    unfold cutoffTwoPulledRowFloorAnchor
    exact Nat.le_max_left _ _
  exact Nat.le_trans htwoFloor
    (cutoffTwoPulledEntryErrorAnchor_ge_floor epsilon)

theorem cutoffTwoPulledEntryErrorAnchor_ge_modulus (epsilon : Q') :
    slabNomeBoundedObservableModulus
        cutoffTwoHalfCoupling (centralExtent 0) epsilon ≤
      cutoffTwoPulledEntryErrorAnchor epsilon := by
  unfold cutoffTwoPulledEntryErrorAnchor
  exact Nat.le_max_right _ _

def cutoffTwoPulledKernelEntryErrorAt_of_anchor
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first later : Nat}
    (hfirst : cutoffTwoPulledEntryErrorAnchor epsilon ≤ first)
    (hlater : cutoffTwoPulledEntryErrorAnchor epsilon ≤ later) :
    CutoffTwoPulledKernelEntryErrorAt first later epsilon := by
  refine
    { later_ge_floor := Nat.le_trans
        (cutoffTwoPulledEntryErrorAnchor_ge_floor epsilon) hlater
      epsilon_nonnegative := Q'.le_of_lt hepsilon
      entry_error := ?_ }
  intro row column hrow hcolumn
  have hbaseFirst : 2 ≤ first := Nat.le_trans
    (cutoffTwoPulledEntryErrorAnchor_ge_two epsilon) hfirst
  have hbaseLater : 2 ≤ later := Nat.le_trans
    (cutoffTwoPulledEntryErrorAnchor_ge_two epsilon) hlater
  have hmodFirst : slabNomeBoundedObservableModulus
      cutoffTwoHalfCoupling (centralExtent 0) epsilon ≤ first :=
    Nat.le_trans
      (cutoffTwoPulledEntryErrorAnchor_ge_modulus epsilon) hfirst
  have hmodLater : slabNomeBoundedObservableModulus
      cutoffTwoHalfCoupling (centralExtent 0) epsilon ≤ later :=
    Nat.le_trans
      (cutoffTwoPulledEntryErrorAnchor_ge_modulus epsilon) hlater
  have hrowLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hrow
  have hcolumnLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hcolumn
  have htwo := centralPhysicalFinitePulledKernel_twoSided_of_modulus
    (w := cutoffTwoHalfCoupling) (base := 2) (half := 0)
    (first := first) (second := later) (row := row) (column := column)
    (epsilon := epsilon)
    (by decide) (by decide) hepsilon hbaseFirst hbaseLater
    hmodFirst hmodLater hrowLt hcolumnLt
  exact CReal.abs_sub_le_of_bounds htwo.1 htwo.2

def cutoffTwoPulledWeightEntryErrorAt_of_anchor
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first later : Nat}
    (hfirst : cutoffTwoPulledEntryErrorAnchor epsilon ≤ first)
    (hlater : cutoffTwoPulledEntryErrorAnchor epsilon ≤ later) :
    CutoffTwoPulledWeightEntryErrorAt first later epsilon := by
  refine
    { later_ge_floor := Nat.le_trans
        (cutoffTwoPulledEntryErrorAnchor_ge_floor epsilon) hlater
      epsilon_nonnegative := Q'.le_of_lt hepsilon
      entry_error := ?_ }
  intro index hindex
  have hbaseFirst : 2 ≤ first := Nat.le_trans
    (cutoffTwoPulledEntryErrorAnchor_ge_two epsilon) hfirst
  have hbaseLater : 2 ≤ later := Nat.le_trans
    (cutoffTwoPulledEntryErrorAnchor_ge_two epsilon) hlater
  have hmodFirst : slabNomeBoundedObservableModulus
      cutoffTwoHalfCoupling (centralExtent 0) epsilon ≤ first :=
    Nat.le_trans
      (cutoffTwoPulledEntryErrorAnchor_ge_modulus epsilon) hfirst
  have hmodLater : slabNomeBoundedObservableModulus
      cutoffTwoHalfCoupling (centralExtent 0) epsilon ≤ later :=
    Nat.le_trans
      (cutoffTwoPulledEntryErrorAnchor_ge_modulus epsilon) hlater
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hindex
  have htwo := centralPhysicalFinitePulledWeight_twoSided_of_modulus
    (w := cutoffTwoHalfCoupling) (base := 2) (half := 0)
    (first := first) (second := later) (index := index)
    (epsilon := epsilon)
    (by decide) (by decide) hepsilon hbaseFirst hbaseLater
    hmodFirst hmodLater hindexLt
  exact CReal.abs_sub_le_of_bounds htwo.1 htwo.2

/-! ## 2. Arbitrary positive relative law-error budgets -/

def cutoffTwoPulledMatrixEntryTolerance
    (matrixError : Q') : Q' :=
  Q'.divPos
    (matrixError * cutoffTwoPulledUniformPositiveRowFloor)
    (Q'.ofNat cutoffTwoPulledStates.length + 1)
    (positive_scale (ExpNeg.ofNat_nonneg' cutoffTwoPulledStates.length))

def cutoffTwoPulledWeightEntryTolerance
    (diagonalError : Q') : Q' :=
  Q'.divPos
    (diagonalError * cutoffTwoPulledUniformPositiveRowFloor)
    ((1 : Q') + 1)
    (positive_scale (by decide : (0 : Q') ≤ 1))

theorem cutoffTwoPulledMatrixEntryTolerance_pos
    {matrixError : Q'} (hmatrix : (0 : Q') < matrixError) :
    (0 : Q') < cutoffTwoPulledMatrixEntryTolerance matrixError := by
  unfold cutoffTwoPulledMatrixEntryTolerance
  exact Q'.divPos_pos _ _ _
    (Q'.mul_pos hmatrix cutoffTwoPulledUniformPositiveRowFloor_pos)

theorem cutoffTwoPulledWeightEntryTolerance_pos
    {diagonalError : Q'} (hdiagonal : (0 : Q') < diagonalError) :
    (0 : Q') < cutoffTwoPulledWeightEntryTolerance diagonalError := by
  unfold cutoffTwoPulledWeightEntryTolerance
  exact Q'.divPos_pos _ _ _
    (Q'.mul_pos hdiagonal cutoffTwoPulledUniformPositiveRowFloor_pos)

theorem cutoffTwoPulledMatrixEntryTolerance_budget
    {matrixError : Q'} (hmatrix : (0 : Q') < matrixError) :
    Q'.ofNat cutoffTwoPulledStates.length *
        cutoffTwoPulledMatrixEntryTolerance matrixError ≤
      matrixError * cutoffTwoPulledUniformPositiveRowFloor := by
  unfold cutoffTwoPulledMatrixEntryTolerance
  exact scaled_divPos_le_epsilon
    (ExpNeg.ofNat_nonneg' cutoffTwoPulledStates.length)
    (Q'.mul_pos hmatrix cutoffTwoPulledUniformPositiveRowFloor_pos)

theorem cutoffTwoPulledWeightEntryTolerance_budget
    {diagonalError : Q'} (hdiagonal : (0 : Q') < diagonalError) :
    cutoffTwoPulledWeightEntryTolerance diagonalError ≤
      diagonalError * cutoffTwoPulledUniformPositiveRowFloor := by
  have hscaled := scaled_divPos_le_epsilon
    (by decide : (0 : Q') ≤ 1)
    (Q'.mul_pos hdiagonal cutoffTwoPulledUniformPositiveRowFloor_pos)
  unfold cutoffTwoPulledWeightEntryTolerance at hscaled ⊢
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))) hscaled

/-- Uniform relative law errors at one cutoff pair.  The entry certificates
are coefficient-independent, so the form bounds may later be instantiated at
the moving coefficient selected by `first`. -/
structure CutoffTwoPulledRelativeLawErrorAt
    (first later : Nat) (matrixError diagonalError : Q') : Type where
  kernelEntry : CutoffTwoPulledKernelEntryErrorAt first later
    (cutoffTwoPulledMatrixEntryTolerance matrixError)
  weightEntry : CutoffTwoPulledWeightEntryErrorAt first later
    (cutoffTwoPulledWeightEntryTolerance diagonalError)
  matrixBudget : Q'.ofNat cutoffTwoPulledStates.length *
      cutoffTwoPulledMatrixEntryTolerance matrixError ≤
    matrixError * cutoffTwoPulledUniformPositiveRowFloor
  diagonalBudget : cutoffTwoPulledWeightEntryTolerance diagonalError ≤
    diagonalError * cutoffTwoPulledUniformPositiveRowFloor

namespace CutoffTwoPulledRelativeLawErrorAt

theorem matrix_error
    {first later : Nat} {matrixError diagonalError : Q'}
    (error : CutoffTwoPulledRelativeLawErrorAt
      first later matrixError diagonalError)
    (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledMatrixAt first coefficient +
          (-cutoffTwoPulledMatrixAt later coefficient)) ≤
      matrixError * cutoffTwoPulledDiagonalAt later coefficient :=
  error.kernelEntry.matrix_error error.matrixBudget coefficient

theorem diagonal_error
    {first later : Nat} {matrixError diagonalError : Q'}
    (error : CutoffTwoPulledRelativeLawErrorAt
      first later matrixError diagonalError)
    (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledDiagonalAt first coefficient +
          (-cutoffTwoPulledDiagonalAt later coefficient)) ≤
      diagonalError * cutoffTwoPulledDiagonalAt later coefficient :=
  error.weightEntry.diagonal_error error.diagonalBudget coefficient

end CutoffTwoPulledRelativeLawErrorAt

def cutoffTwoPulledRelativeLawErrorAnchor
    (matrixError diagonalError : Q') : Nat :=
  max
    (cutoffTwoPulledEntryErrorAnchor
      (cutoffTwoPulledMatrixEntryTolerance matrixError))
    (cutoffTwoPulledEntryErrorAnchor
      (cutoffTwoPulledWeightEntryTolerance diagonalError))

def cutoffTwoPulledRelativeLawErrors_cofinally
    (matrixError diagonalError : Q')
    (hmatrix : (0 : Q') < matrixError)
    (hdiagonal : (0 : Q') < diagonalError) :
    ∀ first later : Nat,
      cutoffTwoPulledRelativeLawErrorAnchor matrixError diagonalError ≤ first →
      cutoffTwoPulledRelativeLawErrorAnchor matrixError diagonalError ≤ later →
      CutoffTwoPulledRelativeLawErrorAt
        first later matrixError diagonalError := by
  intro first later hfirst hlater
  have hmatrixAnchor : cutoffTwoPulledEntryErrorAnchor
      (cutoffTwoPulledMatrixEntryTolerance matrixError) ≤
      cutoffTwoPulledRelativeLawErrorAnchor matrixError diagonalError := by
    unfold cutoffTwoPulledRelativeLawErrorAnchor
    exact Nat.le_max_left _ _
  have hweightAnchor : cutoffTwoPulledEntryErrorAnchor
      (cutoffTwoPulledWeightEntryTolerance diagonalError) ≤
      cutoffTwoPulledRelativeLawErrorAnchor matrixError diagonalError := by
    unfold cutoffTwoPulledRelativeLawErrorAnchor
    exact Nat.le_max_right _ _
  refine
    { kernelEntry := cutoffTwoPulledKernelEntryErrorAt_of_anchor
        (cutoffTwoPulledMatrixEntryTolerance_pos hmatrix)
        (Nat.le_trans hmatrixAnchor hfirst)
        (Nat.le_trans hmatrixAnchor hlater)
      weightEntry := cutoffTwoPulledWeightEntryErrorAt_of_anchor
        (cutoffTwoPulledWeightEntryTolerance_pos hdiagonal)
        (Nat.le_trans hweightAnchor hfirst)
        (Nat.le_trans hweightAnchor hlater)
      matrixBudget := cutoffTwoPulledMatrixEntryTolerance_budget hmatrix
      diagonalBudget := cutoffTwoPulledWeightEntryTolerance_budget hdiagonal }

/-! ## 3. Composition with moving recentering -/

private theorem abs_sub_via_common_le
    {left common right leftError rightError : Q'}
    (hleft : Q'.abs (left + (-common)) ≤ leftError)
    (hright : Q'.abs (common + (-right)) ≤ rightError) :
    Q'.abs (left + (-right)) ≤ leftError + rightError := by
  have hdecompose : left + (-right) ≈
      (left + (-common)) + (common + (-right)) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv left (-common) (common + (-right))) ?_
    refine Q'.add_eqv_congr_left left _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-common) common (-right))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((-common) + common) 0 (-right)
        (Q'.neg_add_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.le_trans' _ _ _
      (Q'.abs_add_le' (left + (-common)) (common + (-right)))
      (Q'.add_le_add hleft hright))

private theorem relative_diagonal_inflation_of_abs_sub_le
    {firstDiagonal laterDiagonal relativeError : Q'}
    (herror : Q'.abs (firstDiagonal + (-laterDiagonal)) ≤
      relativeError * laterDiagonal) :
    firstDiagonal ≤ ((1 : Q') + relativeError) * laterDiagonal := by
  have hadd : firstDiagonal ≤
      laterDiagonal + relativeError * laterDiagonal :=
    ExpNeg.le_add_of_abs_sub_le herror
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((1 : Q') * laterDiagonal + relativeError * laterDiagonal) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.one_mul_eqv laterDiagonal)))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (1 : Q') relativeError laterDiagonal))))

/-- Entrywise law drift at a fixed first-centered coefficient and same-law
recentring at the later cutoff compose into a bound for the actual moving
matrix forms.  The diagonal recentering estimate supplies the only norm
inflation, namely `1 + recenteringError`. -/
theorem moving_matrix_error_of_law_and_recentering
    {first later : Nat}
    {matrixLawError diagonalLawError recenteringError : Q'}
    (hmatrixLaw : (0 : Q') ≤ matrixLawError)
    (lawError : CutoffTwoPulledRelativeLawErrorAt
      first later matrixLawError diagonalLawError)
    (coefficient : Nat → Q')
    (hrecenterMatrix :
      Q'.abs
          (cutoffTwoPulledMatrixAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
            (-cutoffTwoPulledMatrixAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
        recenteringError *
          cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))
    (hrecenterDiagonal :
      Q'.abs
          (cutoffTwoPulledDiagonalAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
            (-cutoffTwoPulledDiagonalAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
        recenteringError *
          cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) :
    Q'.abs
        (cutoffTwoPulledMatrixAt first
            (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
          (-cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
      (matrixLawError * ((1 : Q') + recenteringError) +
          recenteringError) *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let firstCoefficient :=
    cutoffTwoPulledMovingCenteredCoefficientAt first coefficient
  let laterCoefficient :=
    cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let firstLaterDiagonal :=
    cutoffTwoPulledDiagonalAt later firstCoefficient
  let laterDiagonal := cutoffTwoPulledDiagonalAt later laterCoefficient
  have hdiagonalInflation : firstLaterDiagonal ≤
      ((1 : Q') + recenteringError) * laterDiagonal :=
    relative_diagonal_inflation_of_abs_sub_le hrecenterDiagonal
  have hlaw := lawError.matrix_error firstCoefficient
  have hscaledDiagonal : matrixLawError * firstLaterDiagonal ≤
      matrixLawError * (((1 : Q') + recenteringError) * laterDiagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalInflation hmatrixLaw
  have hlawRelative :
      Q'.abs
          (cutoffTwoPulledMatrixAt first firstCoefficient +
            (-cutoffTwoPulledMatrixAt later firstCoefficient)) ≤
        (matrixLawError * ((1 : Q') + recenteringError)) *
          laterDiagonal := by
    exact Q'.le_trans' _ _ _ hlaw
      (Q'.le_trans' _ _ _ hscaledDiagonal
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv matrixLawError
              ((1 : Q') + recenteringError) laterDiagonal))))
  have htriangle := abs_sub_via_common_le
    hlawRelative hrecenterMatrix
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (matrixLawError * ((1 : Q') + recenteringError))
          recenteringError laterDiagonal)))

/-- The identical composition for the moving diagonal forms. -/
theorem moving_diagonal_error_of_law_and_recentering
    {first later : Nat}
    {matrixLawError diagonalLawError recenteringError : Q'}
    (hdiagonalLaw : (0 : Q') ≤ diagonalLawError)
    (lawError : CutoffTwoPulledRelativeLawErrorAt
      first later matrixLawError diagonalLawError)
    (coefficient : Nat → Q')
    (hrecenterDiagonal :
      Q'.abs
          (cutoffTwoPulledDiagonalAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
            (-cutoffTwoPulledDiagonalAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
        recenteringError *
          cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) :
    Q'.abs
        (cutoffTwoPulledDiagonalAt first
            (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
          (-cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
      (diagonalLawError * ((1 : Q') + recenteringError) +
          recenteringError) *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let firstCoefficient :=
    cutoffTwoPulledMovingCenteredCoefficientAt first coefficient
  let laterCoefficient :=
    cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let firstLaterDiagonal :=
    cutoffTwoPulledDiagonalAt later firstCoefficient
  let laterDiagonal := cutoffTwoPulledDiagonalAt later laterCoefficient
  have hdiagonalInflation : firstLaterDiagonal ≤
      ((1 : Q') + recenteringError) * laterDiagonal :=
    relative_diagonal_inflation_of_abs_sub_le hrecenterDiagonal
  have hlaw := lawError.diagonal_error firstCoefficient
  have hscaledDiagonal : diagonalLawError * firstLaterDiagonal ≤
      diagonalLawError * (((1 : Q') + recenteringError) * laterDiagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalInflation hdiagonalLaw
  have hlawRelative :
      Q'.abs
          (cutoffTwoPulledDiagonalAt first firstCoefficient +
            (-cutoffTwoPulledDiagonalAt later firstCoefficient)) ≤
        (diagonalLawError * ((1 : Q') + recenteringError)) *
          laterDiagonal := by
    exact Q'.le_trans' _ _ _ hlaw
      (Q'.le_trans' _ _ _ hscaledDiagonal
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv diagonalLawError
              ((1 : Q') + recenteringError) laterDiagonal))))
  have htriangle := abs_sub_via_common_le
    hlawRelative hrecenterDiagonal
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (diagonalLawError * ((1 : Q') + recenteringError))
          recenteringError laterDiagonal)))

/-! ## 4. Full moving-form tail theorem -/

/-- For arbitrary positive component budgets, every coefficient has a
cofinal tail on which the actual moving matrix and diagonal forms are
relatively stable.  The total error formula records the causal composition:
law drift times the recentering norm inflation, plus recentering drift. -/
theorem movingForm_relative_errors_cofinally
    (coefficient : Nat → Q')
    (matrixLawError diagonalLawError recenteringError : Q')
    (hmatrixLaw : (0 : Q') < matrixLawError)
    (hdiagonalLaw : (0 : Q') < diagonalLawError)
    (hrecentering : (0 : Q') < recenteringError) :
    ∃ cutoff : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ cutoff ∧
      ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt first
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            (matrixLawError * ((1 : Q') + recenteringError) +
                recenteringError) *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt first
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            (diagonalLawError * ((1 : Q') + recenteringError) +
                recenteringError) *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  obtain ⟨recenteringCutoff, hrecenterFloor, hrecenter⟩ :=
    sameLaw_relative_errors_for_every_coefficient
      coefficient recenteringError hrecentering
  let lawCutoff := cutoffTwoPulledRelativeLawErrorAnchor
    matrixLawError diagonalLawError
  refine ⟨max lawCutoff recenteringCutoff,
    Nat.le_trans hrecenterFloor (Nat.le_max_right _ _), ?_⟩
  intro first later hfirst hlater
  have hlawFirst : lawCutoff ≤ first :=
    Nat.le_trans (Nat.le_max_left _ _) hfirst
  have hlawLater : lawCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hrecenterFirst : recenteringCutoff ≤ first :=
    Nat.le_trans (Nat.le_max_right _ _) hfirst
  have hrecenterLater : recenteringCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  let lawError := cutoffTwoPulledRelativeLawErrors_cofinally
    matrixLawError diagonalLawError hmatrixLaw hdiagonalLaw
    first later hlawFirst hlawLater
  have hrecentered := hrecenter first later
    hrecenterFirst hrecenterLater
  exact
    ⟨moving_matrix_error_of_law_and_recentering
        (Q'.le_of_lt hmatrixLaw) lawError coefficient
        hrecentered.1 hrecentered.2,
      moving_diagonal_error_of_law_and_recentering
        (Q'.le_of_lt hdiagonalLaw) lawError coefficient
        hrecentered.2⟩

/-! ## 5. One requested total relative error -/

private theorem component_amplification_eqv (component : Q') :
    component * ((1 : Q') + component) + component ≈
      component * (component + ((1 : Q') + 1)) := by
  refine Q'.eqv_trans _
    (component * ((1 : Q') + component) + component * 1) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv component))
  refine Q'.eqv_trans _
    (component * (((1 : Q') + component) + 1)) _
    (Q'.eqv_symm
      (Q'.mul_add_eqv component ((1 : Q') + component) 1)) ?_
  refine Q'.mul_eqv_congr_left component _ _ ?_
  refine Q'.eqv_trans _ ((component + 1) + 1) _
    (Q'.add_eqv_congr_right _ _ 1
      (Q'.add_comm_eqv (1 : Q') component)) ?_
  exact Q'.add_assoc_eqv component 1 1

/-- A single positive component budget whose composed law-plus-recentering
amplification fits below the requested total relative error. -/
def cutoffTwoPulledMovingFormComponentError
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) : Q' :=
  Q'.divPos relativeError
    (relativeError + ((1 : Q') + 1))
    (Q'.add_pos hrelative (by decide))

theorem cutoffTwoPulledMovingFormComponentError_pos
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) :
    (0 : Q') <
      cutoffTwoPulledMovingFormComponentError relativeError hrelative := by
  unfold cutoffTwoPulledMovingFormComponentError
  exact Q'.divPos_pos _ _ _ hrelative

theorem cutoffTwoPulledMovingFormComponentError_amplification_le
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) :
    let component :=
      cutoffTwoPulledMovingFormComponentError relativeError hrelative
    component * ((1 : Q') + component) + component ≤ relativeError := by
  intro component
  let two : Q' := (1 : Q') + 1
  let denominator := relativeError + two
  have hrelative0 : (0 : Q') ≤ relativeError := Q'.le_of_lt hrelative
  have hcomponentPos : (0 : Q') < component :=
    cutoffTwoPulledMovingFormComponentError_pos relativeError hrelative
  have hcomponent0 : (0 : Q') ≤ component := Q'.le_of_lt hcomponentPos
  have htwoLeDenominator : two ≤ denominator := by
    have hadd := Q'.add_le_add_right
      (0 : Q') relativeError two hrelative0
    simpa only [Q'.zero_add'] using hadd
  have honeLeDenominator : (1 : Q') ≤ denominator :=
    Q'.le_trans' _ two _ (by decide) htwoLeDenominator
  have hcomponentLeProduct : component ≤ component * denominator := by
    refine Q'.le_trans' _ (component * 1) _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv component))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      honeLeDenominator hcomponent0
  have hcollapse : component * denominator ≈ relativeError := by
    unfold component cutoffTwoPulledMovingFormComponentError denominator two
    exact Q'.divPos_mul_eqv _ _ _
  have hcomponentLeRelative : component ≤ relativeError :=
    Q'.le_trans' _ _ _ hcomponentLeProduct (Q'.le_of_eqv hcollapse)
  have hfactor : component + two ≤ relativeError + two :=
    Q'.add_le_add_right _ _ two hcomponentLeRelative
  have hscaled : component * (component + two) ≤
      component * (relativeError + two) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfactor hcomponent0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (component_amplification_eqv component))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse))

/-- Full moving-form tail stability with one arbitrarily prescribed positive
relative error.  This is the strongest tail statement: both the cutoff law
and the centered coefficient move, and both matrix and diagonal differences
are controlled by the same later physical diagonal. -/
theorem movingForm_relative_errors_for_every_positive
    (coefficient : Nat → Q')
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) :
    ∃ cutoff : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ cutoff ∧
      ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt first
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt first
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  let component :=
    cutoffTwoPulledMovingFormComponentError relativeError hrelative
  have hcomponent : (0 : Q') < component :=
    cutoffTwoPulledMovingFormComponentError_pos relativeError hrelative
  obtain ⟨cutoff, hfloor, htail⟩ :=
    movingForm_relative_errors_cofinally coefficient
      component component component hcomponent hcomponent hcomponent
  refine ⟨cutoff, hfloor, ?_⟩
  intro first later hfirst hlater
  have hpair := htail first later hfirst hlater
  let diagonal := cutoffTwoPulledDiagonalAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  have hdiagonal : (0 : Q') ≤ diagonal :=
    cutoffTwoPulledDiagonalAt_nonnegative later _
  have hamplification :
      component * ((1 : Q') + component) + component ≤ relativeError :=
    cutoffTwoPulledMovingFormComponentError_amplification_le
      relativeError hrelative
  have hscaled :
      (component * ((1 : Q') + component) + component) * diagonal ≤
        relativeError * diagonal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hamplification hdiagonal
  exact
    ⟨Q'.le_trans' _ _ _ hpair.1 hscaled,
      Q'.le_trans' _ _ _ hpair.2 hscaled⟩

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.cutoffTwoPulledKernelEntryErrorAt_of_anchor
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.cutoffTwoPulledWeightEntryErrorAt_of_anchor
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.cutoffTwoPulledRelativeLawErrors_cofinally
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.moving_matrix_error_of_law_and_recentering
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.moving_diagonal_error_of_law_and_recentering
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.movingForm_relative_errors_cofinally
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.cutoffTwoPulledMovingFormComponentError_amplification_le
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.movingForm_relative_errors_for_every_positive
