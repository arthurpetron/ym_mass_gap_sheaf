/-
# Adaptive stage for the weighted bulk-source mean scaling defect

The pairwise source action-scaling kernel already has a constructive Heron
modulus after fixing a finite cutoff and row pair.  This file performs the
first actual carrier lift: it identifies the heat `A2` row-square list with
its explicit finite source-index map, aggregates the nonnegative diagonal
pair coefficients with the positive source weights, and chooses one stage
which controls the complete one-point common-action scaling defect.

The stage may depend on the cutoff, source side, history time, and tolerance.
No connected two-source contraction, cutoff-uniform rate, neighboring-time
sign, ORIGINAL-law comparison, continuum Hamiltonian, or Clay mass gap is
proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem abs_listQSum_le_sum_abs_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    Q'.abs (listQSum value items) ≤
      listQSum (fun item => Q'.abs (value item)) items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add
          (Q'.le_refl' (Q'.abs (value head)))
          (abs_listQSum_le_sum_abs_local value tail))

private theorem listQSum_mono_local {Index : Type}
    (lower upper : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hypothesis =>
      Q'.add_le_add
        (hypothesis head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item membership =>
            hypothesis item (List.mem_cons_of_mem head membership)))

private theorem weightedGeoTailSum_eqv {Index : Type}
    (weight coefficient : Index → Q') (stage : Nat) : ∀ items : List Index,
    listQSum (fun item => weight item * geoTail (coefficient item) stage)
        items ≈
      geoTail
        (listQSum (fun item => weight item * coefficient item) items)
        stage
  | [] => by
      unfold geoTail listQSum
      exact Q'.eqv_symm (Q'.zero_mul_eqv (HalfPow.half ^ stage))
  | head :: tail => by
      unfold listQSum
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
            (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 2))
            (by decide) (fun
              | 0 => weight head
              | 1 => coefficient head
              | _ => HalfPow.half ^ stage))
          (weightedGeoTailSum_eqv weight coefficient stage tail)) ?_
      unfold geoTail
      exact poly_identity_of_normal_eq
        (.add
          (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 3))
          (.mul (.mul (.const 2) (.var 2)) (.var 3)))
        (.mul
          (.mul (.const 2) (.add (.mul (.var 0) (.var 1)) (.var 2)))
          (.var 3))
        (by decide) (fun
          | 0 => weight head
          | 1 => coefficient head
          | 2 => listQSum
              (fun item => weight item * coefficient item) tail
          | _ => HalfPow.half ^ stage)

/-- The public heat `A2` row-square carrier is the explicit map over source
color-row indices. -/
theorem openCubeHeatCayleyTraceA2RowSquares_eq_explicit
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    openCubeHeatCayleyTraceA2RowSquares
        timeBonds side sidePositive stage time =
      (List.range (3 * (bulkSourceFaces side).length)).map fun rowIndex =>
        { weight := (4 : Q') *
            bulkSourceIndexWeight side sidePositive (rowIndex / 3)
          row := bulkSourceHeatHeronColorCurlRow
            timeBonds side stage time rowIndex } := by
  unfold openCubeHeatCayleyTraceA2RowSquares
  change
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time).map
        (fun block : WeightedQuadraticRowBlock =>
          ({ weight := block.weight, row := block.first } :
            WeightedRowSquare)) = _
  simp only [List.map_map,
    openCubeHeatBulkCayleyTraceA2RowBlocks,
    bulkSourceHeatQuadraticRowBlocks]
  apply List.map_congr_left
  intro rowIndex _hrowIndex
  rfl

/-- Stage-independent aggregate coefficient for the complete weighted
one-point source scaling contraction. -/
def bulkSourceHeatMeanScalingTotalCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side) (time : Nat) : Q' :=
  listQSum
    (fun rowIndex =>
      ((4 : Q') *
          bulkSourceIndexWeight side sidePositive (rowIndex / 3)) *
        bulkSourceHeatActionScalingTotalCoefficient
          timeBonds side time time rowIndex rowIndex)
    (List.range (3 * (bulkSourceFaces side).length))

theorem bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side) (time : Nat) :
    (0 : Q') ≤
      bulkSourceHeatMeanScalingTotalCoefficient
        timeBonds side sidePositive time := by
  unfold bulkSourceHeatMeanScalingTotalCoefficient
  apply listQSum_nonnegative_on
  intro rowIndex hrowIndex
  have hfaceIndex : rowIndex / 3 < (bulkSourceFaces side).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rw [Nat.mul_comm]
    exact List.mem_range.mp hrowIndex
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt
        (bulkSourceIndexWeight_pos sidePositive hfaceIndex)))
    (bulkSourceHeatActionScalingTotalCoefficient_nonnegative
      timeBonds side time time rowIndex rowIndex)

/-- One constructive stage for the complete weighted one-point source
scaling contraction at a fixed finite cutoff. -/
def bulkSourceHeatMeanScalingAdaptiveStage
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (time : Nat) (epsilon : Q') : Nat :=
  geoOuterModulus
    (bulkSourceHeatMeanScalingTotalCoefficient
      timeBonds side sidePositive time)
    epsilon

/-- The actual complete one-point common-action scaling residual is bounded
by its aggregate geometric tail at every Heron stage. -/
theorem openCubeHeatCayleyTraceMeanScalingResidualContraction_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    Q'.abs
        (openCubeHeatCayleyTraceMeanScalingResidualContraction
          timeBonds side sidePositive stage time) ≤
      geoTail
        (bulkSourceHeatMeanScalingTotalCoefficient
          timeBonds side sidePositive time)
        stage := by
  let rows := List.range (3 * (bulkSourceFaces side).length)
  let weight := fun rowIndex : Nat =>
    (4 : Q') * bulkSourceIndexWeight side sidePositive (rowIndex / 3)
  let coefficient := fun rowIndex : Nat =>
    bulkSourceHeatActionScalingTotalCoefficient
      timeBonds side time time rowIndex rowIndex
  let kernel := fun rowIndex : Nat =>
    finiteGaussianWeightedActionScalingKernel
      (bulkSourceNoiseCount timeBonds side)
      (completeOpenCubeHeatGaussianActionRowSquares
        timeBonds (bulkSourceWidth side) stage)
      (bulkSourceHeatHeronColorCurlRow
        timeBonds side stage time rowIndex)
      (bulkSourceHeatHeronColorCurlRow
        timeBonds side stage time rowIndex)
  have hrowSquares := openCubeHeatCayleyTraceA2RowSquares_eq_explicit
    timeBonds side sidePositive stage time
  unfold openCubeHeatCayleyTraceMeanScalingResidualContraction
    finiteGaussianWeightedMeanScalingResidualContraction
  rw [hrowSquares]
  simp only [List.map_map]
  rw [qListSum_map_eq_listQSum_local]
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local
      (fun rowIndex => weight rowIndex * kernel rowIndex) rows) ?_
  have hterm : ∀ rowIndex, rowIndex ∈ rows →
      Q'.abs (weight rowIndex * kernel rowIndex) ≤
        weight rowIndex * geoTail (coefficient rowIndex) stage := by
    intro rowIndex hrowIndex
    have hfaceIndex : rowIndex / 3 < (bulkSourceFaces side).length := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
      rw [Nat.mul_comm]
      exact List.mem_range.mp hrowIndex
    have hweight : (0 : Q') ≤ weight rowIndex :=
      Q'.mul_nonneg _ _ (by decide)
        (Q'.le_of_lt
          (bulkSourceIndexWeight_pos sidePositive hfaceIndex))
    have hkernel := bulkSourceHeatActionScalingKernel_abs_le_two_order
      timeBonds side stage time time rowIndex rowIndex
    rw [if_pos rfl] at hkernel
    have hfirst := bulkSourceHeatActionScalingFirstOrderCoefficient_nonnegative
      timeBonds side time time rowIndex rowIndex
    have hquadratic := bulkSourceHeatActionScalingQuadraticCoefficient_nonnegative
      timeBonds side time time rowIndex rowIndex
    have henvelope := twoOrderEnvelope_le_geoTail
      (bulkSourceHeatActionScalingFirstOrderCoefficient
        timeBonds side time time rowIndex rowIndex)
      (bulkSourceHeatActionScalingQuadraticCoefficient
        timeBonds side time time rowIndex rowIndex)
      hfirst hquadratic stage
    have habs := ExpNeg.abs_mul_le (weight rowIndex) (kernel rowIndex)
    rw [ExpNeg.abs_of_nonneg hweight] at habs
    exact Q'.le_trans' _ _ _ habs
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_trans' _ _ _ hkernel henvelope) hweight)
  refine Q'.le_trans' _ _ _
    (listQSum_mono_local
      (fun rowIndex => Q'.abs (weight rowIndex * kernel rowIndex))
      (fun rowIndex => weight rowIndex * geoTail (coefficient rowIndex) stage)
      rows hterm) ?_
  refine Q'.le_of_eqv ?_
  exact Q'.eqv_trans _ _ _
    (weightedGeoTailSum_eqv weight coefficient stage rows)
    (Q'.eqv_refl _)

/-- At every later stage, the actual complete one-point common-action scaling
residual of the weighted heat `A2` source is below the supplied tolerance. -/
theorem openCubeHeatCayleyTraceMeanScalingResidualContraction_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatMeanScalingAdaptiveStage
        timeBonds side sidePositive time epsilon ≤ stage) :
    Q'.abs
        (openCubeHeatCayleyTraceMeanScalingResidualContraction
          timeBonds side sidePositive stage time) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceMeanScalingResidualContraction_abs_le_geoTail
      timeBonds side sidePositive stage time) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatMeanScalingTotalCoefficient
      timeBonds side sidePositive time)
    (bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
      timeBonds side sidePositive time)
    epsilon hepsilon stage hstage

/-- The actual corrected one-point common-action Wick defect obeys the same
aggregate geometric-tail bound. -/
theorem openCubeHeatCayleyTraceMeanScalingDefectWickSum_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    Q'.abs
        (openCubeHeatCayleyTraceMeanScalingDefectWickSum
          timeBonds side sidePositive stage time) ≤
      geoTail
        (bulkSourceHeatMeanScalingTotalCoefficient
          timeBonds side sidePositive time)
        stage := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceMeanScalingDefectWickSum_eq_contraction
          timeBonds side sidePositive stage time))) ?_
  exact
    openCubeHeatCayleyTraceMeanScalingResidualContraction_abs_le_geoTail
      timeBonds side sidePositive stage time

/-- The actual corrected one-point common-action Wick defect inherits the
same fixed-cutoff adaptive-stage bound from its exact residual-contraction
identity. -/
theorem openCubeHeatCayleyTraceMeanScalingDefectWickSum_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatMeanScalingAdaptiveStage
        timeBonds side sidePositive time epsilon ≤ stage) :
    Q'.abs
        (openCubeHeatCayleyTraceMeanScalingDefectWickSum
          timeBonds side sidePositive stage time) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceMeanScalingDefectWickSum_abs_le_geoTail
      timeBonds side sidePositive stage time) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatMeanScalingTotalCoefficient
      timeBonds side sidePositive time)
    (bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
      timeBonds side sidePositive time)
    epsilon hepsilon stage hstage

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage.openCubeHeatCayleyTraceA2RowSquares_eq_explicit
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage.bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage.openCubeHeatCayleyTraceMeanScalingResidualContraction_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage.openCubeHeatCayleyTraceMeanScalingDefectWickSum_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage.openCubeHeatCayleyTraceMeanScalingResidualContraction_abs_le_epsilon
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage.openCubeHeatCayleyTraceMeanScalingDefectWickSum_abs_le_epsilon
