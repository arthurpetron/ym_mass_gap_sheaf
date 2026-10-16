/-
# Adaptive stage for the weighted connected bulk-source scaling defect

The pairwise action-scaling kernel and the actual source-row Gram now have
stage-independent finite envelopes.  This file aggregates their product over
the two complete weighted heat `A2` row carriers and applies one constructive
geometric modulus.  The resulting stage controls the actual connected
common-action scaling defect at every later Heron stage.

The stage may depend on the finite cutoff, source side, two history times and
tolerance.  No cutoff-uniform rate, neighboring-time sign, ORIGINAL-law
comparison, continuum Hamiltonian, or Clay mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage

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
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope
open YMGap.Continuum.RegularLinearGeometricModulus

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

private theorem geoTail_add_eqv (left right : Q') (stage : Nat) :
    geoTail left stage + geoTail right stage ≈
      geoTail (left + right) stage := by
  unfold geoTail
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.mul (.const 2) (.var 0)) (.var 2))
      (.mul (.mul (.const 2) (.var 1)) (.var 2)))
    (.mul (.mul (.const 2) (.add (.var 0) (.var 1))) (.var 2))
    (by decide) (fun
      | 0 => left
      | 1 => right
      | _ => HalfPow.half ^ stage)

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
      exact geoTail_add_eqv
        (weight head * coefficient head)
        (listQSum (fun item => weight item * coefficient item) tail)
        stage

private theorem nestedWeightedGeoTailSum_eqv {Left Right : Type}
    (weight coefficient : Left → Right → Q') (stage : Nat)
    (right : List Right) : ∀ left : List Left,
    listQSum
        (fun leftItem => listQSum
          (fun rightItem =>
            weight leftItem rightItem *
              geoTail (coefficient leftItem rightItem) stage)
          right)
        left ≈
      geoTail
        (listQSum
          (fun leftItem => listQSum
            (fun rightItem =>
              weight leftItem rightItem *
                coefficient leftItem rightItem)
            right)
          left)
        stage
  | [] => by
      unfold geoTail listQSum
      exact Q'.eqv_symm (Q'.zero_mul_eqv (HalfPow.half ^ stage))
  | head :: tail => by
      unfold listQSum
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (weightedGeoTailSum_eqv
            (weight head) (coefficient head) stage right)
          (nestedWeightedGeoTailSum_eqv
            weight coefficient stage right tail)) ?_
      exact geoTail_add_eqv
        (listQSum
          (fun rightItem =>
            weight head rightItem * coefficient head rightItem)
          right)
        (listQSum
          (fun leftItem => listQSum
            (fun rightItem =>
              weight leftItem rightItem *
                coefficient leftItem rightItem)
            right)
          tail)
        stage

private theorem abs_connected_term_le
    (leftWeight rightWeight gram kernel gramEnvelope kernelEnvelope : Q')
    (hleftWeight : (0 : Q') ≤ leftWeight)
    (hrightWeight : (0 : Q') ≤ rightWeight)
    (hgramEnvelope : (0 : Q') ≤ gramEnvelope)
    (hgram : Q'.abs gram ≤ gramEnvelope)
    (hkernel : Q'.abs kernel ≤ kernelEnvelope) :
    Q'.abs
        ((leftWeight * rightWeight) * (4 * gram * kernel)) ≤
      ((leftWeight * rightWeight) * (4 * gramEnvelope)) *
        kernelEnvelope := by
  have hweight : (0 : Q') ≤ leftWeight * rightWeight :=
    Q'.mul_nonneg _ _ hleftWeight hrightWeight
  have hfourGram := ExpNeg.abs_mul_le (4 : Q') gram
  rw [ExpNeg.abs_of_nonneg (by decide : (0 : Q') ≤ 4)] at hfourGram
  have hfourEnvelope : (0 : Q') ≤ (4 : Q') * gramEnvelope :=
    Q'.mul_nonneg _ _ (by decide) hgramEnvelope
  have hfourGramBound : Q'.abs ((4 : Q') * gram) ≤
      (4 : Q') * gramEnvelope :=
    Q'.le_trans' _ _ _ hfourGram
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hgram (by decide))
  have hinner := ExpNeg.abs_mul_le ((4 : Q') * gram) kernel
  have hinnerBound : Q'.abs ((4 : Q') * gram * kernel) ≤
      ((4 : Q') * gramEnvelope) * kernelEnvelope :=
    Q'.le_trans' _ _ _ hinner
      (Q'.mul_le_mul_of_nonneg
        hfourGramBound hkernel hfourEnvelope (Q'.abs_nonneg kernel))
  have houter := ExpNeg.abs_mul_le
    (leftWeight * rightWeight) ((4 : Q') * gram * kernel)
  rw [ExpNeg.abs_of_nonneg hweight] at houter
  refine Q'.le_trans' _ _ _ houter
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hinnerBound hweight) ?_)
  exact Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (by decide) (fun
        | 0 => leftWeight * rightWeight
        | 1 => (4 : Q') * gramEnvelope
        | _ => kernelEnvelope))

/-- Pair coefficient used in the complete connected-carrier modulus. -/
def bulkSourceHeatConnectedScalingPairCoefficient
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat)
    (sidePositive : 0 < side) : Q' :=
  let leftWeight := (4 : Q') *
    bulkSourceIndexWeight side sidePositive (leftRowIndex / 3)
  let rightWeight := (4 : Q') *
    bulkSourceIndexWeight side sidePositive (rightRowIndex / 3)
  (leftWeight * rightWeight) *
      (4 * bulkSourceHeatRowGramUniformEnvelope
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex) *
    bulkSourceHeatActionScalingTotalCoefficient
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex

/-- Stage-independent aggregate coefficient for the complete connected
two-source scaling contraction. -/
def bulkSourceHeatConnectedScalingTotalCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) : Q' :=
  let rows := List.range (3 * (bulkSourceFaces side).length)
  listQSum
    (fun leftRowIndex => listQSum
      (fun rightRowIndex =>
        bulkSourceHeatConnectedScalingPairCoefficient
          timeBonds side leftTime rightTime leftRowIndex rightRowIndex
          sidePositive)
      rows)
    rows

theorem bulkSourceHeatConnectedScalingTotalCoefficient_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) :
    (0 : Q') ≤
      bulkSourceHeatConnectedScalingTotalCoefficient
        timeBonds side sidePositive leftTime rightTime := by
  unfold bulkSourceHeatConnectedScalingTotalCoefficient
  dsimp only
  apply listQSum_nonnegative_on
  intro leftRowIndex hleftRowIndex
  apply listQSum_nonnegative_on
  intro rightRowIndex hrightRowIndex
  have hleftFace : leftRowIndex / 3 < (bulkSourceFaces side).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rw [Nat.mul_comm]
    exact List.mem_range.mp hleftRowIndex
  have hrightFace : rightRowIndex / 3 < (bulkSourceFaces side).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rw [Nat.mul_comm]
    exact List.mem_range.mp hrightRowIndex
  unfold bulkSourceHeatConnectedScalingPairCoefficient
  dsimp only
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.le_of_lt
            (bulkSourceIndexWeight_pos sidePositive hleftFace)))
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.le_of_lt
            (bulkSourceIndexWeight_pos sidePositive hrightFace))))
      (Q'.mul_nonneg _ _ (by decide)
        (bulkSourceHeatRowGramUniformEnvelope_nonnegative
          timeBonds side leftTime rightTime
          leftRowIndex rightRowIndex)))
    (bulkSourceHeatActionScalingTotalCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex)

/-- One constructive stage for the complete connected source scaling
contraction at a fixed finite cutoff. -/
def bulkSourceHeatConnectedScalingAdaptiveStage
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (epsilon : Q') : Nat :=
  geoOuterModulus
    (bulkSourceHeatConnectedScalingTotalCoefficient
      timeBonds side sidePositive leftTime rightTime)
    epsilon

/-- The actual complete connected common-action scaling residual contraction
is bounded by its aggregate geometric tail at every Heron stage. -/
theorem openCubeHeatCayleyTraceConnectedScalingResidualContraction_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    Q'.abs
        (openCubeHeatCayleyTraceConnectedScalingResidualContraction
          timeBonds side sidePositive stage leftTime rightTime) ≤
      geoTail
        (bulkSourceHeatConnectedScalingTotalCoefficient
          timeBonds side sidePositive leftTime rightTime)
        stage := by
  let rows := List.range (3 * (bulkSourceFaces side).length)
  let sourceWeight := fun rowIndex : Nat =>
    (4 : Q') * bulkSourceIndexWeight side sidePositive (rowIndex / 3)
  let sourceRow := fun time rowIndex =>
    bulkSourceHeatHeronColorCurlRow
      timeBonds side stage time rowIndex
  let gram := fun leftRowIndex rightRowIndex =>
    finiteRowGram
      (bulkSourceNoiseCount timeBonds side)
      (sourceRow leftTime leftRowIndex)
      (sourceRow rightTime rightRowIndex)
  let kernel := fun leftRowIndex rightRowIndex =>
    finiteGaussianWeightedActionScalingKernel
      (bulkSourceNoiseCount timeBonds side)
      (completeOpenCubeHeatGaussianActionRowSquares
        timeBonds (bulkSourceWidth side) stage)
      (sourceRow leftTime leftRowIndex)
      (sourceRow rightTime rightRowIndex)
  let gramEnvelope := fun leftRowIndex rightRowIndex =>
    bulkSourceHeatRowGramUniformEnvelope
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  let coefficient := fun leftRowIndex rightRowIndex =>
    bulkSourceHeatActionScalingTotalCoefficient
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  let pairScale := fun leftRowIndex rightRowIndex =>
    (sourceWeight leftRowIndex * sourceWeight rightRowIndex) *
      (4 * gramEnvelope leftRowIndex rightRowIndex)
  have hleftRows := openCubeHeatCayleyTraceA2RowSquares_eq_explicit
    timeBonds side sidePositive stage leftTime
  have hrightRows := openCubeHeatCayleyTraceA2RowSquares_eq_explicit
    timeBonds side sidePositive stage rightTime
  unfold openCubeHeatCayleyTraceConnectedScalingResidualContraction
    finiteGaussianWeightedConnectedScalingResidualContraction
  rw [hleftRows, hrightRows]
  simp only [List.map_map, qListSum_map_eq_listQSum_local]
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local
      (fun leftRowIndex => listQSum
        (fun rightRowIndex =>
          (sourceWeight leftRowIndex * sourceWeight rightRowIndex) *
            (4 * gram leftRowIndex rightRowIndex *
              kernel leftRowIndex rightRowIndex))
        rows)
      rows) ?_
  refine Q'.le_trans' _ _ _
    (listQSum_mono_local
      (fun leftRowIndex => Q'.abs (listQSum
        (fun rightRowIndex =>
          (sourceWeight leftRowIndex * sourceWeight rightRowIndex) *
            (4 * gram leftRowIndex rightRowIndex *
              kernel leftRowIndex rightRowIndex))
        rows))
      (fun leftRowIndex => listQSum
        (fun rightRowIndex => Q'.abs
          ((sourceWeight leftRowIndex * sourceWeight rightRowIndex) *
            (4 * gram leftRowIndex rightRowIndex *
              kernel leftRowIndex rightRowIndex)))
        rows)
      rows
      (fun leftRowIndex _ =>
        abs_listQSum_le_sum_abs_local
          (fun rightRowIndex =>
            (sourceWeight leftRowIndex * sourceWeight rightRowIndex) *
              (4 * gram leftRowIndex rightRowIndex *
                kernel leftRowIndex rightRowIndex))
          rows)) ?_
  have hterm : ∀ leftRowIndex, leftRowIndex ∈ rows →
      ∀ rightRowIndex, rightRowIndex ∈ rows →
      Q'.abs
          ((sourceWeight leftRowIndex * sourceWeight rightRowIndex) *
            (4 * gram leftRowIndex rightRowIndex *
              kernel leftRowIndex rightRowIndex)) ≤
        pairScale leftRowIndex rightRowIndex *
          geoTail (coefficient leftRowIndex rightRowIndex) stage := by
    intro leftRowIndex hleftRowIndex rightRowIndex hrightRowIndex
    have hleftFace : leftRowIndex / 3 < (bulkSourceFaces side).length := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
      rw [Nat.mul_comm]
      exact List.mem_range.mp hleftRowIndex
    have hrightFace : rightRowIndex / 3 < (bulkSourceFaces side).length := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
      rw [Nat.mul_comm]
      exact List.mem_range.mp hrightRowIndex
    have hleftWeight : (0 : Q') ≤ sourceWeight leftRowIndex :=
      Q'.mul_nonneg _ _ (by decide)
        (Q'.le_of_lt
          (bulkSourceIndexWeight_pos sidePositive hleftFace))
    have hrightWeight : (0 : Q') ≤ sourceWeight rightRowIndex :=
      Q'.mul_nonneg _ _ (by decide)
        (Q'.le_of_lt
          (bulkSourceIndexWeight_pos sidePositive hrightFace))
    have hgramEnvelope : (0 : Q') ≤
        gramEnvelope leftRowIndex rightRowIndex :=
      bulkSourceHeatRowGramUniformEnvelope_nonnegative
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex
    have hcoefficientPair : (0 : Q') ≤
        coefficient leftRowIndex rightRowIndex :=
      bulkSourceHeatActionScalingTotalCoefficient_nonnegative
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex
    have hgeoTail : (0 : Q') ≤
        geoTail (coefficient leftRowIndex rightRowIndex) stage := by
      unfold geoTail
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hcoefficientPair)
        (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg stage)
    have hgramIf :=
      bulkSourceHeatHeronColorCurlRow_gram_abs_le_uniformEnvelope
        timeBonds side stage leftTime rightTime
        leftRowIndex rightRowIndex
    have hkernelIf := bulkSourceHeatActionScalingKernel_abs_le_two_order
      timeBonds side stage leftTime rightTime
      leftRowIndex rightRowIndex
    have hfirst := bulkSourceHeatActionScalingFirstOrderCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
    have hquadratic := bulkSourceHeatActionScalingQuadraticCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
    have henvelope := twoOrderEnvelope_le_geoTail
      (bulkSourceHeatActionScalingFirstOrderCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex)
      (bulkSourceHeatActionScalingQuadraticCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex)
      hfirst hquadratic stage
    have hgram : Q'.abs (gram leftRowIndex rightRowIndex) ≤
        gramEnvelope leftRowIndex rightRowIndex := by
      by_cases hcomponent : leftRowIndex % 3 = rightRowIndex % 3
      · simpa only [if_pos hcomponent] using hgramIf
      · refine Q'.le_trans' _ _ _
          (by simpa only [if_neg hcomponent] using hgramIf) ?_
        exact hgramEnvelope
    have hkernel : Q'.abs (kernel leftRowIndex rightRowIndex) ≤
        geoTail (coefficient leftRowIndex rightRowIndex) stage := by
      by_cases hcomponent : leftRowIndex % 3 = rightRowIndex % 3
      · exact Q'.le_trans' _ _ _
          (by simpa only [if_pos hcomponent] using hkernelIf)
          henvelope
      · refine Q'.le_trans' _ _ _
          (by simpa only [if_neg hcomponent] using hkernelIf) ?_
        exact hgeoTail
    exact abs_connected_term_le
      (sourceWeight leftRowIndex) (sourceWeight rightRowIndex)
      (gram leftRowIndex rightRowIndex)
      (kernel leftRowIndex rightRowIndex)
      (gramEnvelope leftRowIndex rightRowIndex)
      (geoTail (coefficient leftRowIndex rightRowIndex) stage)
      hleftWeight hrightWeight hgramEnvelope hgram hkernel
  refine Q'.le_trans' _ _ _
    (listQSum_mono_local
      (fun leftRowIndex => listQSum
        (fun rightRowIndex => Q'.abs
          ((sourceWeight leftRowIndex * sourceWeight rightRowIndex) *
            (4 * gram leftRowIndex rightRowIndex *
              kernel leftRowIndex rightRowIndex)))
        rows)
      (fun leftRowIndex => listQSum
        (fun rightRowIndex =>
          pairScale leftRowIndex rightRowIndex *
            geoTail (coefficient leftRowIndex rightRowIndex) stage)
        rows)
      rows
      (fun leftRowIndex hleftRowIndex =>
        listQSum_mono_local _ _ rows
          (hterm leftRowIndex hleftRowIndex))) ?_
  refine Q'.le_of_eqv ?_
  exact Q'.eqv_trans _ _ _
    (nestedWeightedGeoTailSum_eqv
      pairScale coefficient stage rows rows)
    (Q'.eqv_refl _)

/-- At every later stage, the actual complete connected common-action
scaling residual contraction is below the supplied tolerance. -/
theorem openCubeHeatCayleyTraceConnectedScalingResidualContraction_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatConnectedScalingAdaptiveStage
        timeBonds side sidePositive leftTime rightTime epsilon ≤ stage) :
    Q'.abs
        (openCubeHeatCayleyTraceConnectedScalingResidualContraction
          timeBonds side sidePositive stage leftTime rightTime) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceConnectedScalingResidualContraction_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatConnectedScalingTotalCoefficient
      timeBonds side sidePositive leftTime rightTime)
    (bulkSourceHeatConnectedScalingTotalCoefficient_nonnegative
      timeBonds side sidePositive leftTime rightTime)
    epsilon hepsilon stage hstage

/-- The actual corrected connected common-action Wick defect obeys the same
aggregate geometric-tail bound. -/
theorem openCubeHeatCayleyTraceConnectedScalingDefectWickSum_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    Q'.abs
        (openCubeHeatCayleyTraceConnectedScalingDefectWickSum
          timeBonds side sidePositive stage leftTime rightTime) ≤
      geoTail
        (bulkSourceHeatConnectedScalingTotalCoefficient
          timeBonds side sidePositive leftTime rightTime)
        stage := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceConnectedScalingDefectWickSum_eq_contraction
          timeBonds side sidePositive stage leftTime rightTime))) ?_
  exact
    openCubeHeatCayleyTraceConnectedScalingResidualContraction_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime

/-- The actual corrected connected common-action Wick defect inherits the
same fixed-cutoff adaptive-stage bound from its exact residual-contraction
identity. -/
theorem openCubeHeatCayleyTraceConnectedScalingDefectWickSum_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatConnectedScalingAdaptiveStage
        timeBonds side sidePositive leftTime rightTime epsilon ≤ stage) :
    Q'.abs
        (openCubeHeatCayleyTraceConnectedScalingDefectWickSum
          timeBonds side sidePositive stage leftTime rightTime) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceConnectedScalingDefectWickSum_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatConnectedScalingTotalCoefficient
      timeBonds side sidePositive leftTime rightTime)
    (bulkSourceHeatConnectedScalingTotalCoefficient_nonnegative
      timeBonds side sidePositive leftTime rightTime)
    epsilon hepsilon stage hstage

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage.bulkSourceHeatConnectedScalingTotalCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage.openCubeHeatCayleyTraceConnectedScalingResidualContraction_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage.openCubeHeatCayleyTraceConnectedScalingDefectWickSum_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage.openCubeHeatCayleyTraceConnectedScalingResidualContraction_abs_le_epsilon
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage.openCubeHeatCayleyTraceConnectedScalingDefectWickSum_abs_le_epsilon
