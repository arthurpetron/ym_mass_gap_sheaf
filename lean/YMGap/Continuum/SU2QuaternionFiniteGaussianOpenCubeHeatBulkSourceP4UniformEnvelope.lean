/-
# Stage-independent envelope for corrected OLD-centered P4

The denominator-cleared `P6/P4` approximation error carries one factor of
`P4` from the opposite response slot.  This file constructs a finite
stage-independent envelope for that factor.  It bounds the connected `R4`
Wick double sum using the stage-uniform source-row Gram envelope and bounds
the two OLD-centered mean factors using the complete `A2` mean envelopes.

The result is fixed-cutoff and may grow with the cutoff, source side, times
and supplied OLD center.  It proves no denominator positivity, neighboring-
time sign, ORIGINAL-law comparison, continuum Hamiltonian, or Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnEvenDensityCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_congr_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
      qListSum (items.map left) ≈ qListSum (items.map right)
  | [], _ => Q'.eqv_refl _
  | head :: tail, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis head List.mem_cons_self)
        (qListSum_congr_local left right tail
          (fun item membership =>
            hypothesis item (List.mem_cons_of_mem head membership)))

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

private theorem add_nonnegative_local (left right : Q')
    (hleft : (0 : Q') ≤ left) (hright : (0 : Q') ≤ right) :
    (0 : Q') ≤ left + right :=
  Q'.le_trans' _ _ _ hleft
    (Q'.add_le_self_of_nonneg left right hright)

private theorem weightedRowSquareCovarianceWickSum_reduction_local
    (noiseCount : Nat) (left right : List WeightedRowSquare) :
    finiteGaussianWeightedTwoTwoCovarianceWickSum noiseCount
        (left.map weightedRowSquareQuadraticBlock)
        (right.map weightedRowSquareQuadraticBlock) ≈
      qListSum (left.map fun leftTerm =>
        qListSum (right.map fun rightTerm =>
          (leftTerm.weight * rightTerm.weight) *
            (2 * (finiteRowGram noiseCount leftTerm.row rightTerm.row *
              finiteRowGram noiseCount leftTerm.row rightTerm.row)))) := by
  unfold finiteGaussianWeightedTwoTwoCovarianceWickSum
    weightedRowSquareQuadraticBlock
  simp only [List.map_map]
  apply qListSum_congr_local
  intro leftTerm _leftMembership
  apply qListSum_congr_local
  intro rightTerm _rightMembership
  exact Q'.mul_eqv_congr_left _ _ _
    (finiteGaussianTwoTwoCovarianceWickReduction_row_squares
      noiseCount leftTerm.row rightTerm.row)

private theorem abs_weighted_gram_square_le
    (weight gram envelope : Q')
    (hweight : (0 : Q') ≤ weight)
    (henvelope : (0 : Q') ≤ envelope)
    (hgram : Q'.abs gram ≤ envelope) :
    Q'.abs (weight * (2 * (gram * gram))) ≤
      weight * (2 * (envelope * envelope)) := by
  have hsquare := ExpNeg.abs_mul_le gram gram
  have hsquareBound : Q'.abs (gram * gram) ≤ envelope * envelope :=
    Q'.le_trans' _ _ _ hsquare
      (Q'.mul_le_mul_of_nonneg hgram hgram henvelope
        (Q'.abs_nonneg gram))
  have hdouble := ExpNeg.abs_mul_le (2 : Q') (gram * gram)
  rw [ExpNeg.abs_of_nonneg (by decide : (0 : Q') ≤ 2)] at hdouble
  have hdoubleBound : Q'.abs ((2 : Q') * (gram * gram)) ≤
      (2 : Q') * (envelope * envelope) :=
    Q'.le_trans' _ _ _ hdouble
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hsquareBound (by decide))
  have houter := ExpNeg.abs_mul_le weight ((2 : Q') * (gram * gram))
  rw [ExpNeg.abs_of_nonneg hweight] at houter
  exact Q'.le_trans' _ _ _ houter
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hdoubleBound hweight)

/-- Stage-independent finite envelope for the complete connected corrected
`R4` Wick sum. -/
def bulkSourceHeatConnectedR4UniformEnvelope
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) : Q' :=
  let rows := List.range (3 * (bulkSourceFaces side).length)
  let weight := fun rowIndex : Nat =>
    (4 : Q') * bulkSourceIndexWeight side sidePositive (rowIndex / 3)
  listQSum
    (fun leftRowIndex => listQSum
      (fun rightRowIndex =>
        (weight leftRowIndex * weight rightRowIndex) *
          (2 *
            (bulkSourceHeatRowGramUniformEnvelope
                timeBonds side leftTime rightTime
                leftRowIndex rightRowIndex *
              bulkSourceHeatRowGramUniformEnvelope
                timeBonds side leftTime rightTime
                leftRowIndex rightRowIndex)))
      rows)
    rows

theorem bulkSourceHeatConnectedR4UniformEnvelope_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) :
    (0 : Q') ≤ bulkSourceHeatConnectedR4UniformEnvelope
      timeBonds side sidePositive leftTime rightTime := by
  unfold bulkSourceHeatConnectedR4UniformEnvelope
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
  have hleftWeight : (0 : Q') ≤
      (4 : Q') * bulkSourceIndexWeight
        side sidePositive (leftRowIndex / 3) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt
        (bulkSourceIndexWeight_pos sidePositive hleftFace))
  have hrightWeight : (0 : Q') ≤
      (4 : Q') * bulkSourceIndexWeight
        side sidePositive (rightRowIndex / 3) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt
        (bulkSourceIndexWeight_pos sidePositive hrightFace))
  have henvelope := bulkSourceHeatRowGramUniformEnvelope_nonnegative
    timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ hleftWeight hrightWeight)
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ henvelope henvelope))

/-- The complete connected corrected `R4` Wick sum is bounded uniformly over
the Heron stage by the explicit finite source-pair envelope. -/
theorem openCubeHeatCayleyTraceConnectedR4WickSum_abs_le_uniformEnvelope
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    Q'.abs
        (openCubeHeatCayleyTraceConnectedR4WickSum
          timeBonds side sidePositive stage leftTime rightTime) ≤
      bulkSourceHeatConnectedR4UniformEnvelope
        timeBonds side sidePositive leftTime rightTime := by
  let rows := List.range (3 * (bulkSourceFaces side).length)
  let weight := fun rowIndex : Nat =>
    (4 : Q') * bulkSourceIndexWeight side sidePositive (rowIndex / 3)
  let row := fun time rowIndex =>
    bulkSourceHeatHeronColorCurlRow
      timeBonds side stage time rowIndex
  let gram := fun leftRowIndex rightRowIndex =>
    finiteRowGram (bulkSourceNoiseCount timeBonds side)
      (row leftTime leftRowIndex) (row rightTime rightRowIndex)
  let envelope := fun leftRowIndex rightRowIndex =>
    bulkSourceHeatRowGramUniformEnvelope
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  have hleftSquares := openCubeHeatCayleyTraceA2RowSquares_eq_explicit
    timeBonds side sidePositive stage leftTime
  have hrightSquares := openCubeHeatCayleyTraceA2RowSquares_eq_explicit
    timeBonds side sidePositive stage rightTime
  have hreduction := weightedRowSquareCovarianceWickSum_reduction_local
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatCayleyTraceA2RowSquares
      timeBonds side sidePositive stage rightTime)
  have hwickRows : openCubeHeatCayleyTraceConnectedR4WickSum
        timeBonds side sidePositive stage leftTime rightTime ≈
      qListSum ((openCubeHeatCayleyTraceA2RowSquares
        timeBonds side sidePositive stage leftTime).map fun leftTerm =>
        qListSum ((openCubeHeatCayleyTraceA2RowSquares
          timeBonds side sidePositive stage rightTime).map fun rightTerm =>
          (leftTerm.weight * rightTerm.weight) *
            (2 * (finiteRowGram (bulkSourceNoiseCount timeBonds side)
              leftTerm.row rightTerm.row *
              finiteRowGram (bulkSourceNoiseCount timeBonds side)
                leftTerm.row rightTerm.row)))) := by
    refine Q'.eqv_trans _ _ _ ?_ hreduction
    unfold openCubeHeatCayleyTraceConnectedR4WickSum
    rw [openCubeHeatCayleyTraceA2RowSquares_map_quadraticBlock
        timeBonds side sidePositive stage leftTime,
      openCubeHeatCayleyTraceA2RowSquares_map_quadraticBlock
        timeBonds side sidePositive stage rightTime]
    exact Q'.eqv_refl _
  rw [hleftSquares, hrightSquares] at hwickRows
  simp only [List.map_map] at hwickRows
  have hwick : openCubeHeatCayleyTraceConnectedR4WickSum
        timeBonds side sidePositive stage leftTime rightTime ≈
      qListSum (rows.map fun leftRowIndex =>
        qListSum (rows.map fun rightRowIndex =>
          (weight leftRowIndex * weight rightRowIndex) *
            (2 * (gram leftRowIndex rightRowIndex *
              gram leftRowIndex rightRowIndex)))) := by
    exact hwickRows
  simp only [qListSum_map_eq_listQSum_local] at hwick
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hwick)) ?_
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local
      (fun leftRowIndex => listQSum
        (fun rightRowIndex =>
          (weight leftRowIndex * weight rightRowIndex) *
            (2 * (gram leftRowIndex rightRowIndex *
              gram leftRowIndex rightRowIndex)))
        rows)
      rows) ?_
  refine Q'.le_trans' _ _ _
    (listQSum_mono_local
      (fun leftRowIndex => Q'.abs (listQSum
        (fun rightRowIndex =>
          (weight leftRowIndex * weight rightRowIndex) *
            (2 * (gram leftRowIndex rightRowIndex *
              gram leftRowIndex rightRowIndex)))
        rows))
      (fun leftRowIndex => listQSum
        (fun rightRowIndex => Q'.abs
          ((weight leftRowIndex * weight rightRowIndex) *
            (2 * (gram leftRowIndex rightRowIndex *
              gram leftRowIndex rightRowIndex))))
        rows)
      rows
      (fun leftRowIndex _ =>
        abs_listQSum_le_sum_abs_local
          (fun rightRowIndex =>
            (weight leftRowIndex * weight rightRowIndex) *
              (2 * (gram leftRowIndex rightRowIndex *
                gram leftRowIndex rightRowIndex)))
          rows)) ?_
  unfold bulkSourceHeatConnectedR4UniformEnvelope
  dsimp only
  apply listQSum_mono_local
  intro leftRowIndex hleftRowIndex
  apply listQSum_mono_local
  intro rightRowIndex hrightRowIndex
  have hleftFace : leftRowIndex / 3 < (bulkSourceFaces side).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rw [Nat.mul_comm]
    exact List.mem_range.mp hleftRowIndex
  have hrightFace : rightRowIndex / 3 < (bulkSourceFaces side).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rw [Nat.mul_comm]
    exact List.mem_range.mp hrightRowIndex
  have hleftWeight : (0 : Q') ≤ weight leftRowIndex :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt
        (bulkSourceIndexWeight_pos sidePositive hleftFace))
  have hrightWeight : (0 : Q') ≤ weight rightRowIndex :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt
        (bulkSourceIndexWeight_pos sidePositive hrightFace))
  have henvelope : (0 : Q') ≤ envelope leftRowIndex rightRowIndex :=
    bulkSourceHeatRowGramUniformEnvelope_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  have hgramIf :=
    bulkSourceHeatHeronColorCurlRow_gram_abs_le_uniformEnvelope
      timeBonds side stage leftTime rightTime
      leftRowIndex rightRowIndex
  have hgram : Q'.abs (gram leftRowIndex rightRowIndex) ≤
      envelope leftRowIndex rightRowIndex := by
    by_cases hcomponent : leftRowIndex % 3 = rightRowIndex % 3
    · simpa only [if_pos hcomponent] using hgramIf
    · refine Q'.le_trans' _ _ _
        (by simpa only [if_neg hcomponent] using hgramIf) henvelope
  exact abs_weighted_gram_square_le
    (weight leftRowIndex * weight rightRowIndex)
    (gram leftRowIndex rightRowIndex)
    (envelope leftRowIndex rightRowIndex)
    (Q'.mul_nonneg _ _ hleftWeight hrightWeight)
    henvelope hgram

/-- Stage-independent finite envelope for the complete corrected
OLD-centered `P4`. -/
def bulkSourceHeatP4UniformEnvelope
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  bulkSourceHeatConnectedR4UniformEnvelope
      timeBonds side sidePositive leftTime rightTime +
    (bulkSourceHeatA2MeanUniformEnvelope
        timeBonds side sidePositive leftTime + Q'.abs oldCenter.c2) *
      (bulkSourceHeatA2MeanUniformEnvelope
        timeBonds side sidePositive rightTime + Q'.abs oldCenter.c2)

theorem bulkSourceHeatP4UniformEnvelope_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter) :
    (0 : Q') ≤ bulkSourceHeatP4UniformEnvelope
      timeBonds side sidePositive leftTime rightTime oldCenter := by
  unfold bulkSourceHeatP4UniformEnvelope
  exact add_nonnegative_local _ _
    (bulkSourceHeatConnectedR4UniformEnvelope_nonnegative
      timeBonds side sidePositive leftTime rightTime)
    (Q'.mul_nonneg _ _
      (add_nonnegative_local _ _
        (bulkSourceHeatA2MeanUniformEnvelope_nonnegative
          timeBonds side sidePositive leftTime)
        (Q'.abs_nonneg oldCenter.c2))
      (add_nonnegative_local _ _
        (bulkSourceHeatA2MeanUniformEnvelope_nonnegative
          timeBonds side sidePositive rightTime)
        (Q'.abs_nonneg oldCenter.c2)))

private theorem mean_center_abs_le
    (mean center envelope : Q')
    (hmean : Q'.abs mean ≤ envelope) :
    Q'.abs (mean - center) ≤ envelope + Q'.abs center := by
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le' mean (-center)) ?_
  exact Q'.add_le_add hmean
    (Q'.le_of_eqv (Q'.abs_neg' center))

/-- The actual complete corrected OLD-centered `P4` is bounded by the finite
stage-independent envelope. -/
theorem openCubeHeatCayleyTraceP4_abs_le_uniformEnvelope
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    Q'.abs
        (openCubeHeatCayleyTraceP4
          timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      bulkSourceHeatP4UniformEnvelope
        timeBonds side sidePositive leftTime rightTime oldCenter := by
  let connected := openCubeHeatCayleyTraceConnectedR4WickSum
    timeBonds side sidePositive stage leftTime rightTime
  let leftMean := openCubeHeatCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeHeatCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage rightTime
  let leftEnvelope := bulkSourceHeatA2MeanUniformEnvelope
    timeBonds side sidePositive leftTime
  let rightEnvelope := bulkSourceHeatA2MeanUniformEnvelope
    timeBonds side sidePositive rightTime
  have hconnected : Q'.abs connected ≤
      bulkSourceHeatConnectedR4UniformEnvelope
        timeBonds side sidePositive leftTime rightTime :=
    openCubeHeatCayleyTraceConnectedR4WickSum_abs_le_uniformEnvelope
      timeBonds side sidePositive stage leftTime rightTime
  have hleftMean : Q'.abs leftMean ≤ leftEnvelope :=
    openCubeHeatCayleyTraceOwnA2MeanGramSum_abs_le_uniformEnvelope
      timeBonds side sidePositive stage leftTime
  have hrightMean : Q'.abs rightMean ≤ rightEnvelope :=
    openCubeHeatCayleyTraceOwnA2MeanGramSum_abs_le_uniformEnvelope
      timeBonds side sidePositive stage rightTime
  have hleftCentered : Q'.abs (leftMean - oldCenter.c2) ≤
      leftEnvelope + Q'.abs oldCenter.c2 :=
    mean_center_abs_le leftMean oldCenter.c2 leftEnvelope hleftMean
  have hrightCentered : Q'.abs (rightMean - oldCenter.c2) ≤
      rightEnvelope + Q'.abs oldCenter.c2 :=
    mean_center_abs_le rightMean oldCenter.c2 rightEnvelope hrightMean
  have hleftFactor : (0 : Q') ≤ leftEnvelope + Q'.abs oldCenter.c2 :=
    add_nonnegative_local _ _
      (bulkSourceHeatA2MeanUniformEnvelope_nonnegative
        timeBonds side sidePositive leftTime)
      (Q'.abs_nonneg oldCenter.c2)
  have hproduct :
      Q'.abs ((leftMean - oldCenter.c2) * (rightMean - oldCenter.c2)) ≤
        (leftEnvelope + Q'.abs oldCenter.c2) *
          (rightEnvelope + Q'.abs oldCenter.c2) := by
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le (leftMean - oldCenter.c2)
        (rightMean - oldCenter.c2)) ?_
    exact Q'.mul_le_mul_of_nonneg
      hleftCentered hrightCentered hleftFactor
      (Q'.abs_nonneg (rightMean - oldCenter.c2))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceP4_complete_wick
          timeBonds side sidePositive stage leftTime rightTime oldCenter))) ?_
  unfold openCubeHeatCayleyTraceP4CompleteWickSum
    bulkSourceHeatP4UniformEnvelope
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le' connected
      ((leftMean - oldCenter.c2) * (rightMean - oldCenter.c2))) ?_
  exact Q'.add_le_add hconnected hproduct

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope.bulkSourceHeatConnectedR4UniformEnvelope_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope.openCubeHeatCayleyTraceConnectedR4WickSum_abs_le_uniformEnvelope
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope.bulkSourceHeatP4UniformEnvelope_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope.openCubeHeatCayleyTraceP4_abs_le_uniformEnvelope
