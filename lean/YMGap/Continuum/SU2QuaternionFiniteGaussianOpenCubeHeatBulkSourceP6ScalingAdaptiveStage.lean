/-
# Adaptive stage for the complete OLD-centered P6 scaling residual

The one-point and connected common-action scaling defects already have
aggregate geometric tails on each fixed finite heat carrier.  This file adds
the missing OLD-centered factors: it constructs stage-independent envelopes
for the two heat `A2` means, combines all three tail coefficients, and applies
one constructive geometric modulus to the complete corrected `P6` scaling
residual.

The stage may depend on the finite cutoff, source side, two history times,
supplied OLD quadratic center and tolerance.  No neighboring-time sign,
ORIGINAL-law center identification, higher-remainder estimate, continuum
Hamiltonian, or Clay mass gap is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage

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
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnMeanWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceConnectedScalingAdaptiveStage
open YMGap.Continuum.RegularLinearGeometricModulus

local infix:50 " ≈ " => Q'.eqv

private theorem add_nonnegative_local (left right : Q')
    (hleft : (0 : Q') ≤ left) (hright : (0 : Q') ≤ right) :
    (0 : Q') ≤ left + right :=
  Q'.le_trans' _ _ _ hleft
    (Q'.add_le_self_of_nonneg left right hright)

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

/-- Stage-independent envelope for the complete weighted heat `A2` mean. -/
def bulkSourceHeatA2MeanUniformEnvelope
    (timeBonds side : Nat) (sidePositive : 0 < side) (time : Nat) : Q' :=
  listQSum
    (fun rowIndex =>
      ((4 : Q') *
          bulkSourceIndexWeight side sidePositive (rowIndex / 3)) *
        bulkSourceHeatRowGramUniformEnvelope
          timeBonds side time time rowIndex rowIndex)
    (List.range (3 * (bulkSourceFaces side).length))

theorem bulkSourceHeatA2MeanUniformEnvelope_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side) (time : Nat) :
    (0 : Q') ≤
      bulkSourceHeatA2MeanUniformEnvelope
        timeBonds side sidePositive time := by
  unfold bulkSourceHeatA2MeanUniformEnvelope
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
    (bulkSourceHeatRowGramUniformEnvelope_nonnegative
      timeBonds side time time rowIndex rowIndex)

/-- The complete corrected quadratic OWN mean is bounded uniformly over the
Heron stage by the explicit finite source-row envelope. -/
theorem openCubeHeatCayleyTraceOwnA2MeanGramSum_abs_le_uniformEnvelope
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    Q'.abs
        (openCubeHeatCayleyTraceOwnA2MeanGramSum
          timeBonds side sidePositive stage time) ≤
      bulkSourceHeatA2MeanUniformEnvelope
        timeBonds side sidePositive time := by
  let rows := List.range (3 * (bulkSourceFaces side).length)
  let weight := fun rowIndex : Nat =>
    (4 : Q') * bulkSourceIndexWeight side sidePositive (rowIndex / 3)
  let row := fun rowIndex : Nat =>
    bulkSourceHeatHeronColorCurlRow
      timeBonds side stage time rowIndex
  let envelope := fun rowIndex : Nat =>
    bulkSourceHeatRowGramUniformEnvelope
      timeBonds side time time rowIndex rowIndex
  unfold openCubeHeatCayleyTraceOwnA2MeanGramSum
    finiteGaussianWeightedQuadraticExpectationGramSum
    openCubeHeatBulkCayleyTraceA2RowBlocks
    bulkSourceHeatQuadraticRowBlocks
    scaleWeightedQuadraticRowBlock
  simp only [List.map_map]
  rw [qListSum_map_eq_listQSum_local]
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local
      (fun rowIndex => weight rowIndex *
        finiteRowGram (bulkSourceNoiseCount timeBonds side)
          (row rowIndex) (row rowIndex))
      rows) ?_
  unfold bulkSourceHeatA2MeanUniformEnvelope
  apply listQSum_mono_local
  intro rowIndex hrowIndex
  have hfaceIndex : rowIndex / 3 < (bulkSourceFaces side).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rw [Nat.mul_comm]
    exact List.mem_range.mp hrowIndex
  have hweight : (0 : Q') ≤ weight rowIndex :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt
        (bulkSourceIndexWeight_pos sidePositive hfaceIndex))
  have hgram :=
    bulkSourceHeatHeronColorCurlRow_gram_abs_le_uniformEnvelope
      timeBonds side stage time time rowIndex rowIndex
  rw [if_pos rfl] at hgram
  have habs := ExpNeg.abs_mul_le
    (weight rowIndex)
    (finiteRowGram (bulkSourceNoiseCount timeBonds side)
      (row rowIndex) (row rowIndex))
  rw [ExpNeg.abs_of_nonneg hweight] at habs
  exact Q'.le_trans' _ _ _ habs
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hgram hweight)

/-- Aggregate coefficient controlling the complete supplied-OLD-centered
`P6` common-action scaling residual. -/
def bulkSourceHeatP6ScalingTotalCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter) : Q' :=
  let leftMeanEnvelope := bulkSourceHeatA2MeanUniformEnvelope
    timeBonds side sidePositive leftTime
  let rightMeanEnvelope := bulkSourceHeatA2MeanUniformEnvelope
    timeBonds side sidePositive rightTime
  let leftMeanCoefficient := bulkSourceHeatMeanScalingTotalCoefficient
    timeBonds side sidePositive leftTime
  let rightMeanCoefficient := bulkSourceHeatMeanScalingTotalCoefficient
    timeBonds side sidePositive rightTime
  let connectedCoefficient := bulkSourceHeatConnectedScalingTotalCoefficient
    timeBonds side sidePositive leftTime rightTime
  (connectedCoefficient +
    (leftMeanEnvelope + Q'.abs oldCenter.c2) * rightMeanCoefficient) +
  leftMeanCoefficient * (rightMeanEnvelope + Q'.abs oldCenter.c2)

theorem bulkSourceHeatP6ScalingTotalCoefficient_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter) :
    (0 : Q') ≤ bulkSourceHeatP6ScalingTotalCoefficient
      timeBonds side sidePositive leftTime rightTime oldCenter := by
  unfold bulkSourceHeatP6ScalingTotalCoefficient
  dsimp only
  exact add_nonnegative_local _ _
    (add_nonnegative_local _ _
      (bulkSourceHeatConnectedScalingTotalCoefficient_nonnegative
        timeBonds side sidePositive leftTime rightTime)
      (Q'.mul_nonneg _ _
        (add_nonnegative_local _ _
          (bulkSourceHeatA2MeanUniformEnvelope_nonnegative
            timeBonds side sidePositive leftTime)
          (Q'.abs_nonneg oldCenter.c2))
        (bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
          timeBonds side sidePositive rightTime)))
    (Q'.mul_nonneg _ _
      (bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
        timeBonds side sidePositive leftTime)
      (add_nonnegative_local _ _
        (bulkSourceHeatA2MeanUniformEnvelope_nonnegative
          timeBonds side sidePositive rightTime)
        (Q'.abs_nonneg oldCenter.c2)))

/-- One constructive stage for the complete supplied-OLD-centered `P6`
common-action scaling residual at a fixed finite cutoff. -/
def bulkSourceHeatP6ScalingAdaptiveStage
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (leftTime rightTime : Nat) (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') : Nat :=
  geoOuterModulus
    (bulkSourceHeatP6ScalingTotalCoefficient
      timeBonds side sidePositive leftTime rightTime oldCenter)
    epsilon

private theorem mean_center_abs_le
    (mean center envelope : Q')
    (hmean : Q'.abs mean ≤ envelope) :
    Q'.abs (mean - center) ≤ envelope + Q'.abs center := by
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le' mean (-center)) ?_
  exact Q'.add_le_add hmean
    (Q'.le_of_eqv (Q'.abs_neg' center))

private theorem geoTail_weighted_three_eqv
    (connected leftFactor rightCoefficient leftCoefficient rightFactor : Q')
    (stage : Nat) :
    (geoTail connected stage +
        leftFactor * geoTail rightCoefficient stage) +
      geoTail leftCoefficient stage * rightFactor ≈
    geoTail
      ((connected + leftFactor * rightCoefficient) +
        leftCoefficient * rightFactor)
      stage := by
  unfold geoTail
  exact poly_identity_of_normal_eq
    (.add
      (.add
        (.mul (.mul (.const 2) (.var 0)) (.var 5))
        (.mul (.var 1)
          (.mul (.mul (.const 2) (.var 2)) (.var 5))))
      (.mul
        (.mul (.mul (.const 2) (.var 3)) (.var 5))
        (.var 4)))
    (.mul
      (.mul (.const 2)
        (.add
          (.add (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 3) (.var 4))))
      (.var 5))
    (by decide) (fun
      | 0 => connected
      | 1 => leftFactor
      | 2 => rightCoefficient
      | 3 => leftCoefficient
      | 4 => rightFactor
      | _ => HalfPow.half ^ stage)

/-- The complete corrected Wick form of the supplied-OLD-centered `P6`
scaling residual obeys one aggregate geometric-tail bound. -/
theorem openCubeHeatCayleyTraceP6ScalingResidualWickSum_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    Q'.abs
        (openCubeHeatCayleyTraceP6ScalingResidualWickSum
          timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      geoTail
        (bulkSourceHeatP6ScalingTotalCoefficient
          timeBonds side sidePositive leftTime rightTime oldCenter)
        stage := by
  let leftMean := openCubeHeatCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage leftTime
  let rightMean := openCubeHeatCayleyTraceOwnA2MeanGramSum
    timeBonds side sidePositive stage rightTime
  let leftDefect := openCubeHeatCayleyTraceMeanScalingDefectWickSum
    timeBonds side sidePositive stage leftTime
  let rightDefect := openCubeHeatCayleyTraceMeanScalingDefectWickSum
    timeBonds side sidePositive stage rightTime
  let connectedDefect := openCubeHeatCayleyTraceConnectedScalingDefectWickSum
    timeBonds side sidePositive stage leftTime rightTime
  let leftMeanEnvelope := bulkSourceHeatA2MeanUniformEnvelope
    timeBonds side sidePositive leftTime
  let rightMeanEnvelope := bulkSourceHeatA2MeanUniformEnvelope
    timeBonds side sidePositive rightTime
  let leftMeanCoefficient := bulkSourceHeatMeanScalingTotalCoefficient
    timeBonds side sidePositive leftTime
  let rightMeanCoefficient := bulkSourceHeatMeanScalingTotalCoefficient
    timeBonds side sidePositive rightTime
  let connectedCoefficient := bulkSourceHeatConnectedScalingTotalCoefficient
    timeBonds side sidePositive leftTime rightTime
  let leftFactor := leftMeanEnvelope + Q'.abs oldCenter.c2
  let rightFactor := rightMeanEnvelope + Q'.abs oldCenter.c2
  have hleftMean :=
    openCubeHeatCayleyTraceOwnA2MeanGramSum_abs_le_uniformEnvelope
      timeBonds side sidePositive stage leftTime
  have hrightMean :=
    openCubeHeatCayleyTraceOwnA2MeanGramSum_abs_le_uniformEnvelope
      timeBonds side sidePositive stage rightTime
  have hleftCentered : Q'.abs (leftMean - oldCenter.c2) ≤ leftFactor :=
    mean_center_abs_le leftMean oldCenter.c2 leftMeanEnvelope hleftMean
  have hrightCentered : Q'.abs (rightMean - oldCenter.c2) ≤ rightFactor :=
    mean_center_abs_le rightMean oldCenter.c2 rightMeanEnvelope hrightMean
  have hleftDefect : Q'.abs leftDefect ≤
      geoTail leftMeanCoefficient stage :=
    openCubeHeatCayleyTraceMeanScalingDefectWickSum_abs_le_geoTail
      timeBonds side sidePositive stage leftTime
  have hrightDefect : Q'.abs rightDefect ≤
      geoTail rightMeanCoefficient stage :=
    openCubeHeatCayleyTraceMeanScalingDefectWickSum_abs_le_geoTail
      timeBonds side sidePositive stage rightTime
  have hconnected : Q'.abs connectedDefect ≤
      geoTail connectedCoefficient stage :=
    openCubeHeatCayleyTraceConnectedScalingDefectWickSum_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime
  have hleftFactor : (0 : Q') ≤ leftFactor :=
    add_nonnegative_local _ _
      (bulkSourceHeatA2MeanUniformEnvelope_nonnegative
        timeBonds side sidePositive leftTime)
      (Q'.abs_nonneg oldCenter.c2)
  have hrightFactor : (0 : Q') ≤ rightFactor :=
    add_nonnegative_local _ _
      (bulkSourceHeatA2MeanUniformEnvelope_nonnegative
        timeBonds side sidePositive rightTime)
      (Q'.abs_nonneg oldCenter.c2)
  have hrightTail : (0 : Q') ≤ geoTail rightMeanCoefficient stage :=
    geoTail_nonneg rightMeanCoefficient
      (bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
        timeBonds side sidePositive rightTime)
      stage
  have hrightProduct :
      Q'.abs ((leftMean - oldCenter.c2) * rightDefect) ≤
        leftFactor * geoTail rightMeanCoefficient stage := by
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le (leftMean - oldCenter.c2) rightDefect) ?_
    exact Q'.mul_le_mul_of_nonneg
      hleftCentered hrightDefect hleftFactor
      (Q'.abs_nonneg rightDefect)
  have hleftProduct :
      Q'.abs (leftDefect * (rightMean - oldCenter.c2)) ≤
        geoTail leftMeanCoefficient stage * rightFactor := by
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le leftDefect (rightMean - oldCenter.c2)) ?_
    exact Q'.mul_le_mul_of_nonneg
      hleftDefect hrightCentered
      (geoTail_nonneg leftMeanCoefficient
        (bulkSourceHeatMeanScalingTotalCoefficient_nonnegative
          timeBonds side sidePositive leftTime)
        stage)
      (Q'.abs_nonneg (rightMean - oldCenter.c2))
  unfold openCubeHeatCayleyTraceP6ScalingResidualWickSum
  dsimp only
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (connectedDefect + (leftMean - oldCenter.c2) * rightDefect)
      (leftDefect * (rightMean - oldCenter.c2))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add
      (Q'.abs_add_le' connectedDefect
        ((leftMean - oldCenter.c2) * rightDefect))
      (Q'.le_refl' (Q'.abs
        (leftDefect * (rightMean - oldCenter.c2))))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add
      (Q'.add_le_add hconnected hrightProduct)
      hleftProduct) ?_
  unfold bulkSourceHeatP6ScalingTotalCoefficient
  dsimp only
  exact Q'.le_of_eqv
    (geoTail_weighted_three_eqv connectedCoefficient leftFactor
      rightMeanCoefficient leftMeanCoefficient rightFactor stage)

/-- The actual corrected supplied-OLD-centered `P6` scaling residual inherits
the same fixed-cutoff geometric-tail bound from its exact Wick identity. -/
theorem openCubeHeatCayleyTraceP6ScalingResidual_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    Q'.abs
        (openCubeHeatCayleyTraceP6ScalingResidual
          timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      geoTail
        (bulkSourceHeatP6ScalingTotalCoefficient
          timeBonds side sidePositive leftTime rightTime oldCenter)
        stage := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceP6ScalingResidual_wick
          timeBonds side sidePositive stage leftTime rightTime oldCenter))) ?_
  exact openCubeHeatCayleyTraceP6ScalingResidualWickSum_abs_le_geoTail
    timeBonds side sidePositive stage leftTime rightTime oldCenter

/-- At every later stage, the actual complete supplied-OLD-centered `P6`
scaling residual is below the supplied positive rational tolerance. -/
theorem openCubeHeatCayleyTraceP6ScalingResidual_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat)
    (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatP6ScalingAdaptiveStage
        timeBonds side sidePositive leftTime rightTime oldCenter epsilon ≤
      stage) :
    Q'.abs
        (openCubeHeatCayleyTraceP6ScalingResidual
          timeBonds side sidePositive stage leftTime rightTime oldCenter) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceP6ScalingResidual_abs_le_geoTail
      timeBonds side sidePositive stage leftTime rightTime oldCenter) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatP6ScalingTotalCoefficient
      timeBonds side sidePositive leftTime rightTime oldCenter)
    (bulkSourceHeatP6ScalingTotalCoefficient_nonnegative
      timeBonds side sidePositive leftTime rightTime oldCenter)
    epsilon hepsilon stage hstage

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage.bulkSourceHeatA2MeanUniformEnvelope_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage.openCubeHeatCayleyTraceOwnA2MeanGramSum_abs_le_uniformEnvelope
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage.bulkSourceHeatP6ScalingTotalCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage.openCubeHeatCayleyTraceP6ScalingResidualWickSum_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage.openCubeHeatCayleyTraceP6ScalingResidual_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ScalingAdaptiveStage.openCubeHeatCayleyTraceP6ScalingResidual_abs_le_epsilon
